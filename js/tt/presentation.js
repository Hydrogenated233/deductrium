const explicitAtPattern = /@(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+)/g;
const explicitAtNodePattern = /^@(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+)$/;
/** Mark @ aliases that came from a user-facing source string. */
export function markExplicitAtSyntax(ast) {
    const visited = new WeakSet();
    const visit = (node) => {
        if (!node || typeof node !== "object" || visited.has(node))
            return;
        visited.add(node);
        if (node.type === "var" && !node.bondVarId && explicitAtNodePattern.test(node.name ?? "")) {
            node.displayExplicitAt = true;
        }
        for (const child of node.nodes ?? [])
            visit(child);
    };
    visit(ast);
    return ast;
}
/** Return whether a term still contains an @ alias occurrence from source. */
export function hasExplicitAtOccurrence(ast) {
    const visited = new WeakSet();
    const visit = (node) => {
        if (!node || typeof node !== "object" || visited.has(node))
            return false;
        visited.add(node);
        if (node.displayExplicitAt === true)
            return true;
        for (const child of node.nodes ?? []) {
            if (visit(child))
                return true;
        }
        return !!node.checked && visit(node.checked);
    };
    return visit(ast);
}
/** Collect explicit kernel aliases written in user-facing source text. */
export function collectExplicitAtNames(source, result = new Set()) {
    for (const match of source.matchAll(explicitAtPattern))
        result.add(match[0]);
    return result;
}
/**
 * Rename solver-private semantic metavariables before syntax reaches the UI.
 * Preserve sharing and avoid colliding with user-written `?N` names already
 * present in the same tree.
 */
export function restoreSemanticMetaNamesForDisplay(ast) {
    const occupied = new Set();
    const collectVisited = new WeakSet();
    const collect = (node) => {
        if (!node || typeof node !== "object" || collectVisited.has(node))
            return;
        collectVisited.add(node);
        if (node.type === "var") {
            const match = /^\?([0-9]+)$/.exec(node.name ?? "");
            if (match)
                occupied.add(Number(match[1]));
        }
        for (const child of node.nodes ?? [])
            collect(child);
        if (node.checked)
            collect(node.checked);
    };
    collect(ast);
    const renames = new Map();
    let next = 0;
    const visited = new WeakSet();
    const visit = (node) => {
        if (!node || typeof node !== "object" || visited.has(node))
            return;
        visited.add(node);
        if (node.type === "var" && /^\?nbe[0-9]+$/.test(node.name ?? "")) {
            let replacement = renames.get(node.name);
            if (!replacement) {
                while (occupied.has(next))
                    next++;
                replacement = `?${next++}`;
                renames.set(node.name, replacement);
            }
            node.name = replacement;
        }
        for (const child of node.nodes ?? [])
            visit(child);
        if (node.checked)
            visit(node.checked);
    };
    visit(ast);
    return ast;
}
/**
 * Fold elaboration-only implicit prefixes back to their public aliases.
 * Explicit @ occurrences typed by the user remain untouched.
 */
export function compactImplicitAliasesForDisplay(ast, aliases, explicitAtNames) {
    const aliasArities = new Map(aliases);
    const metadataVisited = new WeakSet();
    let hasOccurrenceMetadata = false;
    const scanMetadata = (node) => {
        if (!node || typeof node !== "object" || metadataVisited.has(node))
            return;
        metadataVisited.add(node);
        if (node.displayExplicitAt)
            hasOccurrenceMetadata = true;
        for (const child of node.nodes ?? [])
            scanMetadata(child);
        if (node.checked)
            scanMetadata(node.checked);
    };
    scanMetadata(ast);
    const visited = new WeakSet();
    const visit = (node) => {
        if (!node || typeof node !== "object" || visited.has(node))
            return;
        visited.add(node);
        for (const child of node.nodes ?? [])
            visit(child);
        if (node.checked)
            visit(node.checked);
        if (node.type !== "apply")
            return;
        const application = [];
        let head = node;
        while (head.type === "apply") {
            application.unshift(head.nodes[1]);
            head = head.nodes[0];
        }
        application.unshift(head);
        if (head.type !== "var" || head.bondVarId || head.name?.[0] !== "@"
            || (hasOccurrenceMetadata
                ? head.displayExplicitAt === true
                : explicitAtNames.has(head.name)))
            return;
        const prefixLength = aliasArities.get(head.name.slice(1));
        if (!prefixLength || application.length < prefixLength)
            return;
        let replacement = { type: "var", name: head.name.slice(1) };
        for (const argument of application.slice(prefixLength)) {
            replacement = {
                type: "apply",
                name: "",
                nodes: [replacement, argument]
            };
        }
        const checked = node.checked;
        node.type = replacement.type;
        node.name = replacement.name;
        node.nodes = replacement.nodes;
        node.bondVarId = replacement.bondVarId;
        node.checked = checked;
    };
    visit(ast);
    const hiddenVisited = new WeakSet();
    const hideInternalNames = (node) => {
        if (!node || typeof node !== "object" || hiddenVisited.has(node))
            return;
        hiddenVisited.add(node);
        for (const child of node.nodes ?? [])
            hideInternalNames(child);
        if (node.checked)
            hideInternalNames(node.checked);
        if (node.type !== "var" || node.bondVarId || node.name?.[0] !== "@")
            return;
        const explicitlyWritten = hasOccurrenceMetadata
            ? node.displayExplicitAt === true
            : explicitAtNames.has(node.name);
        if (!explicitlyWritten)
            node.name = "_";
    };
    hideInternalNames(ast);
    return ast;
}
//# sourceMappingURL=presentation.js.map