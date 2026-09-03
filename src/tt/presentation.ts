import { AST } from "./astparser.js";

const explicitAtPattern = /@(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+)/g;
const explicitAtNodePattern = /^@(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+)$/;

/** Mark @ aliases that came from a user-facing source string. */
export function markExplicitAtSyntax(ast: AST): AST {
    const visited = new WeakSet<object>();
    const visit = (node: AST) => {
        if (!node || typeof node !== "object" || visited.has(node)) return;
        visited.add(node);
        if (node.type === "var" && !node.bondVarId && explicitAtNodePattern.test(node.name ?? "")) {
            node.displayExplicitAt = true;
        }
        for (const child of node.nodes ?? []) visit(child);
    };
    visit(ast);
    return ast;
}

/** Return whether a term still contains an @ alias occurrence from source. */
export function hasExplicitAtOccurrence(ast: AST): boolean {
    const visited = new WeakSet<object>();
    const visit = (node: AST): boolean => {
        if (!node || typeof node !== "object" || visited.has(node)) return false;
        visited.add(node);
        if (node.displayExplicitAt === true) return true;
        for (const child of node.nodes ?? []) {
            if (visit(child)) return true;
        }
        return !!node.checked && visit(node.checked);
    };
    return visit(ast);
}

/** Collect explicit kernel aliases written in user-facing source text. */
export function collectExplicitAtNames(source: string, result = new Set<string>()) {
    for (const match of source.matchAll(explicitAtPattern)) result.add(match[0]);
    return result;
}

/**
 * Make binders generated for a sandbox inductive readable without changing
 * the term used by the checker.  The lowering pass deliberately gives every
 * branch/argument a globally unique name (`c1`, `a1_0`, `ih1_0`, ...), which
 * is useful for construction but noisy in the type list.  This pass performs
 * a lexical alpha-renaming on a display clone only.  References are renamed
 * by binder scope (or bondVarId when available), so dependent occurrences
 * continue to point at the same binder.
 */
export type SandboxDisplayNamingOptions = {
    /** Constructor names in declaration order, used for branch binders. */
    constructorNames?: readonly string[];
};

type DisplayNameEnvironment = {
    byName: Map<string, string>;
    byId: Map<number, string>;
    boundNames: Set<string>;
};

const sandboxBranchBinderPattern = /^c([0-9]+)$/;
const sandboxArgumentBinderPattern = /^a([0-9]+)_([0-9]+)$/;
const sandboxInductionBinderPattern = /^ih([0-9]+)_([0-9]+)$/;
const sandboxArgumentNames = ["x", "y", "z", "w", "v", "t", "r", "s", "q"];
const displayBinderTypes = new Set(["P", "L", "S", "W"]);

function collectFreeDisplayNames(
    ast: AST | undefined,
    bound: ReadonlySet<string> = new Set<string>(),
    result = new Set<string>(),
    visited = new WeakSet<object>()
) {
    if (!ast || typeof ast !== "object" || visited.has(ast)) return result;
    visited.add(ast);
    if (ast.type === "var") {
        if (!bound.has(ast.name)) result.add(ast.name);
        if (ast.checked) collectFreeDisplayNames(ast.checked, bound, result, visited);
        return result;
    }
    if (displayBinderTypes.has(ast.type) && ast.nodes?.length) {
        collectFreeDisplayNames(ast.nodes[0], bound, result, visited);
        const nestedBound = new Set(bound);
        nestedBound.add(ast.name);
        collectFreeDisplayNames(ast.nodes[1], nestedBound, result, visited);
    } else {
        for (const child of ast.nodes ?? []) {
            collectFreeDisplayNames(child, bound, result, visited);
        }
    }
    if (ast.checked) collectFreeDisplayNames(ast.checked, bound, result, visited);
    return result;
}

function sanitizeDisplayConstructorName(name: string | undefined, index: number) {
    const sanitized = String(name ?? "")
        .replace(/[^A-Za-z0-9_']/g, "_")
        .replace(/^([^A-Za-z_])/, "_$1");
    return sanitized || `case${index}`;
}

function sandboxDisplayBinderBase(
    name: string,
    domain: AST | undefined,
    options: SandboxDisplayNamingOptions
) {
    const branch = sandboxBranchBinderPattern.exec(name);
    if (branch) {
        const index = Number(branch[1]);
        const ctor = options.constructorNames?.[index];
        return `c${sanitizeDisplayConstructorName(ctor, index)}`;
    }
    const argument = sandboxArgumentBinderPattern.exec(name);
    if (argument) {
        const index = Number(argument[2]);
        // Natural-number arguments are conventionally written as n; other
        // constructor arguments use the familiar x, y, z sequence.
        if (domain?.type === "var" && /^nat$/i.test(domain.name)) return "n";
        return sandboxArgumentNames[index] ?? `x${index + 1}`;
    }
    const induction = sandboxInductionBinderPattern.exec(name);
    if (induction) {
        const index = Number(induction[2]);
        return index === 0 ? "ih" : `ih${index + 1}`;
    }
    return name;
}

function allocateDisplayBinderName(
    base: string,
    oldName: string,
    body: AST | undefined,
    environment: DisplayNameEnvironment
) {
    const occupied = collectFreeDisplayNames(body, new Set([...environment.boundNames, oldName]));
    for (const value of environment.byName.values()) occupied.add(value);
    if (!occupied.has(base) || base === oldName) return base;
    let suffix = 2;
    while (occupied.has(`${base}${suffix}`)) suffix++;
    return `${base}${suffix}`;
}

/**
 * Alpha-rename sandbox-generated inductive binders on a cloned display AST.
 * The input is never mutated and remains suitable for the type checker.
 */
export function prettySandboxInductiveNamesForDisplay(
    ast: AST,
    options: SandboxDisplayNamingOptions = {}
) {
    const clone = (
        node: AST | undefined,
        environment: DisplayNameEnvironment
    ): AST | undefined => {
        if (!node || typeof node !== "object") return node;
        if (node.type === "var") {
            const replacement = (Number.isFinite(node.bondVarId)
                ? environment.byId.get(node.bondVarId as number)
                : undefined) ?? environment.byName.get(node.name);
            const result: AST = { ...node, name: replacement ?? node.name };
            if (node.checked) result.checked = clone(node.checked, environment);
            return result;
        }
        if (displayBinderTypes.has(node.type) && node.nodes?.length >= 2) {
            const domain = clone(node.nodes[0], environment);
            const base = sandboxDisplayBinderBase(node.name, node.nodes[0], options);
            const name = allocateDisplayBinderName(base, node.name, node.nodes[1], environment);
            const nextByName = new Map(environment.byName);
            nextByName.set(node.name, name);
            const nextById = new Map(environment.byId);
            if (Number.isFinite(node.bondVarId)) nextById.set(node.bondVarId as number, name);
            const nextBoundNames = new Set(environment.boundNames);
            nextBoundNames.add(node.name);
            const body = clone(node.nodes[1], {
                byName: nextByName,
                byId: nextById,
                boundNames: nextBoundNames
            });
            const result: AST = {
                ...node,
                name,
                nodes: [domain as AST, body as AST]
            };
            if (node.checked) result.checked = clone(node.checked, environment);
            return result;
        }
        const result: AST = {
            ...node,
            nodes: node.nodes?.map(child => clone(child, environment) as AST)
        };
        if (node.checked) result.checked = clone(node.checked, environment);
        return result;
    };

    return clone(ast, {
        byName: new Map<string, string>(),
        byId: new Map<number, string>(),
        boundNames: new Set<string>()
    }) as AST;
}

/**
 * Fold elaboration-only implicit prefixes back to their public aliases.
 * Explicit @ occurrences typed by the user remain untouched.
 */
export function compactImplicitAliasesForDisplay(
    ast: AST,
    aliases: readonly (readonly [string, number])[],
    explicitAtNames: ReadonlySet<string>
) {
    const aliasArities = new Map(aliases);
    const metadataVisited = new WeakSet<object>();
    let hasOccurrenceMetadata = false;
    const scanMetadata = (node: AST) => {
        if (!node || typeof node !== "object" || metadataVisited.has(node)) return;
        metadataVisited.add(node);
        if (node.displayExplicitAt) hasOccurrenceMetadata = true;
        for (const child of node.nodes ?? []) scanMetadata(child);
        if (node.checked) scanMetadata(node.checked);
    };
    scanMetadata(ast);
    const visited = new WeakSet<object>();

    const visit = (node: AST) => {
        if (!node || typeof node !== "object" || visited.has(node)) return;
        visited.add(node);
        for (const child of node.nodes ?? []) visit(child);
        if (node.checked) visit(node.checked);
        if (node.type !== "apply") return;

        const application: AST[] = [];
        let head = node;
        while (head.type === "apply") {
            application.unshift(head.nodes[1]);
            head = head.nodes[0];
        }
        application.unshift(head);
        if (head.type !== "var" || head.bondVarId || head.name?.[0] !== "@"
            || (hasOccurrenceMetadata
                ? head.displayExplicitAt === true
                : explicitAtNames.has(head.name))) return;

        const prefixLength = aliasArities.get(head.name.slice(1));
        if (!prefixLength || application.length < prefixLength) return;

        let replacement: AST = { type: "var", name: head.name.slice(1) };
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

    const hiddenVisited = new WeakSet<object>();
    const hideInternalNames = (node: AST) => {
        if (!node || typeof node !== "object" || hiddenVisited.has(node)) return;
        hiddenVisited.add(node);
        for (const child of node.nodes ?? []) hideInternalNames(child);
        if (node.checked) hideInternalNames(node.checked);
        if (node.type !== "var" || node.bondVarId || node.name?.[0] !== "@") return;
        const explicitlyWritten = hasOccurrenceMetadata
            ? node.displayExplicitAt === true
            : explicitAtNames.has(node.name);
        if (!explicitlyWritten) node.name = "_";
    };
    hideInternalNames(ast);
    return ast;
}
