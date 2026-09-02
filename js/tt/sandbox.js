import { ASTParser } from "./astparser.js";
import { Core } from "./core.js";
import { TTCoreEngine } from "./engine.js";
import { initTypeSystem } from "./initial.js";
import { TheoremWorkspace } from "./theorem-workspace.js";
import { hasLegacySurfaceSyntax, migrateLegacyDeclarationSource, migrateLegacySurfaceExpression } from "./surface-syntax-migration.js";
import { expandTypeTheoryAliasesInSurface } from "./symbol-aliases.js";
const parser = new ASTParser();
export const SANDBOX_SAVE_VERSION = 1;
export const SANDBOX_VALIDATION_CACHE_VERSION = 1;
/**
 * Bump whenever parsing, lowering, Core registration, or NbE cache semantics
 * change. Persisted validation data is an optimization hint, never authority.
 */
export const SANDBOX_VALIDATION_SEMANTIC_EPOCH = "sandbox-nbe-hit3-strong-ap2-v1-2026-09-02";
const SANDBOX_VALIDATION_CACHE_MAX_ENTRIES = 4_096;
const SANDBOX_VALIDATION_CACHE_MAX_OBJECTS = 500_000;
const SANDBOX_VALIDATION_CACHE_MAX_DEPTH = 256;
const SANDBOX_VALIDATION_CACHE_MAX_STRING_UNITS = 8 * 1024 * 1024;
/** The sandbox is an authoring tool and is intentionally unavailable in survival. */
export function sandboxEnabledInMode(mode) {
    return mode === "creative";
}
const sandboxTypeSystemRules = Object.freeze(initTypeSystem());
const defaultSandboxSystemRuleIds = Object.freeze([...new Set(sandboxTypeSystemRules.map(rule => rule.id))]);
/**
 * The complete system prelude used by a creative-mode type layer.  The UI
 * normally passes its current unlocked set explicitly; this export is useful
 * for non-DOM callers that want the same prelude without importing `initial`.
 */
export const creativeSandboxSystemRuleIds = defaultSandboxSystemRuleIds;
const isolatedSandboxSystemRuleIds = Object.freeze([
    "True", "False", "eq", "eq.="
]);
function sandboxStringFingerprint(value) {
    let left = 2166136261 >>> 0;
    let right = 0x9e3779b9 >>> 0;
    for (let index = 0; index < value.length; index++) {
        const unit = value.charCodeAt(index);
        left ^= unit;
        left = Math.imul(left, 16777619) >>> 0;
        right ^= unit + 0x9e3779b9 + ((right << 6) >>> 0) + (right >>> 2);
        right >>>= 0;
    }
    return `${value.length}:${left.toString(16).padStart(8, "0")}:${right.toString(16).padStart(8, "0")}`;
}
function sandboxValidationPrefixKey(previous, signature) {
    return sandboxStringFingerprint(`${previous}\u0000${signature}`);
}
function sandboxValidationPreludeKey(systemRuleIds, semanticResourceScale) {
    const visible = new Set(systemRuleIds);
    const rules = sandboxTypeSystemRules
        .filter(rule => visible.has(rule.id))
        .map(rule => ({
        id: rule.id,
        prefix: rule.prefix,
        inferMode: rule.inferMode,
        postfix: rule.postfix,
        ast: parser.stringify(rule.ast)
    }));
    return sandboxStringFingerprint(JSON.stringify({
        saveVersion: SANDBOX_SAVE_VERSION,
        cacheVersion: SANDBOX_VALIDATION_CACHE_VERSION,
        semanticEpoch: SANDBOX_VALIDATION_SEMANTIC_EPOCH,
        systemRuleIds,
        rules,
        inferDisplayMode: "_",
        semanticResourceScale: semanticResourceScale ?? 1
    }));
}
/** Iterative guard before any recursive clone/compiler sees untrusted cache data. */
function sandboxValidationCacheWithinLimits(value) {
    if (!value || typeof value !== "object")
        return false;
    const seen = new WeakSet();
    const stack = [{ value, depth: 0 }];
    let objects = 0;
    let stringUnits = 0;
    while (stack.length) {
        const current = stack.pop();
        if (current.depth > SANDBOX_VALIDATION_CACHE_MAX_DEPTH)
            return false;
        if (typeof current.value === "string") {
            stringUnits += current.value.length;
            if (stringUnits > SANDBOX_VALIDATION_CACHE_MAX_STRING_UNITS)
                return false;
            continue;
        }
        if (!current.value || typeof current.value !== "object")
            continue;
        if (seen.has(current.value))
            return false;
        seen.add(current.value);
        if (++objects > SANDBOX_VALIDATION_CACHE_MAX_OBJECTS)
            return false;
        if (Array.isArray(current.value)) {
            for (const item of current.value) {
                stack.push({ value: item, depth: current.depth + 1 });
            }
            continue;
        }
        for (const [key, item] of Object.entries(current.value)) {
            if (key === "origin")
                return false;
            stringUnits += key.length;
            if (stringUnits > SANDBOX_VALIDATION_CACHE_MAX_STRING_UNITS)
                return false;
            stack.push({ value: item, depth: current.depth + 1 });
        }
    }
    return true;
}
function sandboxAstHasInferenceHole(ast) {
    if (!ast)
        return false;
    const stack = [ast];
    while (stack.length) {
        const current = stack.pop();
        if (current.type === "var"
            && (current.name === "_" || current.name?.startsWith("?")))
            return true;
        for (const child of current.nodes ?? [])
            stack.push(child);
    }
    return false;
}
const sandboxNamePattern = String.raw `(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+[A-Za-z_][A-Za-z0-9_']*)`;
const sandboxNameRegex = new RegExp(`^${sandboxNamePattern}$`);
/**
 * Clipboard content often contains non-breaking or zero-width whitespace
 * around `:=` (for example when copied from a rendered theorem row).  The
 * core parser intentionally keeps its strict surface grammar, so normalize
 * only sandbox declaration input before handing it to that parser.  This
 * keeps the saved source deterministic without changing identifier semantics
 * elsewhere in the type-theory language.
 */
function normalizeSandboxSource(source) {
    return String(source ?? "")
        .replace(/[\u200B-\u200D\u2060\uFEFF]/g, "")
        .replace(/\p{White_Space}/gu, " ")
        .trim();
}
function findMatchingDelimiter(source, start, open, close) {
    let depth = 0;
    for (let index = start; index < source.length; index++) {
        if (source[index] === open)
            depth++;
        else if (source[index] === close) {
            depth--;
            if (depth === 0)
                return index;
        }
    }
    return -1;
}
function parseInductiveBinder(source, owner, role = "参数") {
    let ast;
    try {
        // Inductive declarations are parsed by the sandbox's internal
        // compatibility layer. User-facing declaration input is validated at
        // parseSandboxDeclaration; constructor fragments still need to accept
        // legacy ASCII syntax from existing fixtures and migrated saves.
        ast = parser.parse(source.trim());
    }
    catch (error) {
        throw new Error(`${owner}${role}格式错误：${source}（${String(error)}）`);
    }
    if (ast.type !== ":" || ast.nodes?.[0]?.type !== "var" || !ast.nodes?.[1]) {
        throw new Error(`${owner}${role}必须使用“名称 : 类型”格式：${source}`);
    }
    const name = ast.nodes[0].name;
    if (!sandboxNameRegex.test(name))
        throw new Error(`${owner}${role}名称不合法：${name}`);
    return {
        name,
        type: ast.nodes[1],
        typeSource: parser.stringify(ast.nodes[1])
    };
}
function splitInductiveSections(source) {
    const sections = [];
    let current = "";
    let depth = 0;
    for (const character of source) {
        if (character === "(" || character === "[")
            depth++;
        else if (character === ")" || character === "]")
            depth = Math.max(0, depth - 1);
        if (character === "|" && depth === 0) {
            sections.push(current.trim());
            current = "";
        }
        else {
            current += character;
        }
    }
    sections.push(current.trim());
    return sections;
}
/**
 * Migrate the type-bearing part of an inductive/HIT header without treating
 * its declared name or telescope variable names as old single-letter syntax.
 */
function migrateSandboxHeaderTail(source) {
    let output = "";
    let cursor = 0;
    while (cursor < source.length) {
        const character = source[cursor];
        if (character === "(" || character === "[") {
            const close = character === "(" ? ")" : "]";
            const end = findMatchingDelimiter(source, cursor, character, close);
            if (end < 0)
                return output + source.slice(cursor);
            // Header telescope binders use `name : type`; preserving the left
            // side prevents e.g. `Pfoo` from becoming `Πfoo` on restore.
            output += character
                + migrateLegacyDeclarationSource(source.slice(cursor + 1, end))
                + close;
            cursor = end + 1;
            continue;
        }
        if (character === ":") {
            return output + ":" + migrateLegacySurfaceExpression(source.slice(cursor + 1));
        }
        output += character;
        cursor++;
    }
    return output;
}
/**
 * Migrate an old sandbox declaration at the save-load boundary.
 *
 * The general declaration migration is correct for ordinary entries.  An
 * inductive/HIT source additionally owns names in its header and each `|`
 * section, so those name portions remain opaque while their right-hand type
 * expressions are migrated.
 */
export function migrateLegacySandboxDeclarationSource(source) {
    if (!source || typeof source !== "string")
        return source;
    const sections = splitInductiveSections(source);
    const header = sections[0] ?? "";
    const match = /^(\s*(?:inductive|hit)\s+)([^\s(\[\]|:]+)([\s\S]*)$/iu.exec(header);
    if (!match)
        return migrateLegacyDeclarationSource(source);
    const migratedHeader = match[1] + match[2] + migrateSandboxHeaderTail(match[3]);
    return [
        migratedHeader,
        ...sections.slice(1).map(section => migrateLegacyDeclarationSource(section))
    ].join(" | ");
}
/**
 * Clone and migrate the syntax fields of one sandbox save.  This is purposely
 * a load-boundary adapter: folder layout, row IDs, enabled state, validation
 * metadata, and any future persisted fields pass through untouched.
 */
export function migrateLegacySandboxSave(value) {
    if (!value || typeof value !== "object" || !Array.isArray(value.declarations)) {
        return value;
    }
    const save = value;
    return {
        ...value,
        declarations: save.declarations.map(declaration => {
            if (!declaration || typeof declaration !== "object")
                return declaration;
            const raw = declaration;
            const migrated = { ...raw };
            if (typeof raw.source === "string") {
                migrated.source = migrateLegacySandboxDeclarationSource(raw.source);
            }
            if (typeof raw.typeSource === "string") {
                migrated.typeSource = migrateLegacySurfaceExpression(raw.typeSource);
            }
            return migrated;
        })
    };
}
function flattenApplication(ast) {
    const terms = [];
    let head = ast;
    while (head?.type === "apply" && head.nodes?.[0] && head.nodes?.[1]) {
        terms.unshift(head.nodes[1]);
        head = head.nodes[0];
    }
    terms.unshift(head);
    return terms;
}
function inductiveResultIndices(ast, name, parameters, indexCount, constructorName) {
    const terms = flattenApplication(ast);
    if (terms[0]?.type !== "var" || terms[0].name !== name)
        return null;
    const expected = parameters.length + indexCount;
    if (terms.length !== expected + 1) {
        throw new Error(`构造子 ${constructorName} 返回 ${name} 时索引数量错误：需要 ${indexCount} 个索引`);
    }
    for (let index = 0; index < parameters.length; index++) {
        const argument = terms[index + 1];
        if (argument?.type !== "var" || argument.name !== parameters[index].name) {
            throw new Error(`构造子 ${constructorName} 的返回参数必须保持统一参数 ${parameters[index].name}`);
        }
    }
    return terms.slice(parameters.length + 1).map(term => Core.clone(term));
}
function recursiveOccurrence(ast, signatureName, parameters, indexCount, constructorName) {
    const directIndices = inductiveResultIndices(ast, signatureName, parameters, indexCount, constructorName);
    if (directIndices)
        return { telescope: [], resultIndices: directIndices };
    if (ast.type === "P" || ast.type === "->") {
        const domain = ast.nodes?.[0];
        const body = ast.nodes?.[1];
        if (!domain || !body)
            throw new Error(`构造子 ${constructorName} 参数类型不完整`);
        if (containsSandboxName(domain, signatureName)) {
            throw new Error(`归纳类型必须严格正：构造子 ${constructorName} 在函数参数位置含有 ${signatureName}`);
        }
        const tail = recursiveOccurrence(body, signatureName, parameters, indexCount, constructorName);
        if (tail) {
            const used = new Set(tail.telescope.map(binder => binder.name));
            let binderName = ast.type === "P" && ast.name ? ast.name : "x";
            for (let suffix = 1; used.has(binderName); suffix++)
                binderName = `x${suffix}`;
            return {
                telescope: [{
                        name: binderName,
                        type: Core.clone(domain),
                        typeSource: parser.stringify(domain)
                    }, ...tail.telescope],
                resultIndices: tail.resultIndices
            };
        }
        return null;
    }
    if (containsSandboxName(ast, signatureName)) {
        throw new Error(`构造子 ${constructorName} 含有尚不支持的嵌套递归出现：${signatureName}`);
    }
    return null;
}
function renameFreeInductiveNames(ast, replacements, bound = new Set()) {
    const clone = Core.clone(ast);
    const visit = (node, scope) => {
        if (node.type === "var") {
            const replacement = !scope.has(node.name) ? replacements.get(node.name) : undefined;
            if (replacement)
                node.name = replacement;
            return;
        }
        if (["P", "L", "S", "W"].includes(node.type) && node.nodes?.[0] && node.nodes?.[1]) {
            visit(node.nodes[0], scope);
            const next = new Set(scope);
            if (node.name)
                next.add(node.name);
            visit(node.nodes[1], next);
            return;
        }
        for (const child of node.nodes ?? [])
            visit(child, scope);
    };
    visit(clone, bound);
    return clone;
}
/** Restore parser-only aliases, including aliases that appeared as binders. */
function restoreSandboxParsedNames(ast, replacements) {
    const clone = Core.clone(ast);
    const visit = (node) => {
        if (node.type === "var") {
            node.name = replacements.get(node.name) ?? node.name;
        }
        else if (["P", "L", "S", "W"].includes(node.type)) {
            node.name = replacements.get(node.name) ?? node.name;
        }
        for (const child of node.nodes ?? [])
            visit(child);
    };
    visit(clone);
    return clone;
}
function replaceSandboxIdentifiers(source, replacements) {
    let result = source;
    const entries = [...replacements.entries()].sort((left, right) => right[0].length - left[0].length);
    for (const [name, replacement] of entries) {
        const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
        result = result.replace(new RegExp(`(?<![A-Za-z0-9_'])${escaped}(?![A-Za-z0-9_'])`, "g"), replacement);
    }
    return result;
}
function sandboxHitParserAliases(source, names) {
    const hidden = new Map();
    const restored = new Map();
    let sequence = 0;
    for (const name of names) {
        if (hidden.has(name))
            continue;
        let alias = `_SandboxHitName${sequence++}`;
        while (source.includes(alias) || restored.has(alias)) {
            alias = `_SandboxHitName${sequence++}`;
        }
        hidden.set(name, alias);
        restored.set(alias, name);
    }
    return { hidden, restored };
}
function collectSandboxAstNames(ast, names = new Set()) {
    if (ast.name)
        names.add(ast.name);
    for (const child of ast.nodes ?? [])
        collectSandboxAstNames(child, names);
    return names;
}
function renameRecursiveOccurrence(occurrence, reserved) {
    const replacements = new Map();
    const renamed = [];
    for (const binder of occurrence.telescope) {
        const type = renameFreeInductiveNames(binder.type, replacements);
        let name = binder.name;
        if (reserved.has(name)) {
            name = "i";
            for (let suffix = 1; reserved.has(name); suffix++)
                name = `i${suffix}`;
        }
        replacements.set(binder.name, name);
        reserved.add(name);
        renamed.push({ name, type, typeSource: parser.stringify(type) });
    }
    return {
        telescope: renamed,
        resultIndices: occurrence.resultIndices.map(index => renameFreeInductiveNames(index, replacements))
    };
}
function decomposeConstructorType(type, signatureName, parameters, indices, constructorName, constructorIndex) {
    const arguments_ = [];
    const usedNames = new Set([
        signatureName,
        ...parameters.map(parameter => parameter.name)
    ]);
    let result = Core.clone(type);
    while ((result.type === "P" || result.type === "->") && result.nodes?.[0] && result.nodes?.[1]) {
        let name = result.type === "P" && result.name
            ? result.name
            : `a${constructorIndex}_${arguments_.length}`;
        if (usedNames.has(name)) {
            if (result.type === "P") {
                throw new Error(`构造子 ${constructorName} 的参数名称重复或遮蔽类型参数：${name}`);
            }
            const base = name;
            for (let suffix = 1; usedNames.has(name); suffix++)
                name = `${base}_${suffix}`;
        }
        usedNames.add(name);
        const argumentType = Core.clone(result.nodes[0]);
        const recursive = recursiveOccurrence(argumentType, signatureName, parameters, indices.length, constructorName);
        arguments_.push({
            name,
            type: argumentType,
            typeSource: parser.stringify(argumentType),
            recursiveTelescope: recursive?.telescope ?? null,
            recursiveResultIndices: recursive?.resultIndices ?? null
        });
        result = Core.clone(result.nodes[1]);
    }
    const resultIndices = inductiveResultIndices(result, signatureName, parameters, indices.length, constructorName);
    if (!resultIndices) {
        if (containsSandboxName(result, signatureName)) {
            throw new Error(`构造子 ${constructorName} 必须直接返回 ${signatureName}`);
        }
        throw new Error(`构造子 ${constructorName} 必须返回 ${signatureName}`);
    }
    const recursiveScope = new Set([...usedNames, signatureName]);
    for (const argument of arguments_) {
        if (argument.recursiveTelescope) {
            const renamed = renameRecursiveOccurrence({
                telescope: argument.recursiveTelescope,
                resultIndices: argument.recursiveResultIndices ?? []
            }, recursiveScope);
            argument.recursiveTelescope = renamed.telescope;
            argument.recursiveResultIndices = renamed.resultIndices;
        }
    }
    return { arguments: arguments_, result, resultIndices };
}
/** Extract declaration-owned telescope names before the compact parser sees them. */
function sandboxHeaderBinderNames(source) {
    const names = [];
    let remainder = source.trim();
    while (remainder.startsWith("(") || remainder.startsWith("[")) {
        const open = remainder[0];
        const close = open === "(" ? ")" : "]";
        const end = findMatchingDelimiter(remainder, 0, open, close);
        if (end < 0)
            break;
        const match = new RegExp(String.raw `^\s*(${sandboxNamePattern})\s*:`).exec(remainder.slice(1, end));
        if (match)
            names.push(match[1]);
        remainder = remainder.slice(end + 1).trim();
    }
    return names;
}
export function parseSandboxInductive(source) {
    const text = normalizeSandboxSource(source);
    const [rawHeader, ...rawConstructors] = splitInductiveSections(text);
    const header = new RegExp(String.raw `^inductive\s+(${sandboxNamePattern})([\s\S]*)$`, "i")
        .exec(rawHeader);
    if (!header) {
        throw new Error("普通归纳类型声明必须使用 inductive 名称 [(参数 : 类型)] : Universe 格式");
    }
    const name = header[1];
    const constructorParts = rawConstructors
        .map(part => part.trim())
        .filter(Boolean)
        .map(raw => {
        const match = new RegExp(String.raw `^(${sandboxNamePattern})\s*(?::\s*([\s\S]*))?$`).exec(raw);
        if (!match)
            throw new Error(`归纳构造子格式错误：${raw}`);
        return { raw, name: match[1], typeSource: match[2]?.trim() };
    });
    const aliases = sandboxHitParserAliases(text, [name, ...sandboxHeaderBinderNames(header[2]), ...constructorParts.map(part => part.name)]);
    const hideReferences = (value) => replaceSandboxIdentifiers(value, aliases.hidden);
    const restoreReferences = (ast) => restoreSandboxParsedNames(ast, aliases.restored);
    let remainder = header[2].trim();
    const parameters = [];
    const indices = [];
    const parameterNames = new Set();
    while (remainder.startsWith("(")) {
        const end = findMatchingDelimiter(remainder, 0, "(", ")");
        if (end < 0)
            throw new Error(`归纳类型 ${name} 的参数括号未闭合`);
        const parameter = parseInductiveBinder(hideReferences(remainder.slice(1, end)), `归纳类型 ${name}`);
        parameter.name = aliases.restored.get(parameter.name) ?? parameter.name;
        parameter.type = restoreReferences(parameter.type);
        parameter.typeSource = parser.stringify(parameter.type);
        if (parameter.name === name || parameterNames.has(parameter.name)) {
            throw new Error(`归纳类型 ${name} 的参数名称冲突：${parameter.name}`);
        }
        parameters.push(parameter);
        parameterNames.add(parameter.name);
        remainder = remainder.slice(end + 1).trim();
    }
    const indexNames = new Set();
    while (remainder.startsWith("[")) {
        const end = findMatchingDelimiter(remainder, 0, "[", "]");
        if (end < 0)
            throw new Error(`归纳类型 ${name} 的索引括号未闭合`);
        const indexBinder = parseInductiveBinder(hideReferences(remainder.slice(1, end)), `归纳类型 ${name}`, "索引");
        indexBinder.name = aliases.restored.get(indexBinder.name) ?? indexBinder.name;
        indexBinder.type = restoreReferences(indexBinder.type);
        indexBinder.typeSource = parser.stringify(indexBinder.type);
        if (indexBinder.name === name
            || parameterNames.has(indexBinder.name)
            || indexNames.has(indexBinder.name)) {
            throw new Error(`归纳类型 ${name} 的索引名称冲突：${indexBinder.name}`);
        }
        indices.push(indexBinder);
        indexNames.add(indexBinder.name);
        remainder = remainder.slice(end + 1).trim();
    }
    if (!remainder.startsWith(":")) {
        throw new Error(`归纳类型 ${name} 缺少 Universe 类型注释`);
    }
    const universeSource = remainder.slice(1).trim();
    if (!universeSource)
        throw new Error(`归纳类型 ${name} 缺少 Universe`);
    let universe;
    try {
        universe = restoreReferences(parser.parse(hideReferences(universeSource)));
    }
    catch (error) {
        throw new Error(`归纳类型 ${name} 的 Universe 格式错误：${String(error)}`);
    }
    for (const parameter of parameters) {
        if (containsSandboxName(parameter.type, name)) {
            throw new Error(`归纳类型参数 ${parameter.name} 的类型不能递归引用 ${name}`);
        }
    }
    for (const indexBinder of indices) {
        if (containsSandboxName(indexBinder.type, name)) {
            throw new Error(`归纳类型索引 ${indexBinder.name} 的类型不能递归引用 ${name}`);
        }
    }
    if (containsSandboxName(universe, name)) {
        throw new Error(`归纳类型 ${name} 的 Universe 不能递归引用自身`);
    }
    const familyApplication = sandboxApply(sandboxVar(name), ...parameters.map(parameter => sandboxVar(parameter.name)), ...indices.map(index => sandboxVar(index.name)));
    const constructors = [];
    for (const [constructorIndex, part] of constructorParts.entries()) {
        const constructorName = part.name;
        const explicitType = part.typeSource;
        if (!explicitType && indices.length) {
            throw new Error(`索引归纳构造子 ${constructorName} 必须显式写出返回索引`);
        }
        const typeSource = explicitType || parser.stringify(familyApplication);
        let type;
        try {
            type = restoreReferences(parser.parse(hideReferences(typeSource)));
        }
        catch (error) {
            throw new Error(`构造子 ${constructorName} 类型格式错误：${String(error)}`);
        }
        const decomposed = decomposeConstructorType(type, name, parameters, indices, constructorName, constructorIndex);
        constructors.push({
            name: constructorName,
            type,
            typeSource,
            arguments: decomposed.arguments.map(argument => argument.typeSource),
            argumentAsts: decomposed.arguments,
            result: decomposed.result,
            resultIndices: decomposed.resultIndices
        });
    }
    if (!constructors.length)
        throw new Error("归纳类型至少需要一个构造子");
    const names = new Set();
    for (const ctor of constructors) {
        if (ctor.name === name || names.has(ctor.name))
            throw new Error(`归纳构造子名称冲突：${ctor.name}`);
        names.add(ctor.name);
    }
    return {
        name,
        parameters,
        indices,
        universe: universeSource,
        universeAst: universe,
        constructors
    };
}
function sandboxPathTelescope(type, owner) {
    const arguments_ = [];
    const used = new Set();
    let body = Core.clone(type);
    while ((body.type === "P" || body.type === "->") && body.nodes?.[0] && body.nodes?.[1]) {
        let name = body.type === "P" && body.name ? body.name : `x${arguments_.length}`;
        if (body.type === "->") {
            const unavailable = collectSandboxAstNames(body.nodes[1], new Set(used));
            const base = name;
            for (let suffix = 1; unavailable.has(name); suffix++)
                name = `${base}_${suffix}`;
        }
        if (used.has(name)) {
            throw new Error(`路径构造子 ${owner} 的参数名称重复：${name}`);
        }
        used.add(name);
        arguments_.push({
            name,
            type: Core.clone(body.nodes[0]),
            typeSource: parser.stringify(body.nodes[0])
        });
        body = Core.clone(body.nodes[1]);
    }
    return { arguments: arguments_, body };
}
function elaborateHitEndpoint(endpoint, signatureName, parameters, pointConstructors, pathName, boundNames) {
    const terms = flattenApplication(endpoint);
    const headName = terms[0]?.type === "var" ? terms[0].name : "";
    if (boundNames.has(headName)) {
        throw new Error(`路径构造子 ${pathName} 的端点 ${headName} 被局部参数遮蔽`);
    }
    const point = pointConstructors.find(constructor => constructor.name === headName);
    if (!point) {
        throw new Error(`路径构造子 ${pathName} 的路径端点必须由 ${signatureName} 的点构造子形成`);
    }
    const supplied = terms.slice(1);
    const pointArgumentCount = point.argumentAsts.length;
    const fullArgumentCount = parameters.length + pointArgumentCount;
    let arguments_;
    if (supplied.length === pointArgumentCount) {
        arguments_ = [
            ...parameters.map(parameter => sandboxVar(parameter.name)),
            ...supplied.map(argument => Core.clone(argument))
        ];
    }
    else if (supplied.length === fullArgumentCount) {
        for (let index = 0; index < parameters.length; index++) {
            const argument = supplied[index];
            if (argument?.type !== "var" || argument.name !== parameters[index].name) {
                throw new Error(`路径构造子 ${pathName} 的端点必须保持统一参数 ${parameters[index].name}`);
            }
        }
        arguments_ = supplied.map(argument => Core.clone(argument));
    }
    else {
        throw new Error(`路径构造子 ${pathName} 的端点 ${headName} 参数数量错误：需要 ${pointArgumentCount} 个点参数`);
    }
    return sandboxConstructorTerm(headName, arguments_);
}
function substituteSandboxFreeVars(ast, replacements, bound = new Set()) {
    if (!ast)
        return ast;
    if (ast.type === "var") {
        const replacement = !bound.has(ast.name) ? replacements.get(ast.name) : undefined;
        return replacement ? Core.clone(replacement) : Core.clone(ast);
    }
    const clone = Core.clone(ast);
    if (["P", "L", "S", "W"].includes(clone.type)
        && clone.nodes?.[0] && clone.nodes?.[1]) {
        clone.nodes[0] = substituteSandboxFreeVars(clone.nodes[0], replacements, bound);
        const next = new Set(bound);
        if (clone.name)
            next.add(clone.name);
        clone.nodes[1] = substituteSandboxFreeVars(clone.nodes[1], replacements, next);
        return clone;
    }
    clone.nodes = clone.nodes?.map(child => substituteSandboxFreeVars(child, replacements, bound));
    return clone;
}
function elaborateHitTwoPathEndpoint(endpoint, signatureName, parameters, pointConstructors, pathConstructors, pathName, boundNames) {
    const terms = flattenApplication(endpoint);
    const headName = terms[0]?.type === "var" ? terms[0].name : "";
    if (boundNames.has(headName)) {
        throw new Error(`二阶路径构造子 ${pathName} 的端点 ${headName} 被局部参数遮蔽`);
    }
    const path = pathConstructors.find(candidate => candidate.name === headName);
    if (!path) {
        throw new Error(`二阶路径构造子 ${pathName} 的端点必须由 ${signatureName} 的一阶路径构造子形成`);
    }
    const supplied = terms.slice(1);
    const fullArgumentCount = parameters.length + path.arguments.length;
    let arguments_;
    if (supplied.length === path.arguments.length) {
        arguments_ = [
            ...parameters.map(parameter => sandboxVar(parameter.name)),
            ...supplied.map(argument => Core.clone(argument))
        ];
    }
    else if (supplied.length === fullArgumentCount) {
        for (let index = 0; index < parameters.length; index++) {
            const argument = supplied[index];
            if (argument?.type !== "var" || argument.name !== parameters[index].name) {
                throw new Error(`二阶路径构造子 ${pathName} 的端点必须保持统一参数 ${parameters[index].name}`);
            }
        }
        arguments_ = supplied.map(argument => Core.clone(argument));
    }
    else {
        throw new Error(`二阶路径构造子 ${pathName} 的端点 ${headName} 参数数量错误：需要 ${path.arguments.length} 个路径参数`);
    }
    const pathTerm = sandboxConstructorTerm(headName, arguments_);
    const argumentReplacements = new Map();
    path.arguments.forEach((argument, index) => {
        argumentReplacements.set(argument.name, arguments_[parameters.length + index]);
    });
    return {
        pathTerm,
        path,
        leftPoint: substituteSandboxFreeVars(path.left, argumentReplacements),
        rightPoint: substituteSandboxFreeVars(path.right, argumentReplacements)
    };
}
function elaborateHitThreePathEndpoint(endpoint, signatureName, parameters, twoPathConstructors, pathName, boundNames) {
    const terms = flattenApplication(endpoint);
    const headName = terms[0]?.type === "var" ? terms[0].name : "";
    if (boundNames.has(headName)) {
        throw new Error(`三阶路径构造子 ${pathName} 的端点 ${headName} 被局部参数遮蔽`);
    }
    const twoPath = twoPathConstructors.find(candidate => candidate.name === headName);
    if (!twoPath) {
        throw new Error(`三阶路径构造子 ${pathName} 的端点必须由 ${signatureName} 的二阶路径构造子形成`);
    }
    const supplied = terms.slice(1);
    const fullArgumentCount = parameters.length + twoPath.arguments.length;
    let arguments_;
    if (supplied.length === twoPath.arguments.length) {
        arguments_ = [
            ...parameters.map(parameter => sandboxVar(parameter.name)),
            ...supplied.map(argument => Core.clone(argument))
        ];
    }
    else if (supplied.length === fullArgumentCount) {
        for (let index = 0; index < parameters.length; index++) {
            const argument = supplied[index];
            if (argument?.type !== "var" || argument.name !== parameters[index].name) {
                throw new Error(`三阶路径构造子 ${pathName} 的端点必须保持统一参数 ${parameters[index].name}`);
            }
        }
        arguments_ = supplied.map(argument => Core.clone(argument));
    }
    else {
        throw new Error(`三阶路径构造子 ${pathName} 的端点 ${headName} 参数数量错误：需要 ${twoPath.arguments.length} 个路径参数`);
    }
    const twoPathTerm = sandboxConstructorTerm(headName, arguments_);
    const argumentReplacements = new Map();
    twoPath.arguments.forEach((argument, index) => {
        argumentReplacements.set(argument.name, arguments_[parameters.length + index]);
    });
    return {
        twoPathTerm,
        twoPath,
        sourcePath: substituteSandboxFreeVars(twoPath.left, argumentReplacements),
        targetPath: substituteSandboxFreeVars(twoPath.right, argumentReplacements),
        sourcePoint: substituteSandboxFreeVars(twoPath.leftPoint, argumentReplacements),
        targetPoint: substituteSandboxFreeVars(twoPath.rightPoint, argumentReplacements)
    };
}
/** Parse a parameterized, non-indexed higher inductive declaration. */
export function parseSandboxHit(source) {
    const text = normalizeSandboxSource(source);
    const [rawHeader, ...rawConstructors] = splitInductiveSections(text);
    const header = new RegExp(String.raw `^hit\s+(${sandboxNamePattern})([\s\S]*)$`, "i")
        .exec(rawHeader);
    if (!header) {
        throw new Error("HIT 声明必须使用 hit 名称 [(参数 : 类型)] : Universe 格式");
    }
    const declaredName = header[1];
    const constructorParts = rawConstructors
        .map(part => part.trim())
        .filter(Boolean)
        .map(raw => {
        const unsupportedPath = /^path(\d+)\s+/i.exec(raw);
        if (unsupportedPath && Number(unsupportedPath[1]) > 3) {
            throw new Error(`当前沙盒最高只解析三维 HIT：不支持 ${unsupportedPath[0].trim()} 高阶路径构造子`);
        }
        const twoPath = /^path2\s+/i.test(raw);
        const threePath = /^path3\s+/i.test(raw);
        const normalized = twoPath || threePath
            ? raw.replace(/^path[23]\s+/i, "")
            : raw;
        const match = new RegExp(String.raw `^(${sandboxNamePattern})\s*(?::\s*([\s\S]*))?$`).exec(normalized);
        if (!match)
            throw new Error(`HIT 构造子格式错误：${raw}`);
        return {
            raw,
            normalized,
            name: match[1],
            typeSource: match[2]?.trim(),
            twoPath,
            threePath
        };
    });
    // ASTParser reserves leading P/S/W/L/X as binder tokens. Parse every
    // declaration-owned identifier through a fresh, source-absent alias so
    // names such as `Point` remain legal in path endpoints. Fresh aliases also
    // prevent the old fixed `_SandboxHitSelf` placeholder from capturing a
    // user declaration with that exact spelling.
    const aliases = sandboxHitParserAliases(text, [declaredName, ...constructorParts.map(part => part.name)]);
    const hideReferences = (value) => replaceSandboxIdentifiers(value, aliases.hidden);
    const restoreReferences = (ast) => restoreSandboxParsedNames(ast, aliases.restored);
    const hiddenDeclaredName = aliases.hidden.get(declaredName);
    const hideDeclaredName = (value) => replaceSandboxIdentifiers(value, new Map([[declaredName, hiddenDeclaredName]]));
    const pointSections = [];
    const pathSections = [];
    const twoPathSections = [];
    const threePathSections = [];
    let sawPath = false;
    let sawTwoPath = false;
    let sawThreePath = false;
    for (const part of constructorParts) {
        const constructorName = part.name;
        const typeSource = part.typeSource;
        if (!typeSource) {
            if (part.threePath)
                throw new Error("三阶路径构造子必须声明类型");
            if (part.twoPath)
                throw new Error("二阶路径构造子必须声明类型");
            if (sawPath || sawTwoPath || sawThreePath) {
                throw new Error("点构造子必须写在路径构造子之前");
            }
            pointSections.push(part.raw);
            continue;
        }
        let type;
        try {
            type = restoreReferences(parser.parse(hideReferences(typeSource)));
        }
        catch (error) {
            throw new Error(`构造子 ${constructorName} 类型格式错误：${String(error)}`);
        }
        const tail = sandboxPathTelescope(type, constructorName).body;
        if (part.threePath) {
            if (!sawTwoPath)
                throw new Error("三阶路径构造子必须写在二阶路径构造子之后");
            if (tail.type !== "=")
                throw new Error(`三阶路径构造子 ${constructorName} 必须以等式为结论`);
            sawThreePath = true;
            threePathSections.push({ raw: part.normalized, name: constructorName, type, typeSource });
        }
        else if (part.twoPath) {
            if (!sawPath)
                throw new Error("二阶路径构造子必须写在一阶路径构造子之后");
            if (sawThreePath)
                throw new Error("二阶路径构造子必须写在三阶路径构造子之前");
            if (tail.type !== "=")
                throw new Error(`二阶路径构造子 ${constructorName} 必须以等式为结论`);
            sawTwoPath = true;
            twoPathSections.push({ raw: part.normalized, name: constructorName, type, typeSource });
        }
        else if (tail.type === "=") {
            if (sawTwoPath || sawThreePath) {
                throw new Error("一阶路径构造子必须写在高阶路径构造子之前");
            }
            sawPath = true;
            pathSections.push({ raw: part.raw, name: constructorName, type, typeSource });
        }
        else {
            if (sawPath || sawTwoPath || sawThreePath) {
                throw new Error("点构造子必须写在路径构造子之前");
            }
            pointSections.push(part.raw);
        }
    }
    if (!pathSections.length)
        throw new Error("HIT 至少需要一个一阶路径构造子");
    const ordinarySource = hideDeclaredName([
        rawHeader.replace(/^hit\b/i, "inductive"),
        ...pointSections
    ].join(" | "));
    const internalOrdinary = parseSandboxInductive(ordinarySource);
    const ordinary = {
        ...internalOrdinary,
        name: declaredName,
        parameters: internalOrdinary.parameters.map(parameter => ({
            ...parameter,
            type: restoreReferences(parameter.type)
        })),
        indices: internalOrdinary.indices.map(index => ({
            ...index,
            type: restoreReferences(index.type)
        })),
        universeAst: restoreReferences(internalOrdinary.universeAst),
        constructors: internalOrdinary.constructors.map(constructor => {
            const type = restoreReferences(constructor.type);
            return {
                ...constructor,
                type,
                typeSource: parser.stringify(type),
                argumentAsts: constructor.argumentAsts.map(argument => {
                    const argumentType = restoreReferences(argument.type);
                    return {
                        ...argument,
                        type: argumentType,
                        typeSource: parser.stringify(argumentType),
                        recursiveTelescope: argument.recursiveTelescope?.map(binder => {
                            const binderType = restoreReferences(binder.type);
                            return {
                                ...binder,
                                type: binderType,
                                typeSource: parser.stringify(binderType)
                            };
                        }) ?? null,
                        recursiveResultIndices: argument.recursiveResultIndices?.map(restoreReferences) ?? null
                    };
                }),
                result: restoreReferences(constructor.result),
                resultIndices: constructor.resultIndices.map(restoreReferences)
            };
        })
    };
    if (ordinary.indices.length)
        throw new Error("一阶 HIT 第一版暂不支持索引");
    for (const constructor of ordinary.constructors) {
        if (constructor.argumentAsts.some(argument => argument.recursiveTelescope !== null)) {
            throw new Error(`一阶 HIT 暂不支持递归点构造子：${constructor.name}`);
        }
    }
    const names = new Set([ordinary.name, ...ordinary.constructors.map(constructor => constructor.name)]);
    const parameterNames = new Set(ordinary.parameters.map(parameter => parameter.name));
    const pathConstructors = [];
    for (const path of pathSections) {
        if (names.has(path.name))
            throw new Error(`HIT 构造子名称冲突：${path.name}`);
        names.add(path.name);
        const { arguments: arguments_, body } = sandboxPathTelescope(path.type, path.name);
        if (body.type !== "=" || !body.nodes?.[0] || !body.nodes?.[1]) {
            throw new Error(`路径构造子 ${path.name} 必须以等式为结论`);
        }
        for (const argument of arguments_) {
            if (parameterNames.has(argument.name)) {
                throw new Error(`路径构造子 ${path.name} 的参数不能遮蔽统一参数：${argument.name}`);
            }
            if (containsSandboxName(argument.type, ordinary.name)) {
                throw new Error(`路径构造子 ${path.name} 的参数不能递归引用 ${ordinary.name}`);
            }
        }
        const endpointBoundNames = new Set([
            ...ordinary.parameters.map(parameter => parameter.name),
            ...arguments_.map(argument => argument.name)
        ]);
        const left = elaborateHitEndpoint(body.nodes[0], ordinary.name, ordinary.parameters, ordinary.constructors, path.name, endpointBoundNames);
        const right = elaborateHitEndpoint(body.nodes[1], ordinary.name, ordinary.parameters, ordinary.constructors, path.name, endpointBoundNames);
        const elaboratedType = sandboxWrapPis(arguments_, {
            type: "=",
            name: "",
            nodes: [Core.clone(left), Core.clone(right)]
        });
        pathConstructors.push({
            name: path.name,
            arguments: arguments_,
            type: elaboratedType,
            typeSource: parser.stringify(elaboratedType),
            left,
            right
        });
    }
    const twoPathConstructors = [];
    for (const path2 of twoPathSections) {
        if (names.has(path2.name))
            throw new Error(`HIT 构造子名称冲突：${path2.name}`);
        names.add(path2.name);
        const { arguments: arguments_, body } = sandboxPathTelescope(path2.type, path2.name);
        if (body.type !== "=" || !body.nodes?.[0] || !body.nodes?.[1]) {
            throw new Error(`二阶路径构造子 ${path2.name} 必须以等式为结论`);
        }
        for (const argument of arguments_) {
            if (parameterNames.has(argument.name)) {
                throw new Error(`二阶路径构造子 ${path2.name} 的参数不能遮蔽统一参数：${argument.name}`);
            }
        }
        const endpointBoundNames = new Set([
            ...ordinary.parameters.map(parameter => parameter.name),
            ...arguments_.map(argument => argument.name)
        ]);
        const left = elaborateHitTwoPathEndpoint(body.nodes[0], ordinary.name, ordinary.parameters, ordinary.constructors, pathConstructors, path2.name, endpointBoundNames);
        const right = elaborateHitTwoPathEndpoint(body.nodes[1], ordinary.name, ordinary.parameters, ordinary.constructors, pathConstructors, path2.name, endpointBoundNames);
        if (!sameSandboxAst(left.leftPoint, right.leftPoint)
            || !sameSandboxAst(left.rightPoint, right.rightPoint)) {
            throw new Error(`二阶路径构造子 ${path2.name} 的一阶路径端点不一致`);
        }
        const elaboratedType = sandboxWrapPis(arguments_, sandboxEquality(Core.clone(left.pathTerm), Core.clone(right.pathTerm)));
        twoPathConstructors.push({
            name: path2.name,
            arguments: arguments_,
            type: elaboratedType,
            typeSource: parser.stringify(elaboratedType),
            left: left.pathTerm,
            right: right.pathTerm,
            leftPoint: left.leftPoint,
            rightPoint: right.rightPoint
        });
    }
    const threePathConstructors = [];
    for (const path3 of threePathSections) {
        if (names.has(path3.name))
            throw new Error(`HIT 构造子名称冲突：${path3.name}`);
        names.add(path3.name);
        const { arguments: arguments_, body } = sandboxPathTelescope(path3.type, path3.name);
        if (body.type !== "=" || !body.nodes?.[0] || !body.nodes?.[1]) {
            throw new Error(`三阶路径构造子 ${path3.name} 必须以等式为结论`);
        }
        for (const argument of arguments_) {
            if (parameterNames.has(argument.name)) {
                throw new Error(`三阶路径构造子 ${path3.name} 的参数不能遮蔽统一参数：${argument.name}`);
            }
        }
        const endpointBoundNames = new Set([
            ...ordinary.parameters.map(parameter => parameter.name),
            ...arguments_.map(argument => argument.name)
        ]);
        const left = elaborateHitThreePathEndpoint(body.nodes[0], ordinary.name, ordinary.parameters, twoPathConstructors, path3.name, endpointBoundNames);
        const right = elaborateHitThreePathEndpoint(body.nodes[1], ordinary.name, ordinary.parameters, twoPathConstructors, path3.name, endpointBoundNames);
        if (!sameSandboxAst(left.sourcePath, right.sourcePath)
            || !sameSandboxAst(left.targetPath, right.targetPath)) {
            throw new Error(`三阶路径构造子 ${path3.name} 的二阶路径边界不一致`);
        }
        if (!sameSandboxAst(left.sourcePoint, right.sourcePoint)
            || !sameSandboxAst(left.targetPoint, right.targetPoint)) {
            throw new Error(`三阶路径构造子 ${path3.name} 的一阶路径边界不一致`);
        }
        const elaboratedType = sandboxWrapPis(arguments_, sandboxEquality(Core.clone(left.twoPathTerm), Core.clone(right.twoPathTerm)));
        threePathConstructors.push({
            name: path3.name,
            arguments: arguments_,
            type: elaboratedType,
            typeSource: parser.stringify(elaboratedType),
            left: left.twoPathTerm,
            right: right.twoPathTerm,
            leftTwoPath: left.twoPath.name,
            rightTwoPath: right.twoPath.name,
            sourcePath: left.sourcePath,
            targetPath: left.targetPath,
            sourcePoint: left.sourcePoint,
            targetPoint: left.targetPoint
        });
    }
    return {
        name: ordinary.name,
        parameters: ordinary.parameters,
        indices: [],
        universe: ordinary.universe,
        universeAst: ordinary.universeAst,
        pointConstructors: ordinary.constructors,
        pathConstructors,
        twoPathConstructors,
        threePathConstructors
    };
}
function sameSandboxAst(left, right) {
    if (!left || !right || left.type !== right.type || left.name !== right.name)
        return false;
    const leftNodes = left.nodes ?? [];
    const rightNodes = right.nodes ?? [];
    return leftNodes.length === rightNodes.length
        && leftNodes.every((node, index) => sameSandboxAst(node, rightNodes[index]));
}
function containsSandboxName(ast, name) {
    if (!ast)
        return false;
    if (ast.type === "var")
        return ast.name === name;
    return (ast.nodes ?? []).some(child => containsSandboxName(child, name));
}
function sandboxVar(name) {
    return { type: "var", name, nodes: [] };
}
function sandboxApply(...terms) {
    let result = terms[0];
    for (let index = 1; index < terms.length; index++) {
        result = { type: "apply", name: "", nodes: [result, terms[index]] };
    }
    return result;
}
function sandboxArrow(domain, codomain) {
    return { type: "->", name: "", nodes: [domain, codomain] };
}
function sandboxPi(name, domain, body) {
    return { type: "P", name, nodes: [domain, body] };
}
function sandboxConstructorTerm(name, arguments_) {
    return sandboxApply(sandboxVar(name), ...arguments_);
}
function sandboxWrapPis(binders, body) {
    let result = body;
    for (let index = binders.length - 1; index >= 0; index--) {
        result = sandboxPi(binders[index].name, Core.clone(binders[index].type), result);
    }
    return result;
}
function sandboxLambda(name, domain, body) {
    return { type: "L", name, nodes: [domain, body] };
}
function sandboxWrapLambdas(binders, body) {
    let result = body;
    for (let index = binders.length - 1; index >= 0; index--) {
        result = sandboxLambda(binders[index].name, Core.clone(binders[index].type), result);
    }
    return result;
}
function sandboxFreshName(base, used) {
    let candidate = base;
    for (let suffix = 1; used.has(candidate); suffix++)
        candidate = `${base}${suffix}`;
    used.add(candidate);
    return candidate;
}
function sandboxInductionHypothesisName(argumentName) {
    const generated = /^a(\d+)_(\d+)$/.exec(argumentName);
    return generated ? `ih${generated[1]}_${generated[2]}` : `${argumentName}_ih`;
}
function sandboxRecursiveValue(argument, telescope) {
    return sandboxApply(Core.clone(argument), ...telescope.map(binder => sandboxVar(binder.name)));
}
function sandboxRecursiveHypothesisType(motiveName, argument, telescope, resultIndices) {
    return sandboxWrapPis(telescope, sandboxApply(sandboxVar(motiveName), ...resultIndices.map(index => Core.clone(index)), sandboxRecursiveValue(argument, telescope)));
}
function sandboxRecursiveCall(recursionHead, argument, telescope, resultIndices) {
    return sandboxWrapLambdas(telescope, sandboxApply(Core.clone(recursionHead), ...resultIndices.map(index => Core.clone(index)), sandboxRecursiveValue(argument, telescope)));
}
/** Lower a validated ordinary signature to Core's trusted system bundle. */
export function lowerSandboxInductive(signature) {
    const typeName = signature.name;
    const parameterVars = signature.parameters.map(parameter => sandboxVar(parameter.name));
    const indexVars = signature.indices.map(index => sandboxVar(index.name));
    const inductiveType = sandboxApply(sandboxVar(typeName), ...parameterVars, ...indexVars);
    const constructorEntries = [];
    const metadataConstructors = [];
    const generatedScope = new Set([
        ...signature.parameters.map(parameter => parameter.name),
        ...signature.constructors.flatMap(constructor => constructor.argumentAsts.map(argument => argument.name))
    ]);
    const motiveName = sandboxFreshName("C", generatedScope);
    const motiveUniverseName = sandboxFreshName("u", generatedScope);
    const resultName = sandboxFreshName("x", generatedScope);
    const branchNames = signature.constructors.map((_, index) => sandboxFreshName(`c${index}`, generatedScope));
    const branchTypes = [];
    const recursorBranchNames = signature.constructors.map((_, index) => sandboxFreshName(`r${index}`, generatedScope));
    const recursorBranchTypes = [];
    for (const ctor of signature.constructors) {
        metadataConstructors.push({
            name: ctor.name,
            argumentTypes: ctor.argumentAsts.map(argument => Core.clone(argument.type)),
            argumentNames: ctor.argumentAsts.map(argument => argument.name),
            recursiveArguments: ctor.argumentAsts.flatMap((argument, index) => argument.recursiveTelescope
                ? [{
                        index,
                        telescope: argument.recursiveTelescope.map(binder => ({
                            name: binder.name,
                            type: Core.clone(binder.type)
                        })),
                        resultIndices: (argument.recursiveResultIndices ?? [])
                            .map(resultIndex => Core.clone(resultIndex))
                    }]
                : []),
            resultIndices: ctor.resultIndices.map(index => Core.clone(index))
        });
        const ctorType = sandboxWrapPis([...signature.parameters, ...ctor.argumentAsts], Core.clone(ctor.result));
        constructorEntries.push([ctor.name, ctorType]);
    }
    const motive = sandboxWrapPis(signature.indices, sandboxArrow(Core.clone(inductiveType), sandboxApply(sandboxVar("U"), sandboxVar(motiveUniverseName))));
    for (let ctorIndex = 0; ctorIndex < signature.constructors.length; ctorIndex++) {
        const ctor = signature.constructors[ctorIndex];
        const argumentVars = ctor.argumentAsts.map(argument => sandboxVar(argument.name));
        let branch = sandboxApply(sandboxVar(motiveName), ...ctor.resultIndices.map(index => Core.clone(index)), sandboxConstructorTerm(ctor.name, [...parameterVars, ...argumentVars]));
        const branchScope = new Set(generatedScope);
        for (let index = ctor.argumentAsts.length - 1; index >= 0; index--) {
            const argument = ctor.argumentAsts[index];
            const recursive = argument.recursiveTelescope;
            if (recursive) {
                branch = sandboxPi(sandboxFreshName(sandboxInductionHypothesisName(argument.name), branchScope), sandboxRecursiveHypothesisType(motiveName, argumentVars[index], recursive, argument.recursiveResultIndices ?? []), branch);
            }
            branch = sandboxPi(argument.name, Core.clone(argument.type), branch);
        }
        branchTypes.push(branch);
        let recursorBranch = sandboxVar(motiveName);
        const recursorBranchScope = new Set(generatedScope);
        for (let index = ctor.argumentAsts.length - 1; index >= 0; index--) {
            const argument = ctor.argumentAsts[index];
            const recursive = argument.recursiveTelescope;
            if (recursive) {
                recursorBranch = sandboxPi(sandboxFreshName(sandboxInductionHypothesisName(argument.name), recursorBranchScope), sandboxWrapPis(recursive, sandboxVar(motiveName)), recursorBranch);
            }
            recursorBranch = sandboxPi(argument.name, Core.clone(argument.type), recursorBranch);
        }
        recursorBranchTypes.push(recursorBranch);
    }
    let fullEliminatorType = sandboxWrapPis(signature.indices, sandboxPi(resultName, Core.clone(inductiveType), sandboxApply(sandboxVar(motiveName), ...indexVars, sandboxVar(resultName))));
    for (let index = branchTypes.length - 1; index >= 0; index--) {
        fullEliminatorType = sandboxPi(branchNames[index], branchTypes[index], fullEliminatorType);
    }
    fullEliminatorType = sandboxPi(motiveName, motive, fullEliminatorType);
    fullEliminatorType = sandboxWrapPis(signature.parameters, fullEliminatorType);
    fullEliminatorType = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullEliminatorType);
    const publicMotive = sandboxWrapPis(signature.indices, sandboxArrow(Core.clone(inductiveType), sandboxApply(sandboxVar("U"), sandboxVar("@0"))));
    let publicEliminatorType = sandboxWrapPis(signature.indices, sandboxPi(resultName, Core.clone(inductiveType), sandboxApply(sandboxVar(motiveName), ...indexVars, sandboxVar(resultName))));
    for (let index = branchTypes.length - 1; index >= 0; index--) {
        publicEliminatorType = sandboxPi(branchNames[index], branchTypes[index], publicEliminatorType);
    }
    // The motive must bind the branch methods and the final result.  Putting
    // `C` outside the branch binders keeps every `C <constructor>` occurrence
    // in scope (the previous order left C free and was rejected by Core).
    publicEliminatorType = sandboxPi(motiveName, publicMotive, publicEliminatorType);
    publicEliminatorType = sandboxWrapPis(signature.parameters, publicEliminatorType);
    let fullRecursorType = sandboxWrapPis(signature.indices, sandboxPi(resultName, Core.clone(inductiveType), sandboxVar(motiveName)));
    for (let index = recursorBranchTypes.length - 1; index >= 0; index--) {
        fullRecursorType = sandboxPi(recursorBranchNames[index], recursorBranchTypes[index], fullRecursorType);
    }
    fullRecursorType = sandboxPi(motiveName, sandboxApply(sandboxVar("U"), sandboxVar(motiveUniverseName)), fullRecursorType);
    fullRecursorType = sandboxWrapPis(signature.parameters, fullRecursorType);
    fullRecursorType = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullRecursorType);
    let publicRecursorType = sandboxWrapPis(signature.indices, sandboxPi(resultName, Core.clone(inductiveType), sandboxVar(motiveName)));
    for (let index = recursorBranchTypes.length - 1; index >= 0; index--) {
        publicRecursorType = sandboxPi(recursorBranchNames[index], recursorBranchTypes[index], publicRecursorType);
    }
    publicRecursorType = sandboxPi(motiveName, sandboxApply(sandboxVar("U"), sandboxVar("@0")), publicRecursorType);
    publicRecursorType = sandboxWrapPis(signature.parameters, publicRecursorType);
    const computeRules = {
        [`ind_${typeName}`]: [],
        [`@ind_${typeName}`]: [],
        [`rec_${typeName}`]: [],
        [`@rec_${typeName}`]: []
    };
    for (let ctorIndex = 0; ctorIndex < signature.constructors.length; ctorIndex++) {
        const ctor = signature.constructors[ctorIndex];
        const parameterPatterns = signature.parameters.map((_, index) => sandboxVar(`?p${index}`));
        const argumentVars = ctor.argumentAsts.map((_, index) => sandboxVar(`?a${ctorIndex}_${index}`));
        const patternReplacements = new Map();
        signature.parameters.forEach((parameter, index) => patternReplacements.set(parameter.name, parameterPatterns[index].name));
        ctor.argumentAsts.forEach((argument, index) => patternReplacements.set(argument.name, argumentVars[index].name));
        const recursivePatternTelescope = (telescope) => telescope.map(binder => ({
            ...binder,
            type: renameFreeInductiveNames(binder.type, patternReplacements)
        }));
        const resultIndexPatterns = ctor.resultIndices.map(index => renameFreeInductiveNames(index, patternReplacements));
        const method = sandboxVar(`?${branchNames[ctorIndex]}`);
        let result = method;
        const methodArgs = [];
        const publicInductionHead = sandboxApply(sandboxVar(`ind_${typeName}`), ...parameterPatterns, sandboxVar(`?${motiveName}`), ...branchNames.map(name => sandboxVar(`?${name}`)));
        const fullInductionHead = sandboxApply(sandboxVar(`@ind_${typeName}`), sandboxVar(`?${motiveUniverseName}`), ...parameterPatterns, sandboxVar(`?${motiveName}`), ...branchNames.map(name => sandboxVar(`?${name}`)));
        for (let index = 0; index < ctor.argumentAsts.length; index++) {
            methodArgs.push(Core.clone(argumentVars[index]));
            const recursive = ctor.argumentAsts[index].recursiveTelescope;
            if (recursive) {
                methodArgs.push(sandboxRecursiveCall(publicInductionHead, argumentVars[index], recursivePatternTelescope(recursive), (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex => renameFreeInductiveNames(resultIndex, patternReplacements))));
            }
        }
        if (methodArgs.length)
            result = sandboxApply(method, ...methodArgs);
        const ctorTerm = sandboxConstructorTerm(ctor.name, [...parameterPatterns, ...argumentVars]);
        const publicPattern = [
            sandboxVar(`ind_${typeName}`),
            ...parameterPatterns,
            sandboxVar(`?${motiveName}`),
            ...branchNames.map(name => sandboxVar(`?${name}`)),
            ...resultIndexPatterns.map(index => Core.clone(index)),
            ctorTerm
        ];
        computeRules[`ind_${typeName}`].push({ pattern: publicPattern, result });
        const fullMethodArgs = [];
        for (let index = 0; index < ctor.argumentAsts.length; index++) {
            fullMethodArgs.push(Core.clone(argumentVars[index]));
            const recursive = ctor.argumentAsts[index].recursiveTelescope;
            if (recursive) {
                fullMethodArgs.push(sandboxRecursiveCall(fullInductionHead, argumentVars[index], recursivePatternTelescope(recursive), (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex => renameFreeInductiveNames(resultIndex, patternReplacements))));
            }
        }
        const fullResult = fullMethodArgs.length
            ? sandboxApply(Core.clone(method), ...fullMethodArgs)
            : Core.clone(method);
        computeRules[`@ind_${typeName}`].push({
            pattern: [
                sandboxVar(`@ind_${typeName}`),
                sandboxVar(`?${motiveUniverseName}`),
                ...publicPattern.slice(1)
            ],
            result: fullResult
        });
        const recursorMethod = sandboxVar(`?${recursorBranchNames[ctorIndex]}`);
        const publicRecursorArgs = [];
        const fullRecursorArgs = [];
        const publicRecursorHead = sandboxApply(sandboxVar(`rec_${typeName}`), ...parameterPatterns, sandboxVar(`?${motiveName}`), ...recursorBranchNames.map(name => sandboxVar(`?${name}`)));
        const fullRecursorHead = sandboxApply(sandboxVar(`@rec_${typeName}`), sandboxVar(`?${motiveUniverseName}`), ...parameterPatterns, sandboxVar(`?${motiveName}`), ...recursorBranchNames.map(name => sandboxVar(`?${name}`)));
        for (let index = 0; index < ctor.argumentAsts.length; index++) {
            publicRecursorArgs.push(Core.clone(argumentVars[index]));
            fullRecursorArgs.push(Core.clone(argumentVars[index]));
            const recursive = ctor.argumentAsts[index].recursiveTelescope;
            if (recursive) {
                publicRecursorArgs.push(sandboxRecursiveCall(publicRecursorHead, argumentVars[index], recursivePatternTelescope(recursive), (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex => renameFreeInductiveNames(resultIndex, patternReplacements))));
                fullRecursorArgs.push(sandboxRecursiveCall(fullRecursorHead, argumentVars[index], recursivePatternTelescope(recursive), (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex => renameFreeInductiveNames(resultIndex, patternReplacements))));
            }
        }
        const publicRecursorResult = publicRecursorArgs.length
            ? sandboxApply(Core.clone(recursorMethod), ...publicRecursorArgs)
            : Core.clone(recursorMethod);
        const fullRecursorResult = fullRecursorArgs.length
            ? sandboxApply(Core.clone(recursorMethod), ...fullRecursorArgs)
            : Core.clone(recursorMethod);
        const recursorTail = [
            ...parameterPatterns,
            sandboxVar(`?${motiveName}`),
            ...recursorBranchNames.map(name => sandboxVar(`?${name}`)),
            ...resultIndexPatterns.map(index => Core.clone(index)),
            Core.clone(ctorTerm)
        ];
        computeRules[`rec_${typeName}`].push({
            pattern: [sandboxVar(`rec_${typeName}`), ...recursorTail],
            result: publicRecursorResult
        });
        computeRules[`@rec_${typeName}`].push({
            pattern: [
                sandboxVar(`@rec_${typeName}`),
                sandboxVar(`?${motiveUniverseName}`),
                ...recursorTail
            ],
            result: fullRecursorResult
        });
    }
    const generatedNames = [
        typeName,
        ...constructorEntries.map(([name]) => name),
        `ind_${typeName}`,
        `@ind_${typeName}`,
        `rec_${typeName}`,
        `@rec_${typeName}`
    ];
    return {
        type: [
            typeName,
            sandboxWrapPis([...signature.parameters, ...signature.indices], Core.clone(signature.universeAst))
        ],
        constructors: constructorEntries,
        auxiliaryTypes: [
            [`@ind_${typeName}`, fullEliminatorType],
            [`@rec_${typeName}`, fullRecursorType]
        ],
        eliminator: [`ind_${typeName}`, publicEliminatorType],
        recursor: [`rec_${typeName}`, publicRecursorType],
        computeRules,
        metadata: {
            version: 2,
            ruleSchemaVersion: 1,
            typeName,
            parameterCount: signature.parameters.length,
            indexCount: signature.indices.length,
            indices: signature.indices.map(index => ({
                name: index.name,
                type: Core.clone(index.type)
            })),
            eliminatorName: `ind_${typeName}`,
            fullEliminatorName: `@ind_${typeName}`,
            recursorName: `rec_${typeName}`,
            fullRecursorName: `@rec_${typeName}`,
            constructors: metadataConstructors
        },
        generatedNames
    };
}
function sandboxInsertPis(type, depth, binders) {
    const root = Core.clone(type);
    let cursor = root;
    for (let index = 0; index < depth; index++) {
        if ((cursor.type !== "P" && cursor.type !== "->") || !cursor.nodes?.[1]) {
            throw new Error("HIT 消去器类型结构与点构造 lowering 不一致");
        }
        cursor = cursor.nodes[1];
    }
    const tail = Core.clone(cursor);
    const replacement = sandboxWrapPis(binders, tail);
    Object.assign(cursor, replacement);
    return root;
}
function sandboxHitBranchValue(endpoint, parameters, pointConstructors, branchNames) {
    const terms = flattenApplication(endpoint);
    const constructorName = terms[0]?.name;
    const constructorIndex = pointConstructors.findIndex(ctor => ctor.name === constructorName);
    if (constructorIndex < 0)
        throw new Error(`未知的 HIT 点构造子端点：${constructorName || ""}`);
    const arguments_ = terms.slice(1 + parameters.length).map(argument => Core.clone(argument));
    return arguments_.length
        ? sandboxApply(sandboxVar(branchNames[constructorIndex]), ...arguments_)
        : sandboxVar(branchNames[constructorIndex]);
}
function sandboxHitPathMethodValue(endpoint, parameters, pathConstructors, methodNames, owner) {
    const terms = flattenApplication(endpoint);
    const pathName = terms[0]?.type === "var" ? terms[0].name : "";
    const pathIndex = pathConstructors.findIndex(path => path.name === pathName);
    if (pathIndex < 0)
        throw new Error(`未知的二维 HIT 一阶路径端点：${pathName || owner}`);
    const arguments_ = terms.slice(1 + parameters.length).map(argument => Core.clone(argument));
    return sandboxApply(sandboxVar(methodNames[pathIndex]), ...arguments_);
}
function sandboxHitTwoPathMethodValue(endpoint, parameters, twoPathConstructors, methodNames, owner) {
    const terms = flattenApplication(endpoint);
    const pathName = terms[0]?.type === "var" ? terms[0].name : "";
    const pathIndex = twoPathConstructors.findIndex(path => path.name === pathName);
    if (pathIndex < 0)
        throw new Error(`未知的三维 HIT 二阶路径端点：${pathName || owner}`);
    const arguments_ = terms.slice(1 + parameters.length).map(argument => Core.clone(argument));
    return sandboxApply(sandboxVar(methodNames[pathIndex]), ...arguments_);
}
/**
 * Resolve one of a 2-path's endpoint paths together with the dependent
 * equality type required by its path method.  Keeping this information in one
 * place is important for the 2-path computation theorem: the first-path
 * computation terms and the user-supplied coherence term need the exact same
 * endpoints, not merely syntactically similar path-method applications.
 */
function sandboxHitPathData(endpoint, parameters, pointConstructors, pathConstructors, motiveName, branchNames, owner) {
    const terms = flattenApplication(endpoint);
    const pathName = terms[0]?.type === "var" ? terms[0].name : "";
    const pathIndex = pathConstructors.findIndex(path => path.name === pathName);
    if (pathIndex < 0) {
        throw new Error(`未知的二维 HIT 一阶路径端点：${pathName || owner}`);
    }
    const path = pathConstructors[pathIndex];
    const arguments_ = terms
        .slice(1 + parameters.length)
        .map(argument => Core.clone(argument));
    const pathTerm = sandboxConstructorTerm(path.name, [
        ...parameters.map(parameter => sandboxVar(parameter.name)),
        ...arguments_
    ]);
    const leftBranch = sandboxHitBranchValue(path.left, parameters, pointConstructors, branchNames);
    const rightBranch = sandboxHitBranchValue(path.right, parameters, pointConstructors, branchNames);
    const type = sandboxEquality(sandboxApply(sandboxVar("trans"), sandboxVar(motiveName), pathTerm, leftBranch), rightBranch);
    return { path, pathIndex, arguments_, pathTerm, type };
}
function sandboxEquality(left, right) {
    return { type: "=", name: "", nodes: [left, right] };
}
function sandboxCompose(left, right) {
    return { type: "*", name: "", nodes: [left, right] };
}
function sandboxRenameHitPathArguments(path, reserved) {
    const chosen = new Set(reserved);
    const occupied = new Set(reserved);
    for (const argument of path.arguments) {
        occupied.add(argument.name);
        collectSandboxAstNames(argument.type, occupied);
    }
    collectSandboxAstNames(path.left, occupied);
    collectSandboxAstNames(path.right, occupied);
    const replacements = new Map();
    const arguments_ = [];
    for (const argument of path.arguments) {
        const type = renameFreeInductiveNames(argument.type, replacements);
        let name = argument.name;
        if (chosen.has(name))
            name = sandboxFreshName(`path_${name}`, occupied);
        else
            occupied.add(name);
        chosen.add(name);
        replacements.set(argument.name, name);
        arguments_.push({ name, type, typeSource: parser.stringify(type) });
    }
    const left = renameFreeInductiveNames(path.left, replacements);
    const right = renameFreeInductiveNames(path.right, replacements);
    const type = sandboxWrapPis(arguments_, sandboxEquality(Core.clone(left), Core.clone(right)));
    return {
        name: path.name,
        arguments: arguments_,
        type,
        typeSource: parser.stringify(type),
        left,
        right
    };
}
function sandboxRenameHitTwoPathArguments(path, reserved) {
    const chosen = new Set(reserved);
    const occupied = new Set(reserved);
    for (const argument of path.arguments) {
        occupied.add(argument.name);
        collectSandboxAstNames(argument.type, occupied);
    }
    collectSandboxAstNames(path.left, occupied);
    collectSandboxAstNames(path.right, occupied);
    const replacements = new Map();
    const arguments_ = [];
    for (const argument of path.arguments) {
        const type = renameFreeInductiveNames(argument.type, replacements);
        let name = argument.name;
        if (chosen.has(name))
            name = sandboxFreshName(`path2_${name}`, occupied);
        else
            occupied.add(name);
        chosen.add(name);
        replacements.set(argument.name, name);
        arguments_.push({ name, type, typeSource: parser.stringify(type) });
    }
    const left = renameFreeInductiveNames(path.left, replacements);
    const right = renameFreeInductiveNames(path.right, replacements);
    const leftPoint = renameFreeInductiveNames(path.leftPoint, replacements);
    const rightPoint = renameFreeInductiveNames(path.rightPoint, replacements);
    const type = sandboxWrapPis(arguments_, sandboxEquality(Core.clone(left), Core.clone(right)));
    return {
        name: path.name,
        arguments: arguments_,
        type,
        typeSource: parser.stringify(type),
        left,
        right,
        leftPoint,
        rightPoint
    };
}
function sandboxRenameHitThreePathArguments(path, reserved) {
    const chosen = new Set(reserved);
    const occupied = new Set(reserved);
    for (const argument of path.arguments) {
        occupied.add(argument.name);
        collectSandboxAstNames(argument.type, occupied);
    }
    for (const ast of [
        path.left,
        path.right,
        path.sourcePath,
        path.targetPath,
        path.sourcePoint,
        path.targetPoint
    ])
        collectSandboxAstNames(ast, occupied);
    const replacements = new Map();
    const arguments_ = [];
    for (const argument of path.arguments) {
        const type = renameFreeInductiveNames(argument.type, replacements);
        let name = argument.name;
        if (chosen.has(name))
            name = sandboxFreshName(`path3_${name}`, occupied);
        else
            occupied.add(name);
        chosen.add(name);
        replacements.set(argument.name, name);
        arguments_.push({ name, type, typeSource: parser.stringify(type) });
    }
    const rename = (ast) => renameFreeInductiveNames(ast, replacements);
    const left = rename(path.left);
    const right = rename(path.right);
    const type = sandboxWrapPis(arguments_, sandboxEquality(Core.clone(left), Core.clone(right)));
    return {
        ...path,
        arguments: arguments_,
        type,
        typeSource: parser.stringify(type),
        left,
        right,
        sourcePath: rename(path.sourcePath),
        targetPath: rename(path.targetPath),
        sourcePoint: rename(path.sourcePoint),
        targetPoint: rename(path.targetPoint)
    };
}
function sandboxRenameHitUniformParameters(signature, reserved) {
    const occupied = new Set(reserved);
    const collectBinder = (binder) => {
        occupied.add(binder.name);
        collectSandboxAstNames(binder.type, occupied);
    };
    for (const parameter of signature.parameters)
        collectBinder(parameter);
    collectSandboxAstNames(signature.universeAst, occupied);
    for (const constructor of signature.pointConstructors) {
        occupied.add(constructor.name);
        collectSandboxAstNames(constructor.type, occupied);
        for (const argument of constructor.argumentAsts)
            collectBinder(argument);
        collectSandboxAstNames(constructor.result, occupied);
        for (const index of constructor.resultIndices)
            collectSandboxAstNames(index, occupied);
    }
    for (const path of signature.pathConstructors) {
        occupied.add(path.name);
        collectSandboxAstNames(path.type, occupied);
        for (const argument of path.arguments)
            collectBinder(argument);
        collectSandboxAstNames(path.left, occupied);
        collectSandboxAstNames(path.right, occupied);
    }
    for (const path of signature.twoPathConstructors) {
        occupied.add(path.name);
        collectSandboxAstNames(path.type, occupied);
        for (const argument of path.arguments)
            collectBinder(argument);
        collectSandboxAstNames(path.left, occupied);
        collectSandboxAstNames(path.right, occupied);
        collectSandboxAstNames(path.leftPoint, occupied);
        collectSandboxAstNames(path.rightPoint, occupied);
    }
    for (const path of signature.threePathConstructors) {
        occupied.add(path.name);
        collectSandboxAstNames(path.type, occupied);
        for (const argument of path.arguments)
            collectBinder(argument);
        collectSandboxAstNames(path.left, occupied);
        collectSandboxAstNames(path.right, occupied);
        collectSandboxAstNames(path.sourcePath, occupied);
        collectSandboxAstNames(path.targetPath, occupied);
        collectSandboxAstNames(path.sourcePoint, occupied);
        collectSandboxAstNames(path.targetPoint, occupied);
    }
    const replacements = new Map();
    const parameters = signature.parameters.map(parameter => {
        const type = renameFreeInductiveNames(parameter.type, replacements);
        const name = reserved.has(parameter.name)
            ? sandboxFreshName(`param_${parameter.name}`, occupied)
            : parameter.name;
        occupied.add(name);
        replacements.set(parameter.name, name);
        return { name, type, typeSource: parser.stringify(type) };
    });
    if ([...replacements].every(([name, replacement]) => name === replacement)) {
        return signature;
    }
    const rename = (ast) => renameFreeInductiveNames(ast, replacements);
    const renameBinder = (binder) => {
        const type = rename(binder.type);
        return { ...binder, type, typeSource: parser.stringify(type) };
    };
    const pointConstructors = signature.pointConstructors.map(constructor => {
        const type = rename(constructor.type);
        const argumentAsts = constructor.argumentAsts.map(argument => ({
            ...renameBinder(argument),
            recursiveTelescope: argument.recursiveTelescope?.map(renameBinder) ?? null,
            recursiveResultIndices: argument.recursiveResultIndices?.map(rename) ?? null
        }));
        return {
            ...constructor,
            type,
            typeSource: parser.stringify(type),
            arguments: argumentAsts.map(argument => argument.typeSource),
            argumentAsts,
            result: rename(constructor.result),
            resultIndices: constructor.resultIndices.map(rename)
        };
    });
    const pathConstructors = signature.pathConstructors.map(path => {
        const type = rename(path.type);
        return {
            ...path,
            arguments: path.arguments.map(renameBinder),
            type,
            typeSource: parser.stringify(type),
            left: rename(path.left),
            right: rename(path.right)
        };
    });
    const twoPathConstructors = signature.twoPathConstructors.map(path => {
        const type = rename(path.type);
        return {
            ...path,
            arguments: path.arguments.map(renameBinder),
            type,
            typeSource: parser.stringify(type),
            left: rename(path.left),
            right: rename(path.right),
            leftPoint: rename(path.leftPoint),
            rightPoint: rename(path.rightPoint)
        };
    });
    const threePathConstructors = signature.threePathConstructors.map(path => {
        const type = rename(path.type);
        return {
            ...path,
            arguments: path.arguments.map(renameBinder),
            type,
            typeSource: parser.stringify(type),
            left: rename(path.left),
            right: rename(path.right),
            sourcePath: rename(path.sourcePath),
            targetPath: rename(path.targetPath),
            sourcePoint: rename(path.sourcePoint),
            targetPoint: rename(path.targetPoint)
        };
    });
    const universeAst = rename(signature.universeAst);
    return {
        ...signature,
        parameters,
        universe: parser.stringify(universeAst),
        universeAst,
        pointConstructors,
        pathConstructors,
        twoPathConstructors,
        threePathConstructors
    };
}
/** Lower a HIT while keeping path computation propositional. */
export function lowerSandboxHit(signature) {
    if (signature.indices.length)
        throw new Error("一阶 HIT 第一版暂不支持索引");
    if (!signature.pathConstructors.length)
        throw new Error("一阶 HIT 至少需要一个一阶路径构造子");
    for (const constructor of signature.pointConstructors) {
        if (constructor.argumentAsts.some(argument => argument.recursiveTelescope !== null)) {
            throw new Error(`一阶 HIT 暂不支持递归点构造子：${constructor.name}`);
        }
    }
    const uniformParameterReserved = new Set([
        signature.name,
        ...signature.pointConstructors.map(constructor => constructor.name),
        ...signature.pathConstructors.flatMap(path => [
            path.name,
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`
        ]),
        ...signature.twoPathConstructors.flatMap(path => [
            path.name,
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`,
            `ap2_${path.name}`,
            `@ap2_${path.name}`
        ]),
        ...signature.threePathConstructors.flatMap(path => [
            path.name,
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`
        ]),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`,
        "U",
        "U@",
        "eq",
        "trans",
        "trans2",
        "trans3",
        "apd",
        "ap",
        "apd2",
        "ap2",
        "apd3",
        "ap3",
        "@hit_ap2",
        "hit_ap2"
    ]);
    signature = sandboxRenameHitUniformParameters(signature, uniformParameterReserved);
    const ordinary = {
        name: signature.name,
        parameters: signature.parameters,
        indices: [],
        universe: signature.universe,
        universeAst: signature.universeAst,
        constructors: signature.pointConstructors
    };
    const base = lowerSandboxInductive(ordinary);
    const fullEliminatorEntry = base.auxiliaryTypes?.find(([name]) => name === `@ind_${signature.name}`);
    const fullRecursorEntry = base.auxiliaryTypes?.find(([name]) => name === `@rec_${signature.name}`);
    if (!fullEliminatorEntry || !fullRecursorEntry || !base.eliminator || !base.recursor) {
        throw new Error("HIT lowering 缺少普通归纳消去器骨架");
    }
    const motiveBinder = extractSandboxPiBinder(base.eliminator[1], signature.parameters.length);
    const fullUniverseBinder = extractSandboxPiBinder(fullEliminatorEntry[1], 0);
    const pointBranchBinders = extractSandboxPiBinders(base.eliminator[1], signature.parameters.length + 1, signature.pointConstructors.length);
    const recursorPointBinders = extractSandboxPiBinders(base.recursor[1], signature.parameters.length + 1, signature.pointConstructors.length);
    const motiveName = motiveBinder.name;
    const motiveUniverseName = fullUniverseBinder.name;
    const branchNames = pointBranchBinders.map(binder => binder.name);
    const recursorBranchNames = recursorPointBinders.map(binder => binder.name);
    const reserved = new Set([
        ...uniformParameterReserved,
        ...signature.parameters.map(parameter => parameter.name),
        motiveName,
        motiveUniverseName,
        ...branchNames,
        ...recursorBranchNames,
        signature.name,
        ...signature.pointConstructors.map(constructor => constructor.name),
        ...signature.pathConstructors.map(path => path.name),
        ...signature.twoPathConstructors.map(path => path.name),
        ...signature.threePathConstructors.map(path => path.name),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`
    ]);
    signature = {
        ...signature,
        pathConstructors: signature.pathConstructors.map(path => sandboxRenameHitPathArguments(path, reserved)),
        twoPathConstructors: signature.twoPathConstructors.map(path => sandboxRenameHitTwoPathArguments(path, reserved)),
        threePathConstructors: signature.threePathConstructors.map(path => sandboxRenameHitThreePathArguments(path, reserved))
    };
    const coherenceScope = new Set([
        ...reserved,
        ...signature.pathConstructors.flatMap(path => path.arguments.map(argument => argument.name)),
        ...signature.twoPathConstructors.flatMap(path => path.arguments.map(argument => argument.name)),
        ...signature.threePathConstructors.flatMap(path => path.arguments.map(argument => argument.name))
    ]);
    const pathMethodNames = signature.pathConstructors.map((_, index) => sandboxFreshName(`p${index}`, coherenceScope));
    const recursorPathMethodNames = signature.pathConstructors.map((_, index) => sandboxFreshName(`q${index}`, coherenceScope));
    const dependentTwoPathMethodNames = signature.twoPathConstructors.map((_, index) => sandboxFreshName(`p2_${index}`, coherenceScope));
    const recursorTwoPathMethodNames = signature.twoPathConstructors.map((_, index) => sandboxFreshName(`q2_${index}`, coherenceScope));
    const dependentThreePathMethodNames = signature.threePathConstructors.map((_, index) => sandboxFreshName(`p3_${index}`, coherenceScope));
    const recursorThreePathMethodNames = signature.threePathConstructors.map((_, index) => sandboxFreshName(`q3_${index}`, coherenceScope));
    const parameterVars = signature.parameters.map(parameter => sandboxVar(parameter.name));
    const dependentPathBinders = [];
    const recursorPathBinders = [];
    for (let index = 0; index < signature.pathConstructors.length; index++) {
        const path = signature.pathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const pathTerm = sandboxConstructorTerm(path.name, [...parameterVars, ...pathArguments]);
        const leftBranch = sandboxHitBranchValue(path.left, signature.parameters, signature.pointConstructors, branchNames);
        const rightBranch = sandboxHitBranchValue(path.right, signature.parameters, signature.pointConstructors, branchNames);
        const dependentType = sandboxWrapPis(path.arguments, sandboxEquality(sandboxApply(sandboxVar("trans"), sandboxVar(motiveName), pathTerm, leftBranch), rightBranch));
        dependentPathBinders.push({
            name: pathMethodNames[index],
            type: dependentType,
            typeSource: parser.stringify(dependentType)
        });
        const leftRecursorBranch = sandboxHitBranchValue(path.left, signature.parameters, signature.pointConstructors, recursorBranchNames);
        const rightRecursorBranch = sandboxHitBranchValue(path.right, signature.parameters, signature.pointConstructors, recursorBranchNames);
        const recursorType = sandboxWrapPis(path.arguments, sandboxEquality(leftRecursorBranch, rightRecursorBranch));
        recursorPathBinders.push({
            name: recursorPathMethodNames[index],
            type: recursorType,
            typeSource: parser.stringify(recursorType)
        });
    }
    const dependentTwoPathBinders = [];
    const recursorTwoPathBinders = [];
    for (let index = 0; index < signature.twoPathConstructors.length; index++) {
        const path = signature.twoPathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const leftMethod = sandboxHitPathMethodValue(path.left, signature.parameters, signature.pathConstructors, pathMethodNames, path.name);
        const rightMethod = sandboxHitPathMethodValue(path.right, signature.parameters, signature.pathConstructors, pathMethodNames, path.name);
        const endpointValue = sandboxHitBranchValue(path.leftPoint, signature.parameters, signature.pointConstructors, branchNames);
        const transportedRightMethod = {
            type: "*",
            name: "",
            nodes: [
                sandboxApply(sandboxVar("trans2"), sandboxVar(motiveName), sandboxConstructorTerm(path.name, [
                    ...parameterVars,
                    ...pathArguments
                ]), endpointValue),
                rightMethod
            ]
        };
        const dependentType = sandboxWrapPis(path.arguments, sandboxEquality(leftMethod, transportedRightMethod));
        dependentTwoPathBinders.push({
            name: dependentTwoPathMethodNames[index],
            type: dependentType,
            typeSource: parser.stringify(dependentType)
        });
        const leftRecursorMethod = sandboxHitPathMethodValue(path.left, signature.parameters, signature.pathConstructors, recursorPathMethodNames, path.name);
        const rightRecursorMethod = sandboxHitPathMethodValue(path.right, signature.parameters, signature.pathConstructors, recursorPathMethodNames, path.name);
        const recursorType = sandboxWrapPis(path.arguments, sandboxEquality(leftRecursorMethod, rightRecursorMethod));
        recursorTwoPathBinders.push({
            name: recursorTwoPathMethodNames[index],
            type: recursorType,
            typeSource: parser.stringify(recursorType)
        });
    }
    const dependentThreePathBinders = [];
    const recursorThreePathBinders = [];
    for (let index = 0; index < signature.threePathConstructors.length; index++) {
        const path = signature.threePathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const pathTerm = sandboxConstructorTerm(path.name, [...parameterVars, ...pathArguments]);
        const leftMethod = sandboxHitTwoPathMethodValue(path.left, signature.parameters, signature.twoPathConstructors, dependentTwoPathMethodNames, path.name);
        const rightMethod = sandboxHitTwoPathMethodValue(path.right, signature.parameters, signature.twoPathConstructors, dependentTwoPathMethodNames, path.name);
        const sourceMethod = sandboxHitPathMethodValue(path.sourcePath, signature.parameters, signature.pathConstructors, pathMethodNames, path.name);
        const targetMethod = sandboxHitPathMethodValue(path.targetPath, signature.parameters, signature.pathConstructors, pathMethodNames, path.name);
        const endpointValue = sandboxHitBranchValue(path.sourcePoint, signature.parameters, signature.pointConstructors, branchNames);
        const lambdaScope = new Set([
            ...coherenceScope,
            ...path.arguments.map(argument => argument.name)
        ]);
        for (const ast of [path.sourcePath, path.targetPath, sourceMethod, targetMethod]) {
            collectSandboxAstNames(ast, lambdaScope);
        }
        const pathValueName = sandboxFreshName("twoPathValue", lambdaScope);
        const pathValue = sandboxVar(pathValueName);
        const coherenceFamily = sandboxLambda(pathValueName, sandboxEquality(Core.clone(path.sourcePath), Core.clone(path.targetPath)), sandboxEquality(sourceMethod, sandboxCompose(sandboxApply(sandboxVar("trans2"), sandboxVar(motiveName), pathValue, endpointValue), targetMethod)));
        const dependentType = sandboxWrapPis(path.arguments, sandboxEquality(sandboxApply(sandboxVar("trans"), coherenceFamily, pathTerm, leftMethod), rightMethod));
        dependentThreePathBinders.push({
            name: dependentThreePathMethodNames[index],
            type: dependentType,
            typeSource: parser.stringify(dependentType)
        });
        const leftRecursorMethod = sandboxHitTwoPathMethodValue(path.left, signature.parameters, signature.twoPathConstructors, recursorTwoPathMethodNames, path.name);
        const rightRecursorMethod = sandboxHitTwoPathMethodValue(path.right, signature.parameters, signature.twoPathConstructors, recursorTwoPathMethodNames, path.name);
        const recursorType = sandboxWrapPis(path.arguments, sandboxEquality(leftRecursorMethod, rightRecursorMethod));
        recursorThreePathBinders.push({
            name: recursorThreePathMethodNames[index],
            type: recursorType,
            typeSource: parser.stringify(recursorType)
        });
    }
    const allDependentPathBinders = [
        ...dependentPathBinders,
        ...dependentTwoPathBinders,
        ...dependentThreePathBinders
    ];
    const allRecursorPathBinders = [
        ...recursorPathBinders,
        ...recursorTwoPathBinders,
        ...recursorThreePathBinders
    ];
    const publicEliminatorType = sandboxInsertPis(base.eliminator[1], signature.parameters.length + 1 + signature.pointConstructors.length, allDependentPathBinders);
    const fullEliminatorType = sandboxInsertPis(fullEliminatorEntry[1], 1 + signature.parameters.length + 1 + signature.pointConstructors.length, allDependentPathBinders);
    const publicRecursorType = sandboxInsertPis(base.recursor[1], signature.parameters.length + 1 + signature.pointConstructors.length, allRecursorPathBinders);
    const fullRecursorType = sandboxInsertPis(fullRecursorEntry[1], 1 + signature.parameters.length + 1 + signature.pointConstructors.length, allRecursorPathBinders);
    // Keep computation-rule metavariables disjoint from ordinary lowering's
    // `?pN` parameter patterns and generated branch names.
    const pathPatternVariables = pathMethodNames.map((_, index) => sandboxVar(`?hitPath${index}`));
    const recursorPathPatternVariables = recursorPathMethodNames.map((_, index) => sandboxVar(`?hitRecPath${index}`));
    const twoPathPatternVariables = dependentTwoPathMethodNames.map((_, index) => sandboxVar(`?hitTwoPath${index}`));
    const recursorTwoPathPatternVariables = recursorTwoPathMethodNames.map((_, index) => sandboxVar(`?hitRecTwoPath${index}`));
    const threePathPatternVariables = dependentThreePathMethodNames.map((_, index) => sandboxVar(`?hitThreePath${index}`));
    const recursorThreePathPatternVariables = recursorThreePathMethodNames.map((_, index) => sandboxVar(`?hitRecThreePath${index}`));
    const computeRules = Object.fromEntries(Object.entries(base.computeRules ?? {}).map(([head, rules]) => [
        head,
        rules.map(rule => {
            const pattern = rule.pattern.map(term => Core.clone(term));
            const full = head.startsWith("@");
            const insertion = 1 + (full ? 1 : 0) + signature.parameters.length + 1
                + signature.pointConstructors.length;
            pattern.splice(insertion, 0, ...(head.includes("rec_")
                ? [
                    ...recursorPathPatternVariables,
                    ...recursorTwoPathPatternVariables,
                    ...recursorThreePathPatternVariables
                ]
                : [
                    ...pathPatternVariables,
                    ...twoPathPatternVariables,
                    ...threePathPatternVariables
                ])
                .map(term => Core.clone(term)));
            return { pattern, result: Core.clone(rule.result) };
        })
    ]));
    const pathTypes = signature.pathConstructors.map(path => [
        path.name,
        sandboxWrapPis(signature.parameters, Core.clone(path.type))
    ]);
    pathTypes.push(...signature.twoPathConstructors.map(path => [
        path.name,
        sandboxWrapPis(signature.parameters, Core.clone(path.type))
    ]));
    pathTypes.push(...signature.threePathConstructors.map(path => [
        path.name,
        sandboxWrapPis(signature.parameters, Core.clone(path.type))
    ]));
    const computationTypes = [];
    for (let index = 0; index < signature.pathConstructors.length; index++) {
        const path = signature.pathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const pathTerm = sandboxConstructorTerm(path.name, [...parameterVars, ...pathArguments]);
        const dependentHead = sandboxApply(sandboxVar(`ind_${signature.name}`), ...parameterVars, sandboxVar(motiveName), ...branchNames.map(name => sandboxVar(name)), ...pathMethodNames.map(name => sandboxVar(name)), ...dependentTwoPathMethodNames.map(name => sandboxVar(name)), ...dependentThreePathMethodNames.map(name => sandboxVar(name)));
        const fullDependentHead = sandboxApply(sandboxVar(`@ind_${signature.name}`), sandboxVar(motiveUniverseName), ...parameterVars, sandboxVar(motiveName), ...branchNames.map(name => sandboxVar(name)), ...pathMethodNames.map(name => sandboxVar(name)), ...dependentTwoPathMethodNames.map(name => sandboxVar(name)), ...dependentThreePathMethodNames.map(name => sandboxVar(name)));
        const recursorHead = sandboxApply(sandboxVar(`rec_${signature.name}`), ...parameterVars, sandboxVar(motiveName), ...recursorBranchNames.map(name => sandboxVar(name)), ...recursorPathMethodNames.map(name => sandboxVar(name)), ...recursorTwoPathMethodNames.map(name => sandboxVar(name)), ...recursorThreePathMethodNames.map(name => sandboxVar(name)));
        const fullRecursorHead = sandboxApply(sandboxVar(`@rec_${signature.name}`), sandboxVar(motiveUniverseName), ...parameterVars, sandboxVar(motiveName), ...recursorBranchNames.map(name => sandboxVar(name)), ...recursorPathMethodNames.map(name => sandboxVar(name)), ...recursorTwoPathMethodNames.map(name => sandboxVar(name)), ...recursorThreePathMethodNames.map(name => sandboxVar(name)));
        const pathMethodValue = sandboxApply(sandboxVar(pathMethodNames[index]), ...pathArguments);
        const recursorPathMethodValue = sandboxApply(sandboxVar(recursorPathMethodNames[index]), ...pathArguments);
        const publicApdBody = sandboxWrapPis(path.arguments, sandboxEquality(sandboxApply(sandboxVar("apd"), dependentHead, pathTerm), pathMethodValue));
        let publicApdType = sandboxWrapPis(allDependentPathBinders, publicApdBody);
        const pointBranchBinders = extractSandboxPiBinders(base.eliminator[1], signature.parameters.length + 1, signature.pointConstructors.length);
        publicApdType = sandboxWrapPis(pointBranchBinders, publicApdType);
        publicApdType = sandboxPi(motiveName, extractSandboxPiBinder(base.eliminator[1], signature.parameters.length).type, publicApdType);
        publicApdType = sandboxWrapPis(signature.parameters, publicApdType);
        let fullApdType = sandboxWrapPis(path.arguments, sandboxEquality(sandboxApply(sandboxVar("apd"), fullDependentHead, pathTerm), Core.clone(pathMethodValue)));
        fullApdType = sandboxWrapPis(allDependentPathBinders, fullApdType);
        const fullPointBranchBinders = extractSandboxPiBinders(fullEliminatorEntry[1], 1 + signature.parameters.length + 1, signature.pointConstructors.length);
        fullApdType = sandboxWrapPis(fullPointBranchBinders, fullApdType);
        fullApdType = sandboxPi(motiveName, extractSandboxPiBinder(fullEliminatorEntry[1], 1 + signature.parameters.length).type, fullApdType);
        fullApdType = sandboxWrapPis(signature.parameters, fullApdType);
        fullApdType = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullApdType);
        let publicApType = sandboxWrapPis(path.arguments, sandboxEquality(sandboxApply(sandboxVar("ap"), recursorHead, pathTerm), recursorPathMethodValue));
        publicApType = sandboxWrapPis(allRecursorPathBinders, publicApType);
        const recursorPointBinders = extractSandboxPiBinders(base.recursor[1], signature.parameters.length + 1, signature.pointConstructors.length);
        publicApType = sandboxWrapPis(recursorPointBinders, publicApType);
        publicApType = sandboxPi(motiveName, extractSandboxPiBinder(base.recursor[1], signature.parameters.length).type, publicApType);
        publicApType = sandboxWrapPis(signature.parameters, publicApType);
        let fullApType = sandboxWrapPis(path.arguments, sandboxEquality(sandboxApply(sandboxVar("ap"), fullRecursorHead, pathTerm), Core.clone(recursorPathMethodValue)));
        fullApType = sandboxWrapPis(allRecursorPathBinders, fullApType);
        const fullRecursorPointBinders = extractSandboxPiBinders(fullRecursorEntry[1], 1 + signature.parameters.length + 1, signature.pointConstructors.length);
        fullApType = sandboxWrapPis(fullRecursorPointBinders, fullApType);
        fullApType = sandboxPi(motiveName, extractSandboxPiBinder(fullRecursorEntry[1], 1 + signature.parameters.length).type, fullApType);
        fullApType = sandboxWrapPis(signature.parameters, fullApType);
        fullApType = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullApType);
        computationTypes.push([`apd_${path.name}`, publicApdType], [`@apd_${path.name}`, fullApdType], [`ap_${path.name}`, publicApType], [`@ap_${path.name}`, fullApType]);
    }
    // Two-dimensional path computation is propositional.  The first-path
    // computation rules are themselves propositional, so the raw p2 method
    // cannot be used directly as the RHS of apd2: its endpoints are p0 and
    // trans2 ... p1, while apd2 has the corresponding apd endpoints.  Insert
    // those first-path computation paths explicitly and keep the result out
    // of the definitional compute-rule table.
    for (let index = 0; index < signature.twoPathConstructors.length; index++) {
        const path = signature.twoPathConstructors[index];
        const pathArguments = path.arguments.map(argument => sandboxVar(argument.name));
        const pathTerm = sandboxConstructorTerm(path.name, [...parameterVars, ...pathArguments]);
        const dependentHead = sandboxApply(sandboxVar(`ind_${signature.name}`), ...parameterVars, sandboxVar(motiveName), ...branchNames.map(name => sandboxVar(name)), ...pathMethodNames.map(name => sandboxVar(name)), ...dependentTwoPathMethodNames.map(name => sandboxVar(name)), ...dependentThreePathMethodNames.map(name => sandboxVar(name)));
        const fullDependentHead = sandboxApply(sandboxVar(`@ind_${signature.name}`), sandboxVar(motiveUniverseName), ...parameterVars, sandboxVar(motiveName), ...branchNames.map(name => sandboxVar(name)), ...pathMethodNames.map(name => sandboxVar(name)), ...dependentTwoPathMethodNames.map(name => sandboxVar(name)), ...dependentThreePathMethodNames.map(name => sandboxVar(name)));
        const recursorHead = sandboxApply(sandboxVar(`rec_${signature.name}`), ...parameterVars, sandboxVar(motiveName), ...recursorBranchNames.map(name => sandboxVar(name)), ...recursorPathMethodNames.map(name => sandboxVar(name)), ...recursorTwoPathMethodNames.map(name => sandboxVar(name)), ...recursorThreePathMethodNames.map(name => sandboxVar(name)));
        const fullRecursorHead = sandboxApply(sandboxVar(`@rec_${signature.name}`), sandboxVar(motiveUniverseName), ...parameterVars, sandboxVar(motiveName), ...recursorBranchNames.map(name => sandboxVar(name)), ...recursorPathMethodNames.map(name => sandboxVar(name)), ...recursorTwoPathMethodNames.map(name => sandboxVar(name)), ...recursorThreePathMethodNames.map(name => sandboxVar(name)));
        const dependentMethodValue = sandboxApply(sandboxVar(dependentTwoPathMethodNames[index]), ...pathArguments);
        const recursorMethodValue = sandboxApply(sandboxVar(recursorTwoPathMethodNames[index]), ...pathArguments);
        const leftPathData = sandboxHitPathData(path.left, signature.parameters, signature.pointConstructors, signature.pathConstructors, motiveName, branchNames, path.name);
        const rightPathData = sandboxHitPathData(path.right, signature.parameters, signature.pointConstructors, signature.pathConstructors, motiveName, branchNames, path.name);
        const endpointValue = sandboxHitBranchValue(path.leftPoint, signature.parameters, signature.pointConstructors, branchNames);
        const transport2Value = sandboxApply(sandboxVar("trans2"), sandboxVar(motiveName), pathTerm, endpointValue);
        // Generated path computation theorems retain the HIT's uniform
        // parameters before the motive. Omitting them only works for
        // unparameterized HITs; for `hit SurfaceP (A : U)`, the old
        // expression treated `C` as `A` and made the final `apd2` slot fail
        // type checking.
        const makeDependentPathComputation = (data, full) => sandboxApply(sandboxVar(`${full ? "@" : ""}apd_${data.path.name}`), ...(full ? [sandboxVar(motiveUniverseName)] : []), ...parameterVars, sandboxVar(motiveName), ...branchNames.map(name => sandboxVar(name)), ...pathMethodNames.map(name => sandboxVar(name)), ...dependentTwoPathMethodNames.map(name => sandboxVar(name)), ...dependentThreePathMethodNames.map(name => sandboxVar(name)), ...data.arguments_);
        const makeRecursorPathComputation = (data, full) => sandboxApply(sandboxVar(`${full ? "@" : ""}ap_${data.path.name}`), ...(full ? [sandboxVar(motiveUniverseName)] : []), ...parameterVars, sandboxVar(motiveName), ...recursorBranchNames.map(name => sandboxVar(name)), ...recursorPathMethodNames.map(name => sandboxVar(name)), ...recursorTwoPathMethodNames.map(name => sandboxVar(name)), ...recursorThreePathMethodNames.map(name => sandboxVar(name)), ...data.arguments_);
        const leftDependentComputation = makeDependentPathComputation(leftPathData, false);
        const rightDependentComputation = makeDependentPathComputation(rightPathData, false);
        const leftDependentComputationFull = makeDependentPathComputation(leftPathData, true);
        const rightDependentComputationFull = makeDependentPathComputation(rightPathData, true);
        const leftRecursorComputation = makeRecursorPathComputation(leftPathData, false);
        const rightRecursorComputation = makeRecursorPathComputation(rightPathData, false);
        const leftRecursorComputationFull = makeRecursorPathComputation(leftPathData, true);
        const rightRecursorComputationFull = makeRecursorPathComputation(rightPathData, true);
        const lambdaScope = new Set([
            ...coherenceScope,
            ...path.arguments.map(argument => argument.name)
        ]);
        collectSandboxAstNames(transport2Value, lambdaScope);
        collectSandboxAstNames(rightPathData.type, lambdaScope);
        const pathValueName = sandboxFreshName("pathValue", lambdaScope);
        const correctedDependentMethod = sandboxCompose(sandboxCompose(leftDependentComputation, dependentMethodValue), sandboxApply(sandboxVar("inveq"), sandboxApply(sandboxVar("ap"), sandboxLambda(pathValueName, rightPathData.type, sandboxCompose(Core.clone(transport2Value), sandboxVar(pathValueName))), rightDependentComputation)));
        const correctedDependentMethodFull = sandboxCompose(sandboxCompose(leftDependentComputationFull, Core.clone(dependentMethodValue)), sandboxApply(sandboxVar("inveq"), sandboxApply(sandboxVar("ap"), sandboxLambda(pathValueName, rightPathData.type, sandboxCompose(Core.clone(transport2Value), sandboxVar(pathValueName))), rightDependentComputationFull)));
        let publicApd2Type = sandboxWrapPis(path.arguments, sandboxEquality(sandboxApply(sandboxVar("apd2"), dependentHead, pathTerm), correctedDependentMethod));
        publicApd2Type = sandboxWrapPis(allDependentPathBinders, publicApd2Type);
        publicApd2Type = sandboxWrapPis(extractSandboxPiBinders(base.eliminator[1], signature.parameters.length + 1, signature.pointConstructors.length), publicApd2Type);
        publicApd2Type = sandboxPi(motiveName, extractSandboxPiBinder(base.eliminator[1], signature.parameters.length).type, publicApd2Type);
        publicApd2Type = sandboxWrapPis(signature.parameters, publicApd2Type);
        let fullApd2Type = sandboxWrapPis(path.arguments, sandboxEquality(sandboxApply(sandboxVar("apd2"), fullDependentHead, pathTerm), correctedDependentMethodFull));
        fullApd2Type = sandboxWrapPis(allDependentPathBinders, fullApd2Type);
        fullApd2Type = sandboxWrapPis(extractSandboxPiBinders(fullEliminatorEntry[1], 1 + signature.parameters.length + 1, signature.pointConstructors.length), fullApd2Type);
        fullApd2Type = sandboxPi(motiveName, extractSandboxPiBinder(fullEliminatorEntry[1], 1 + signature.parameters.length).type, fullApd2Type);
        fullApd2Type = sandboxWrapPis(signature.parameters, fullApd2Type);
        fullApd2Type = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullApd2Type);
        const leftRecursorAction = sandboxApply(sandboxVar("ap"), recursorHead, leftPathData.pathTerm);
        const rightRecursorAction = sandboxApply(sandboxVar("ap"), recursorHead, rightPathData.pathTerm);
        let publicAp2Type = sandboxWrapPis(path.arguments, sandboxEquality(leftRecursorAction, rightRecursorAction));
        publicAp2Type = sandboxWrapPis(allRecursorPathBinders, publicAp2Type);
        publicAp2Type = sandboxWrapPis(extractSandboxPiBinders(base.recursor[1], signature.parameters.length + 1, signature.pointConstructors.length), publicAp2Type);
        publicAp2Type = sandboxPi(motiveName, extractSandboxPiBinder(base.recursor[1], signature.parameters.length).type, publicAp2Type);
        publicAp2Type = sandboxWrapPis(signature.parameters, publicAp2Type);
        const leftFullRecursorAction = sandboxApply(sandboxVar("ap"), fullRecursorHead, leftPathData.pathTerm);
        const rightFullRecursorAction = sandboxApply(sandboxVar("ap"), fullRecursorHead, rightPathData.pathTerm);
        let fullAp2Type = sandboxWrapPis(path.arguments, sandboxEquality(leftFullRecursorAction, rightFullRecursorAction));
        fullAp2Type = sandboxWrapPis(allRecursorPathBinders, fullAp2Type);
        fullAp2Type = sandboxWrapPis(extractSandboxPiBinders(fullRecursorEntry[1], 1 + signature.parameters.length + 1, signature.pointConstructors.length), fullAp2Type);
        fullAp2Type = sandboxPi(motiveName, extractSandboxPiBinder(fullRecursorEntry[1], 1 + signature.parameters.length).type, fullAp2Type);
        fullAp2Type = sandboxWrapPis(signature.parameters, fullAp2Type);
        fullAp2Type = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullAp2Type);
        const correctedRecursorMethod = sandboxCompose(sandboxCompose(leftRecursorComputation, recursorMethodValue), sandboxApply(sandboxVar("inveq"), rightRecursorComputation));
        const correctedRecursorMethodFull = sandboxCompose(sandboxCompose(leftRecursorComputationFull, Core.clone(recursorMethodValue)), sandboxApply(sandboxVar("inveq"), rightRecursorComputationFull));
        const strongRecursorAction = (head) => sandboxApply(sandboxVar("hit_ap2"), head, Core.clone(pathTerm));
        let publicStrongAp2Type = sandboxWrapPis(path.arguments, sandboxEquality(strongRecursorAction(Core.clone(recursorHead)), correctedRecursorMethod));
        publicStrongAp2Type = sandboxWrapPis(allRecursorPathBinders, publicStrongAp2Type);
        publicStrongAp2Type = sandboxWrapPis(extractSandboxPiBinders(base.recursor[1], signature.parameters.length + 1, signature.pointConstructors.length), publicStrongAp2Type);
        publicStrongAp2Type = sandboxPi(motiveName, extractSandboxPiBinder(base.recursor[1], signature.parameters.length).type, publicStrongAp2Type);
        publicStrongAp2Type = sandboxWrapPis(signature.parameters, publicStrongAp2Type);
        let fullStrongAp2Type = sandboxWrapPis(path.arguments, sandboxEquality(strongRecursorAction(Core.clone(fullRecursorHead)), correctedRecursorMethodFull));
        fullStrongAp2Type = sandboxWrapPis(allRecursorPathBinders, fullStrongAp2Type);
        fullStrongAp2Type = sandboxWrapPis(extractSandboxPiBinders(fullRecursorEntry[1], 1 + signature.parameters.length + 1, signature.pointConstructors.length), fullStrongAp2Type);
        fullStrongAp2Type = sandboxPi(motiveName, extractSandboxPiBinder(fullRecursorEntry[1], 1 + signature.parameters.length).type, fullStrongAp2Type);
        fullStrongAp2Type = sandboxWrapPis(signature.parameters, fullStrongAp2Type);
        fullStrongAp2Type = sandboxPi(motiveUniverseName, sandboxVar("U@"), fullStrongAp2Type);
        computationTypes.push([`apd_${path.name}`, publicApd2Type], [`@apd_${path.name}`, fullApd2Type], [`ap_${path.name}`, publicAp2Type], [`@ap_${path.name}`, fullAp2Type], [`ap2_${path.name}`, publicStrongAp2Type], [`@ap2_${path.name}`, fullStrongAp2Type]);
    }
    const generatedNames = [
        signature.name,
        ...signature.pointConstructors.map(constructor => constructor.name),
        ...signature.pathConstructors.map(path => path.name),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`,
        ...signature.pathConstructors.flatMap(path => [
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`
        ]),
        ...signature.twoPathConstructors.flatMap(path => [
            path.name,
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`,
            `ap2_${path.name}`,
            `@ap2_${path.name}`
        ]),
        ...signature.threePathConstructors.map(path => path.name)
    ];
    return {
        type: [base.type[0], Core.clone(base.type[1])],
        constructors: base.constructors.map(([name, type]) => [name, Core.clone(type)]),
        auxiliaryTypes: [
            ...pathTypes,
            [`@ind_${signature.name}`, fullEliminatorType],
            [`@rec_${signature.name}`, fullRecursorType],
            ...computationTypes
        ],
        eliminator: [`ind_${signature.name}`, publicEliminatorType],
        recursor: [`rec_${signature.name}`, publicRecursorType],
        computeRules,
        metadata: {
            version: signature.threePathConstructors.length
                ? 5
                : signature.twoPathConstructors.length ? 4 : 3,
            kind: signature.threePathConstructors.length
                ? "hit3"
                : signature.twoPathConstructors.length ? "hit2" : "hit1",
            dimension: signature.threePathConstructors.length
                ? 3
                : signature.twoPathConstructors.length ? 2 : 1,
            ruleSchemaVersion: 1,
            typeName: signature.name,
            parameterCount: signature.parameters.length,
            indexCount: 0,
            indices: [],
            eliminatorName: `ind_${signature.name}`,
            fullEliminatorName: `@ind_${signature.name}`,
            recursorName: `rec_${signature.name}`,
            fullRecursorName: `@rec_${signature.name}`,
            constructors: signature.pointConstructors.map(constructor => ({
                name: constructor.name,
                argumentTypes: constructor.argumentAsts.map(argument => Core.clone(argument.type)),
                argumentNames: constructor.argumentAsts.map(argument => argument.name),
                recursiveArguments: [],
                resultIndices: []
            })),
            pathConstructors: signature.pathConstructors.map(path => ({
                name: path.name,
                argumentTypes: path.arguments.map(argument => Core.clone(argument.type)),
                argumentNames: path.arguments.map(argument => argument.name),
                left: Core.clone(path.left),
                right: Core.clone(path.right),
                computationName: `apd_${path.name}`
            })),
            twoPathConstructors: signature.twoPathConstructors.map(path => ({
                name: path.name,
                argumentTypes: path.arguments.map(argument => Core.clone(argument.type)),
                argumentNames: path.arguments.map(argument => argument.name),
                left: Core.clone(path.left),
                right: Core.clone(path.right),
                leftPath: flattenApplication(path.left)[0]?.name ?? "",
                rightPath: flattenApplication(path.right)[0]?.name ?? "",
                computationName: `apd_${path.name}`,
                strongComputationName: `ap2_${path.name}`
            })),
            threePathConstructors: signature.threePathConstructors.map(path => ({
                name: path.name,
                argumentTypes: path.arguments.map(argument => Core.clone(argument.type)),
                argumentNames: path.arguments.map(argument => argument.name),
                left: Core.clone(path.left),
                right: Core.clone(path.right),
                leftTwoPath: path.leftTwoPath,
                rightTwoPath: path.rightTwoPath,
                sourcePath: Core.clone(path.sourcePath),
                targetPath: Core.clone(path.targetPath)
            }))
        },
        generatedNames
    };
}
function extractSandboxPiBinder(type, depth) {
    let cursor = type;
    for (let index = 0; index < depth; index++) {
        if ((cursor.type !== "P" && cursor.type !== "->") || !cursor.nodes?.[1]) {
            throw new Error("HIT 消去器 binder 结构不完整");
        }
        cursor = cursor.nodes[1];
    }
    if ((cursor.type !== "P" && cursor.type !== "->") || !cursor.nodes?.[0]) {
        throw new Error("HIT 消去器 binder 结构不完整");
    }
    return {
        name: cursor.type === "P" && cursor.name ? cursor.name : `x${depth}`,
        type: Core.clone(cursor.nodes[0]),
        typeSource: parser.stringify(cursor.nodes[0])
    };
}
function extractSandboxPiBinders(type, depth, count) {
    return Array.from({ length: count }, (_, index) => extractSandboxPiBinder(type, depth + index));
}
function parseOrdinarySandboxAst(ast) {
    if ((ast.type !== ":" && ast.type !== ":=") || ast.nodes?.[0]?.type !== "var") {
        throw new Error("沙盒声明必须使用“名称 : 类型”或“名称 := 项”格式");
    }
    const name = ast.nodes[0].name;
    if (!/^(?:[A-Za-z_][A-Za-z0-9_']*|[0-9]+[A-Za-z_][A-Za-z0-9_']*)$/.test(name)) {
        throw new Error(`声明名称不合法：${name}`);
    }
    if (ast.type === ":=") {
        const rhs = ast.nodes[1];
        if (!rhs)
            throw new Error("定义缺少右侧项");
        if (rhs.type === ":") {
            if (!rhs.nodes?.[0] || !rhs.nodes?.[1])
                throw new Error("定义类型注释不完整");
            return {
                ast,
                name,
                typeAst: rhs.nodes[1],
                typeSource: parser.stringify(rhs.nodes[1]),
                definitionAst: rhs.nodes[0]
            };
        }
        return {
            ast,
            name,
            typeSource: "",
            definitionAst: rhs
        };
    }
    return {
        ast,
        name,
        typeAst: ast.nodes[1],
        typeSource: parser.stringify(ast.nodes[1])
    };
}
export function parseSandboxDeclaration(source) {
    const text = normalizeSandboxSource(source);
    if (!text)
        throw new Error("声明不能为空");
    if (/^hit\s/i.test(text)) {
        const hit = parseSandboxHit(text);
        const typeAst = sandboxWrapPis([...hit.parameters, ...hit.indices], Core.clone(hit.universeAst));
        return {
            ast: undefined,
            name: hit.name,
            typeAst,
            typeSource: parser.stringify(typeAst),
            hit
        };
    }
    if (/^inductive\s/i.test(text)) {
        const inductive = parseSandboxInductive(text);
        return {
            ast: undefined,
            name: inductive.name,
            typeAst: sandboxWrapPis([...inductive.parameters, ...inductive.indices], Core.clone(inductive.universeAst)),
            typeSource: parser.stringify(sandboxWrapPis([...inductive.parameters, ...inductive.indices], Core.clone(inductive.universeAst))),
            inductive
        };
    }
    // This exported parser is also the compatibility boundary used by
    // migrated saves, workers, and existing programmatic fixtures. Strict
    // rejection belongs to the browser editor, not this low-level API.
    return parseOrdinarySandboxAst(parser.parse(text));
}
/** Parse a declaration entered through the new Unicode-facing editor. */
export function parseSandboxDeclarationSurface(source) {
    // Pasted/user-entered aliases must be expanded before legacy detection.
    // Otherwise `\\*` is mistaken for the old `*` operator and rejected even
    // though it is the supported surface spelling for `▪`.
    const text = expandTypeTheoryAliasesInSurface(normalizeSandboxSource(source));
    if (!text)
        throw new Error("声明不能为空");
    if (hasLegacySurfaceSyntax(text)) {
        throw new Error("不再支持旧语法，请使用 Unicode 符号");
    }
    if (/^(?:hit|inductive)\s/i.test(text))
        return parseSandboxDeclaration(text);
    return parseOrdinarySandboxAst(parser.parseSurface(text));
}
/** Parse a stored declaration at either the modern or legacy boundary. */
function parseSandboxStoredDeclaration(source) {
    const text = normalizeSandboxSource(source);
    try {
        return parseSandboxDeclarationSurface(text);
    }
    catch (surfaceError) {
        try {
            return parseSandboxDeclaration(text);
        }
        catch {
            throw surfaceError;
        }
    }
}
export function createSandboxDeclaration(source, id) {
    // Keep the creation path consistent with the strict editor boundary.
    // The keyboard normally expands aliases on Space, but pasted text can
    // reach this API directly (and the GUI passes the original input after
    // validation).  Expand it here before the compatibility parser sees it.
    const text = expandTypeTheoryAliasesInSurface(normalizeSandboxSource(source));
    try {
        // New declarations use the Unicode surface parser so names such as
        // `SurfaceX` and `Pfoo` survive the compact parser's historical
        // marker tokens.  Keep the compatibility parser as a fallback for
        // migrated saves and old programmatic fixtures.
        const parsed = parseSandboxStoredDeclaration(text);
        if (parsed.hit) {
            const generatedNames = sandboxHitGeneratedNames(parsed.hit);
            return {
                id,
                name: parsed.hit.name,
                kind: "hit",
                source: text,
                typeSource: parsed.hit.universe,
                enabled: true,
                trusted: true,
                status: "unchecked",
                dependencies: collectHitDependencies(parsed.hit),
                folderId: null,
                hit: parsed.hit,
                generatedNames
            };
        }
        if (parsed.inductive) {
            const generatedNames = sandboxInductiveGeneratedNames(parsed.inductive);
            return {
                id,
                name: parsed.inductive.name,
                kind: "inductive",
                source: text,
                typeSource: parsed.inductive.universe,
                enabled: true,
                trusted: true,
                status: "unchecked",
                dependencies: collectInductiveDependencies(parsed.inductive),
                folderId: null,
                inductive: parsed.inductive,
                generatedNames
            };
        }
        const definition = parsed.definitionAst;
        const dependencies = definition
            ? [
                ...collectFreeNames(definition),
                ...(parsed.typeAst ? collectFreeNames(parsed.typeAst) : [])
            ].filter((name, index, names) => names.indexOf(name) === index)
            : collectFreeNames(parsed.typeAst);
        return {
            id,
            name: parsed.name,
            kind: parsed.definitionAst ? "definition" : declarationKind(parsed.typeAst),
            source: text,
            typeSource: parsed.typeSource,
            enabled: true,
            trusted: true,
            status: "unchecked",
            dependencies,
            folderId: null
        };
    }
    catch (error) {
        return {
            id,
            name: "",
            kind: "term",
            source: text,
            typeSource: "",
            enabled: true,
            trusted: true,
            status: "unchecked",
            error: String(error),
            dependencies: [],
            folderId: null
        };
    }
}
function sandboxInductiveGeneratedNames(signature) {
    return [
        signature.name,
        ...signature.constructors.map(ctor => ctor.name),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`
    ];
}
function sandboxHitGeneratedNames(signature) {
    return [
        signature.name,
        ...signature.pointConstructors.map(ctor => ctor.name),
        ...signature.pathConstructors.map(ctor => ctor.name),
        ...signature.twoPathConstructors.map(ctor => ctor.name),
        ...signature.threePathConstructors.map(ctor => ctor.name),
        `ind_${signature.name}`,
        `@ind_${signature.name}`,
        `rec_${signature.name}`,
        `@rec_${signature.name}`,
        ...signature.pathConstructors.flatMap(path => [
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`
        ]),
        ...signature.twoPathConstructors.flatMap(path => [
            `apd_${path.name}`,
            `@apd_${path.name}`,
            `ap_${path.name}`,
            `@ap_${path.name}`,
            `ap2_${path.name}`,
            `@ap2_${path.name}`
        ]),
        ...signature.threePathConstructors.map(path => path.name)
    ];
}
function collectInductiveDependencies(signature) {
    const own = new Set(sandboxInductiveGeneratedNames(signature));
    for (const parameter of signature.parameters)
        own.add(parameter.name);
    for (const index of signature.indices)
        own.add(index.name);
    const names = new Set();
    const collect = (ast) => {
        for (const name of collectFreeNames(ast)) {
            if (!own.has(name))
                names.add(name);
        }
    };
    for (const parameter of signature.parameters)
        collect(parameter.type);
    for (const index of signature.indices)
        collect(index.type);
    collect(signature.universeAst);
    for (const ctor of signature.constructors) {
        collect(ctor.type);
    }
    return [...names];
}
function collectHitDependencies(signature) {
    const own = new Set(sandboxHitGeneratedNames(signature));
    for (const parameter of signature.parameters)
        own.add(parameter.name);
    const names = new Set();
    const collect = (ast) => {
        for (const name of collectFreeNames(ast)) {
            if (!own.has(name))
                names.add(name);
        }
    };
    for (const parameter of signature.parameters)
        collect(parameter.type);
    collect(signature.universeAst);
    for (const constructor of signature.pointConstructors)
        collect(constructor.type);
    for (const path of signature.pathConstructors) {
        collect(path.type);
    }
    for (const path of signature.twoPathConstructors) {
        collect(path.type);
    }
    for (const path of signature.threePathConstructors) {
        collect(path.type);
    }
    return [...names];
}
function normalizeSandboxLimit(value) {
    if (value === undefined || value === null || value === "")
        return undefined;
    const numeric = Number(value);
    return Number.isFinite(numeric) && numeric >= 0
        ? Math.floor(numeric)
        : undefined;
}
/** Count source AST nodes without following parser back-references such as `origin`. */
function countSandboxSyntaxNodes(value) {
    const seen = new WeakSet();
    const stack = [value];
    let count = 0;
    while (stack.length) {
        const current = stack.pop();
        if (!current || typeof current !== "object")
            continue;
        if (seen.has(current))
            continue;
        seen.add(current);
        if (Array.isArray(current)) {
            stack.push(...current);
            continue;
        }
        const record = current;
        if (typeof record.type === "string" && Array.isArray(record.nodes))
            count++;
        for (const [key, child] of Object.entries(record)) {
            // `origin` can point back into the source tree and is presentation
            // metadata, not a unit of validation work.
            if (key === "origin")
                continue;
            if (child && typeof child === "object")
                stack.push(child);
        }
    }
    return count;
}
function estimateSandboxDeclarationNodes(source) {
    try {
        return Math.max(1, countSandboxSyntaxNodes(parseSandboxStoredDeclaration(source)));
    }
    catch {
        // A malformed source is still bounded before the normal parser error
        // path. Character count is deterministic and avoids hiding the real
        // syntax diagnostic behind an estimator failure.
        return Math.max(1, String(source ?? "").length);
    }
}
/**
 * Stage-1 sandbox model. It deliberately owns a fresh TTCoreEngine and never
 * writes to TTGui, GameSaveLoad, unlock state, theorem rows, or map state.
 */
export class SandboxEnvironment {
    builtinNames = new Set();
    systemRuleIds;
    semanticResourceScale;
    validationBudget;
    validationCachePreludeKey;
    engine;
    /** Fully elaborated body-less declaration types used by the bridge. */
    axiomTypes = new Map();
    /** Checked source bodies used for the read-only creative bridge. */
    definitionBodies = new Map();
    nextId = 1;
    nextFolderId = 1;
    dirtyFrom = 0;
    validatedThrough = 0;
    pendingValidationCache = null;
    /** The shared type-layer ordering/folder engine. */
    workspace = new TheoremWorkspace();
    declarations = [];
    folders = [];
    order = [];
    lastValidationDurationMs = 0;
    lastValidationStats = {
        checkedDeclarations: 0,
        replayedDeclarations: 0,
        validatedThrough: 0
    };
    constructor(options = {}) {
        // Standalone callers retain the deliberately small stage-1 prelude so
        // names such as `base` remain available for experimentation. The
        // creative UI passes its complete unlocked system set, which lets a
        // sandbox definition use built-ins such as `nat`/`ind_nat` directly.
        this.systemRuleIds = Object.freeze([
            ...new Set(options.systemRuleIds ?? isolatedSandboxSystemRuleIds)
        ]);
        this.semanticResourceScale = options.semanticResourceScale;
        this.validationCachePreludeKey = sandboxValidationPreludeKey(this.systemRuleIds, this.semanticResourceScale);
        this.validationBudget = Object.freeze({
            maxDeclarations: normalizeSandboxLimit(options.validationMaxDeclarations),
            maxNodes: normalizeSandboxLimit(options.validationMaxNodes),
            maxSteps: normalizeSandboxLimit(options.validationMaxSteps),
            timeoutMs: normalizeSandboxLimit(options.validationTimeoutMs)
        });
        this.engine = this.createEngine();
        for (const name of Object.keys(this.engine.core.state.sysTypes))
            this.builtinNames.add(name);
        for (const name of Object.keys(this.engine.core.state.sysDefs))
            this.builtinNames.add(name);
        this.builtinNames.add("U");
        this.builtinNames.add("U0");
    }
    createEngine() {
        const engine = new TTCoreEngine();
        const config = {
            unlockedTypes: [...this.systemRuleIds],
            inferDisplayMode: "_",
            semanticResourceScale: this.semanticResourceScale ?? 1
        };
        // Keep the process-wide Core.timeout untouched. The sandbox timeout
        // is enforced by validate() at declaration boundaries, so constructing
        // a bounded sandbox cannot leak its setting into the game Core.
        engine.configure(config);
        return engine;
    }
    add(source) {
        return this.addInFolder(source, null);
    }
    addInFolder(source, folderId) {
        if (folderId) {
            const folder = this.folders.find(item => item.id === folderId);
            if (!folder)
                throw new Error(`找不到沙盒文件夹：${folderId}`);
            if (!folder.open)
                throw new Error("折叠文件夹不能添加沙盒声明");
        }
        const before = this.validationSignatures();
        const id = `sandbox-${this.nextId++}`;
        const declaration = createSandboxDeclaration(source, id);
        declaration.folderId = folderId;
        this.declarations.push(declaration);
        this.order.push(id);
        this.syncWorkspaceFromState();
        if (folderId) {
            const mutation = this.workspace.move(id, `inside:${folderId}`);
            this.applyWorkspaceSnapshot(mutation.snapshot);
        }
        this.markWorkspaceChange(before);
        return this.validate();
    }
    replace(source, id) {
        const index = this.orderedDeclarationIndex(id);
        if (index < 0)
            throw new Error(`找不到沙盒声明：${id}`);
        const declarationIndex = this.declarations.findIndex(declaration => declaration.id === id);
        const previous = this.declarations[declarationIndex];
        const replacement = createSandboxDeclaration(source, id);
        replacement.folderId = previous.folderId;
        replacement.enabled = previous.enabled;
        this.declarations[declarationIndex] = replacement;
        this.markDirty(index);
        return this.validate();
    }
    addFolder(name = "新文件夹") {
        const folder = {
            kind: "folder",
            id: `sandbox-folder-${this.nextFolderId++}`,
            name: name.trim() || "新文件夹",
            length: 0,
            open: true,
            disabled: false
        };
        this.folders.push(folder);
        this.order.push(folder.id);
        this.syncWorkspaceFromState();
        return folder;
    }
    setFolder(id, folderId) {
        const declaration = this.find(id);
        if (folderId && !this.folders.some(folder => folder.id === folderId)) {
            throw new Error(`找不到沙盒文件夹：${folderId}`);
        }
        if (folderId) {
            const folder = this.folders.find(item => item.id === folderId);
            if (!folder.open)
                throw new Error("折叠文件夹不能接收沙盒声明");
        }
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const mutation = folderId
            ? this.workspace.move(id, `inside:${folderId}`)
            : this.workspace.move(id, " ");
        if (!mutation.changed && declaration.folderId !== folderId) {
            throw new Error(folderId
                ? "无法将沙盒声明移入该文件夹"
                : "无法将沙盒声明移出当前文件夹");
        }
        if (mutation.changed)
            this.applyWorkspaceSnapshot(mutation.snapshot);
        this.markWorkspaceChange(before);
        return this.validate();
    }
    setFolderOpen(id, open) {
        const folder = this.folders.find(item => item.id === id);
        if (!folder)
            throw new Error(`找不到沙盒文件夹：${id}`);
        this.syncWorkspaceFromState();
        const mutation = this.workspace.setFolderOpen(id, !!open);
        this.applyWorkspaceSnapshot(mutation.snapshot);
        return this.validate();
    }
    setFolderDisabled(id, disabled) {
        const folder = this.folders.find(item => item.id === id);
        if (!folder)
            throw new Error(`找不到沙盒文件夹：${id}`);
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const mutation = this.workspace.setFolderDisabled(id, !!disabled);
        this.applyWorkspaceSnapshot(mutation.snapshot);
        this.markWorkspaceChange(before);
        return this.validate();
    }
    renameFolder(id, name) {
        const folder = this.folders.find(item => item.id === id);
        if (!folder)
            throw new Error(`找不到沙盒文件夹：${id}`);
        this.syncWorkspaceFromState();
        const mutation = this.workspace.renameFolder(id, name.trim() || folder.name);
        this.applyWorkspaceSnapshot(mutation.snapshot);
        return this.validate();
    }
    removeFolder(id) {
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const mutation = this.workspace.removeFolder(id);
        if (!mutation.changed)
            return this.validate();
        this.applyWorkspaceSnapshot(mutation.snapshot);
        this.markWorkspaceChange(before);
        return this.validate();
    }
    setEnabled(id, enabled) {
        const declaration = this.find(id);
        const index = this.orderedDeclarationIndex(id);
        declaration.enabled = !!enabled;
        this.markDirty(index);
        return this.validate();
    }
    remove(id) {
        const before = this.validationSignatures();
        const declarationIndex = this.declarations.findIndex(declaration => declaration.id === id);
        if (declarationIndex >= 0)
            this.declarations.splice(declarationIndex, 1);
        if (declarationIndex >= 0)
            this.order = this.order.filter(item => item !== id);
        if (declarationIndex >= 0) {
            this.syncWorkspaceFromState();
            this.markWorkspaceChange(before);
        }
        return this.validate();
    }
    reorder(id, targetIndex) {
        if (!this.declarations.some(declaration => declaration.id === id)) {
            throw new Error(`找不到沙盒声明：${id}`);
        }
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const targetItemIndex = this.workspace.itemIndexForTheorem(Math.max(0, Math.floor(targetIndex)));
        const snapshot = this.workspace.snapshot();
        const destination = snapshot[targetItemIndex]?.id ?? " ";
        const mutation = this.workspace.move(id, destination);
        if (mutation.changed)
            this.applyWorkspaceSnapshot(mutation.snapshot);
        this.markWorkspaceChange(before);
        return this.validate();
    }
    /** Apply the same drag/drop destination grammar as the type-layer list. */
    moveItem(sourceId, destination) {
        const before = this.validationSignatures();
        this.syncWorkspaceFromState();
        const mutation = this.workspace.move(sourceId, destination);
        if (mutation.changed) {
            this.applyWorkspaceSnapshot(mutation.snapshot);
            this.markWorkspaceChange(before);
        }
        return mutation;
    }
    workspaceLayout() {
        this.syncWorkspaceFromState();
        return this.workspace.layout();
    }
    folderAppendIndex(folderId) {
        this.syncWorkspaceFromState();
        return this.workspace.folderAppendIndex(folderId);
    }
    validate(options = {}) {
        const started = performance.now();
        this.syncWorkspaceFromState();
        const workspaceItems = this.workspace.snapshot();
        const layout = new Map(this.workspace.layout().map(item => [item.id, item]));
        const orderedDeclarations = workspaceItems
            .filter((item) => item.kind === "theorem")
            .map(item => this.declarations.find(declaration => declaration.id === item.id))
            .filter((declaration) => !!declaration);
        const budget = this.validationBudgetFor(options);
        const estimatedNodes = budget.maxNodes === undefined && budget.maxSteps === undefined
            ? 0
            : orderedDeclarations.reduce((total, declaration) => total + estimateSandboxDeclarationNodes(declaration.source), 0);
        const estimatedSteps = orderedDeclarations.length + estimatedNodes;
        const budgetFailure = this.validationBudgetFailure(started, budget, orderedDeclarations.length, estimatedNodes, estimatedSteps);
        if (budgetFailure)
            return budgetFailure;
        if (options.shouldCancel?.()) {
            return this.validationInterrupted("cancelled", started, 0, 0);
        }
        let replayedDeclarations = 0;
        if (this.pendingValidationCache && this.dirtyFrom === 0) {
            const cacheReplay = this.restorePersistedValidationCache(this.pendingValidationCache, orderedDeclarations, layout, options, budget, started);
            this.pendingValidationCache = null;
            if (cacheReplay.status === "cancelled" || cacheReplay.status === "budget-exhausted") {
                return this.validationInterrupted(cacheReplay.status, started, 0, cacheReplay.count);
            }
            if (cacheReplay.status === "restored") {
                this.validatedThrough = cacheReplay.count;
                this.dirtyFrom = cacheReplay.count;
                replayedDeclarations += cacheReplay.count;
            }
        }
        else {
            this.pendingValidationCache = null;
        }
        if (this.dirtyFrom < this.validatedThrough || this.validatedThrough > orderedDeclarations.length) {
            if (options.shouldCancel?.()) {
                return this.validationInterrupted("cancelled", started, 0, 0);
            }
            const prefixLength = Math.min(this.dirtyFrom, this.validatedThrough, orderedDeclarations.length);
            this.replayValidatedPrefix(orderedDeclarations, prefixLength, layout);
            this.validatedThrough = prefixLength;
            replayedDeclarations = prefixLength;
        }
        const allNames = new Set();
        const declarationByName = new Map();
        for (const candidate of this.declarations) {
            try {
                const parsed = parseSandboxStoredDeclaration(candidate.source);
                if (parsed.hit) {
                    for (const name of sandboxHitGeneratedNames(parsed.hit)) {
                        allNames.add(name);
                        declarationByName.set(name, candidate);
                    }
                }
                else if (parsed.inductive) {
                    for (const name of sandboxInductiveGeneratedNames(parsed.inductive)) {
                        allNames.add(name);
                        declarationByName.set(name, candidate);
                    }
                }
                else {
                    allNames.add(parsed.name);
                    declarationByName.set(parsed.name, candidate);
                }
            }
            catch {
                if (candidate.name) {
                    allNames.add(candidate.name);
                    declarationByName.set(candidate.name, candidate);
                }
            }
        }
        const seenNames = new Set();
        let firstError;
        let checkedDeclarations = 0;
        for (let index = 0; index < this.validatedThrough; index++) {
            if (options.shouldCancel?.()) {
                return this.validationInterrupted("cancelled", started, checkedDeclarations, replayedDeclarations);
            }
            const declaration = orderedDeclarations[index];
            if (declaration.status === "invalid"
                && /未知的沙盒名称|禁止前向引用/.test(declaration.error ?? "")) {
                const unresolved = declaration.dependencies.find(dependency => !this.builtinNames.has(dependency) && !seenNames.has(dependency));
                if (unresolved) {
                    declaration.error = String(new Error(allNames.has(unresolved)
                        ? `禁止前向引用：${declaration.name} 依赖 ${unresolved}`
                        : `未知的沙盒名称：${unresolved}`));
                }
            }
            if (declaration.status === "invalid")
                firstError ??= declaration.error;
            for (const name of declaration.generatedNames ?? (declaration.name ? [declaration.name] : [])) {
                seenNames.add(name);
            }
        }
        for (let index = this.validatedThrough; index < orderedDeclarations.length; index++) {
            if (options.shouldCancel?.()) {
                return this.validationInterrupted("cancelled", started, checkedDeclarations, replayedDeclarations);
            }
            if (budget.timeoutMs !== undefined && performance.now() - started >= budget.timeoutMs) {
                return this.validationInterrupted("budget-exhausted", started, checkedDeclarations, replayedDeclarations);
            }
            const declaration = orderedDeclarations[index];
            checkedDeclarations++;
            // A declaration may have been edited, disabled, or moved since
            // the previous validation. Never let its old transparent body
            // leak into the next bridge snapshot.
            if (declaration.name)
                this.axiomTypes.delete(declaration.name);
            if (declaration.name)
                this.definitionBodies.delete(declaration.name);
            declaration.error = undefined;
            declaration.dependencies = [];
            declaration.inductive = undefined;
            declaration.hit = undefined;
            declaration.generatedNames = undefined;
            const rowState = layout.get(declaration.id);
            if (rowState?.disabled) {
                declaration.status = "disabled";
                for (const name of declaration.name ? [declaration.name] : [])
                    seenNames.add(name);
                continue;
            }
            if (!declaration.enabled) {
                declaration.status = "disabled";
                for (const name of declaration.name ? [declaration.name] : [])
                    seenNames.add(name);
                continue;
            }
            let parsed;
            try {
                parsed = parseSandboxStoredDeclaration(declaration.source);
                declaration.name = parsed.name;
                declaration.typeSource = parsed.typeSource;
                if (parsed.hit) {
                    declaration.kind = "hit";
                    declaration.hit = parsed.hit;
                    declaration.generatedNames = sandboxHitGeneratedNames(parsed.hit);
                    declaration.dependencies = collectHitDependencies(parsed.hit);
                }
                else if (parsed.inductive) {
                    declaration.kind = "inductive";
                    declaration.inductive = parsed.inductive;
                    declaration.generatedNames = sandboxInductiveGeneratedNames(parsed.inductive);
                    declaration.dependencies = collectInductiveDependencies(parsed.inductive);
                }
                else if (parsed.definitionAst) {
                    declaration.kind = "definition";
                    declaration.dependencies = [
                        ...collectFreeNames(parsed.definitionAst),
                        ...(parsed.typeAst ? collectFreeNames(parsed.typeAst) : [])
                    ].filter((name, position, names) => names.indexOf(name) === position);
                }
                else {
                    declaration.kind = declarationKind(parsed.typeAst);
                    declaration.dependencies = collectFreeNames(parsed.typeAst);
                }
            }
            catch (error) {
                this.markInvalid(declaration, error);
                firstError ??= declaration.error;
                if (declaration.name)
                    seenNames.add(declaration.name);
                continue;
            }
            const ownedNames = declaration.generatedNames ?? [declaration.name];
            const conflict = ownedNames.find(name => seenNames.has(name)
                || this.builtinNames.has(name)
                || this.engine.core.hasConst(name));
            if (conflict) {
                this.markInvalid(declaration, new Error(`沙盒声明名称冲突：${conflict}`));
                firstError ??= declaration.error;
                for (const name of ownedNames)
                    seenNames.add(name);
                continue;
            }
            let dependencyError;
            for (const dependency of declaration.dependencies) {
                if (dependency === declaration.name) {
                    dependencyError = new Error(`不支持递归沙盒定义：${declaration.name}`);
                    break;
                }
                if (this.builtinNames.has(dependency))
                    continue;
                if (!seenNames.has(dependency)) {
                    dependencyError = new Error(allNames.has(dependency)
                        ? `禁止前向引用：${declaration.name} 依赖 ${dependency}`
                        : `未知的沙盒名称：${dependency}`);
                    break;
                }
                const dependencyDeclaration = declarationByName.get(dependency);
                if (!dependencyDeclaration || dependencyDeclaration.status !== "valid") {
                    dependencyError = new Error(`依赖声明无效：${dependency}`);
                    break;
                }
            }
            if (dependencyError) {
                this.markInvalid(declaration, dependencyError);
                firstError ??= declaration.error;
                for (const name of ownedNames)
                    seenNames.add(name);
                continue;
            }
            try {
                if (parsed.hit) {
                    const bundle = lowerSandboxHit(parsed.hit);
                    this.engine.core.registerSystemInductive(bundle);
                    declaration.generatedNames = [...bundle.generatedNames];
                }
                else if (parsed.inductive) {
                    const bundle = lowerSandboxInductive(parsed.inductive);
                    this.engine.core.registerSystemInductive(bundle);
                    declaration.generatedNames = [...bundle.generatedNames];
                }
                else if (parsed.definitionAst) {
                    // Validate the source (including an optional type
                    // ascription) before installing its transparent body. The
                    // check is performed in the same Core so subsequent
                    // declarations can depend on this definition, while the
                    // explicit cleanup keeps a failed registration from
                    // leaving a stale system entry behind.
                    const definitionAst = {
                        type: ":=",
                        name: "",
                        nodes: [
                            { type: "var", name: declaration.name, nodes: [] },
                            parsed.typeAst
                                ? {
                                    type: ":",
                                    name: "",
                                    nodes: [
                                        Core.clone(parsed.definitionAst),
                                        Core.clone(parsed.typeAst)
                                    ]
                                }
                                : Core.clone(parsed.definitionAst)
                        ]
                    };
                    const checked = this.engine.core.checkDefinition(definitionAst, []);
                    const body = checked.filledDefinition.type === ":"
                        ? checked.filledDefinition.nodes?.[0]
                        : checked.filledDefinition;
                    if (!body)
                        throw new Error("定义体为空");
                    try {
                        this.engine.core.registerSystemDefinition(declaration.name, Core.clone(body));
                    }
                    catch (error) {
                        this.engine.core.setSystemDefinition(declaration.name);
                        this.engine.core.clearDefinitionCache(declaration.name);
                        throw error;
                    }
                    const inferredType = parsed.typeAst
                        ?? this.engine.core.state.defTypes[declaration.name]?.type
                        ?? definitionAst.checked;
                    if (inferredType) {
                        declaration.typeSource = parser.stringify(inferredType);
                        declaration.kind = "definition";
                    }
                    this.definitionBodies.set(declaration.name, Core.clone(body));
                }
                else {
                    const type = this.engine.core.checkTypeFormation(parsed.typeAst, []);
                    this.engine.core.setSystemType(declaration.name, Core.clone(type));
                    this.engine.core.syncSemanticTypes();
                    this.axiomTypes.set(declaration.name, Core.clone(type));
                }
                declaration.status = "valid";
            }
            catch (error) {
                this.definitionBodies.delete(declaration.name);
                this.markInvalid(declaration, error);
                firstError ??= declaration.error;
            }
            for (const name of ownedNames)
                seenNames.add(name);
        }
        if (options.shouldCancel?.()) {
            return this.validationInterrupted("cancelled", started, checkedDeclarations, replayedDeclarations);
        }
        if (budget.timeoutMs !== undefined && performance.now() - started >= budget.timeoutMs) {
            return this.validationInterrupted("budget-exhausted", started, checkedDeclarations, replayedDeclarations);
        }
        this.validatedThrough = orderedDeclarations.length;
        this.dirtyFrom = this.validatedThrough;
        this.lastValidationDurationMs = performance.now() - started;
        this.lastValidationStats = {
            checkedDeclarations,
            replayedDeclarations,
            validatedThrough: this.validatedThrough
        };
        const validationCache = this.buildValidationCache();
        return {
            ok: !this.declarations.some(declaration => declaration.status === "invalid"),
            declarations: this.getDeclarations(),
            error: firstError,
            status: firstError ? "invalid" : "ok",
            bridge: this.bridge(),
            validationStats: { ...this.lastValidationStats },
            validationCache
        };
    }
    /** Return the enabled, validated, read-only creative-mode projection. */
    bridge() {
        const axioms = [];
        const inductives = [];
        const definitions = [];
        const order = [];
        const layout = new Map(this.workspace.layout().map(item => [item.id, item]));
        const ordered = this.workspace.snapshot()
            .filter((item) => item.kind === "theorem")
            .map(item => this.declarations.find(declaration => declaration.id === item.id))
            .filter((declaration) => !!declaration);
        for (const declaration of ordered) {
            const state = layout.get(declaration.id);
            if (!declaration.enabled || declaration.status !== "valid" || state?.disabled)
                continue;
            if (declaration.hit) {
                try {
                    inductives.push(lowerSandboxHit(declaration.hit));
                    order.push({ kind: "inductive", name: declaration.name });
                }
                catch { }
                continue;
            }
            if (declaration.inductive) {
                try {
                    inductives.push(lowerSandboxInductive(declaration.inductive));
                    order.push({ kind: "inductive", name: declaration.name });
                }
                catch { }
                continue;
            }
            try {
                const parsed = parseSandboxStoredDeclaration(declaration.source);
                if (parsed.definitionAst) {
                    const body = this.definitionBodies.get(declaration.name) ?? parsed.definitionAst;
                    definitions.push([declaration.name, Core.clone(body)]);
                    order.push({ kind: "definition", name: declaration.name });
                }
                else if (!parsed.inductive && !parsed.hit && parsed.typeAst) {
                    const type = this.axiomTypes.get(declaration.name);
                    if (type) {
                        axioms.push([declaration.name, Core.clone(type)]);
                        order.push({ kind: "axiom", name: declaration.name });
                    }
                }
            }
            catch { }
        }
        return { axioms, inductives, definitions, order };
    }
    check(source) {
        const started = performance.now();
        const normalized = normalizeSandboxSource(source);
        let ast;
        try {
            // Use the shared surface/legacy boundary so generated sandbox
            // names (for example `SurfaceX`) stay intact in both modern UI
            // input and old saved queries.
            ast = parser.parseSurfaceOrLegacy(normalized);
        }
        catch (error) {
            return {
                ok: false,
                error: String(error),
                timeout: false,
                durationMs: performance.now() - started,
                source
            };
        }
        let result = this.engine.checkAst(ast);
        // A common sandbox query writes a telescope before a final type
        // assertion: `PA:U,...,term : T`.  The surface parser places `:`
        // outside the telescope, leaving T's binder names apparently free.
        // Retry with the assertion scoped under those binders; this changes
        // only the sandbox query convenience layer, not Core syntax.
        if (!result.ok) {
            try {
                if (ast.type === ":" && ast.nodes?.[0] && ast.nodes?.[1]) {
                    const binders = [];
                    let term = ast.nodes[0];
                    while ((term.type === "P" || term.type === "->")
                        && term.nodes?.[0] && term.nodes?.[1]) {
                        binders.push({
                            type: term.type,
                            name: term.name,
                            domain: Core.clone(term.nodes[0])
                        });
                        term = term.nodes[1];
                    }
                    if (binders.length) {
                        let lambda = Core.clone(term);
                        let expected = Core.clone(ast.nodes[1]);
                        for (let index = binders.length - 1; index >= 0; index--) {
                            const name = binders[index].name || `_sandbox${index}`;
                            lambda = {
                                type: "L",
                                name,
                                nodes: [Core.clone(binders[index].domain), lambda]
                            };
                            expected = {
                                type: "P",
                                name,
                                nodes: [Core.clone(binders[index].domain), expected]
                            };
                        }
                        const inferred = this.engine.checkAst(lambda);
                        if (inferred.ok && inferred.type) {
                            const equality = this.engine.checkAst({
                                type: "===",
                                name: "",
                                nodes: [Core.clone(inferred.type), expected]
                            });
                            if (equality.ok)
                                result = inferred;
                        }
                    }
                }
            }
            catch { }
        }
        return { ...result, source };
    }
    getDeclarations() {
        return this.declarations.map(declaration => ({ ...declaration, dependencies: [...declaration.dependencies] }));
    }
    toJSON() {
        this.syncWorkspaceFromState();
        const snapshot = this.workspace.snapshot();
        const validationCache = this.buildValidationCache();
        return {
            version: SANDBOX_SAVE_VERSION,
            declarations: this.getDeclarations(),
            folders: snapshot
                .filter((item) => item.kind === "folder")
                .map(folder => ({ ...folder })),
            order: snapshot.map(item => item.id),
            ...(validationCache.entries.length ? { validationCache } : {})
        };
    }
    serialize() {
        return JSON.stringify(this.toJSON());
    }
    load(value, validationOptions = {}) {
        const parsed = typeof value === "string" ? JSON.parse(value) : value;
        const save = migrateLegacySandboxSave(parsed);
        if (!save || save.version !== SANDBOX_SAVE_VERSION || !Array.isArray(save.declarations)) {
            throw new Error("不支持的沙盒存档版本");
        }
        const beforeSignatures = this.validationSignatures();
        const previousDeclarations = new Map(this.declarations.map(declaration => [declaration.id, declaration]));
        const cleanPrefix = Math.min(this.dirtyFrom, this.validatedThrough);
        this.folders = Array.isArray(save.folders)
            ? save.folders.map((raw, index) => ({
                kind: "folder",
                id: String(raw.id || `sandbox-folder-${index + 1}`),
                name: String(raw.name || "新文件夹"),
                // Older sandbox saves did not persist the flat subtree length.
                // Keep a marker until the order and declaration ownership are
                // available so it can be reconstructed below.
                length: Number.isFinite(Number(raw.length)) ? Number(raw.length) : -1,
                open: raw.open !== false,
                disabled: !!raw.disabled
            }))
            : [];
        const knownIds = new Set([
            ...this.folders.map(folder => folder.id),
            ...save.declarations.map(declaration => declaration.id)
        ]);
        const folderIds = new Set(this.folders.map(folder => folder.id));
        this.declarations = save.declarations.map((raw, index) => {
            const source = String(raw.source ?? (raw.name && raw.typeSource ? `${raw.name} : ${raw.typeSource}` : ""));
            const declaration = createSandboxDeclaration(source, String(raw.id || `sandbox-${index + 1}`));
            declaration.enabled = raw.enabled !== false;
            declaration.folderId = raw.folderId && folderIds.has(raw.folderId) ? raw.folderId : null;
            return declaration;
        });
        this.order = (Array.isArray(save.order) ? save.order : [])
            .filter(id => knownIds.has(id));
        for (const id of [...this.folders.map(folder => folder.id), ...this.declarations.map(declaration => declaration.id)]) {
            if (!this.order.includes(id))
                this.order.push(id);
        }
        this.repairLegacyFolderLengths();
        this.syncWorkspaceFromState();
        const afterSignatures = this.validationSignatures();
        const commonLimit = Math.min(beforeSignatures.length, afterSignatures.length, cleanPrefix);
        let commonPrefix = 0;
        while (commonPrefix < commonLimit
            && beforeSignatures[commonPrefix] === afterSignatures[commonPrefix]) {
            commonPrefix++;
        }
        const orderedIds = this.workspace.snapshot()
            .filter((item) => item.kind === "theorem")
            .map(item => item.id);
        for (let index = 0; index < commonPrefix; index++) {
            const id = orderedIds[index];
            const previous = previousDeclarations.get(id);
            const nextIndex = this.declarations.findIndex(declaration => declaration.id === id);
            if (!previous || nextIndex < 0)
                continue;
            previous.folderId = this.declarations[nextIndex].folderId;
            this.declarations[nextIndex] = previous;
        }
        const maxId = this.declarations.reduce((max, declaration) => {
            const match = declaration.id.match(/^sandbox-(\d+)$/);
            return match ? Math.max(max, Number(match[1])) : max;
        }, 0);
        this.nextId = maxId + 1;
        this.nextFolderId = this.folders.reduce((max, folder) => {
            const match = folder.id.match(/^sandbox-folder-(\d+)$/);
            return match ? Math.max(max, Number(match[1])) : max;
        }, 0) + 1;
        this.pendingValidationCache = save.validationCache ?? null;
        this.markDirty(commonPrefix);
        return this.validate(validationOptions);
    }
    syncWorkspaceFromState() {
        const folders = new Map(this.folders.map(folder => [folder.id, folder]));
        const declarations = new Map(this.declarations.map(declaration => [declaration.id, declaration]));
        const items = [];
        for (const id of this.order) {
            const folder = folders.get(id);
            if (folder) {
                items.push({
                    kind: "folder",
                    id: folder.id,
                    name: folder.name,
                    length: Math.max(0, Number(folder.length) || 0),
                    open: folder.open,
                    disabled: folder.disabled
                });
                continue;
            }
            const declaration = declarations.get(id);
            if (declaration) {
                items.push({ kind: "theorem", id: declaration.id, value: declaration.source, local: false });
            }
        }
        // Keep external/legacy array edits visible to the shared model.
        for (const folder of this.folders) {
            if (!items.some(item => item.id === folder.id)) {
                items.push({
                    kind: "folder",
                    id: folder.id,
                    name: folder.name,
                    length: Math.max(0, Number(folder.length) || 0),
                    open: folder.open,
                    disabled: folder.disabled
                });
                this.order.push(folder.id);
            }
        }
        for (const declaration of this.declarations) {
            if (!items.some(item => item.id === declaration.id)) {
                items.push({ kind: "theorem", id: declaration.id, value: declaration.source, local: false });
                this.order.push(declaration.id);
            }
        }
        this.workspace.replace(items);
    }
    /**
     * Recover the flat folder lengths used by the shared workspace from old
     * saves that only stored `folderId` on declarations.  Explicit lengths
     * remain authoritative; only the legacy `-1` marker is repaired.
     */
    repairLegacyFolderLengths() {
        const positions = new Map(this.order.map((id, index) => [id, index]));
        for (const folder of this.folders) {
            if (folder.length >= 0)
                continue;
            const folderIndex = positions.get(folder.id);
            if (folderIndex === undefined) {
                folder.length = 0;
                continue;
            }
            let last = folderIndex;
            for (const declaration of this.declarations) {
                if (declaration.folderId !== folder.id)
                    continue;
                const index = positions.get(declaration.id);
                if (index !== undefined && index > last)
                    last = index;
            }
            folder.length = Math.max(0, last - folderIndex);
        }
    }
    applyWorkspaceSnapshot(snapshot) {
        const folderById = new Map(this.folders.map(folder => [folder.id, folder]));
        const declarationById = new Map(this.declarations.map(declaration => [declaration.id, declaration]));
        const nextFolders = [];
        const nextDeclarations = [];
        this.workspace.replace(snapshot);
        const scopesById = this.workspace.folderScopesForItems(snapshot.map(item => item.id));
        for (const item of snapshot) {
            if (item.kind === "folder") {
                const previous = folderById.get(item.id);
                nextFolders.push({
                    kind: "folder",
                    id: item.id,
                    name: item.name,
                    length: item.length,
                    open: item.open,
                    disabled: item.disabled
                });
                if (previous)
                    Object.assign(previous, nextFolders[nextFolders.length - 1]);
            }
            else {
                const declaration = declarationById.get(item.id);
                if (!declaration)
                    continue;
                declaration.source = item.value;
                declaration.folderId = scopesById.get(item.id)?.at(-1)?.id ?? null;
                nextDeclarations.push(declaration);
            }
        }
        this.folders = nextFolders;
        this.declarations = nextDeclarations;
        this.order = snapshot.map(item => item.id);
    }
    buildValidationCache() {
        this.syncWorkspaceFromState();
        const snapshot = this.workspace.snapshot();
        const layout = new Map(this.workspace.layout().map(item => [item.id, item]));
        const ordered = snapshot
            .filter((item) => item.kind === "theorem")
            .map(item => this.declarations.find(declaration => declaration.id === item.id))
            .filter((declaration) => !!declaration);
        const signatures = this.validationSignatures();
        const entries = [];
        let prefixKey = this.validationCachePreludeKey;
        for (let index = 0; index < ordered.length; index++) {
            const declaration = ordered[index];
            const disabled = !declaration.enabled || !!layout.get(declaration.id)?.disabled;
            const expectedStatus = disabled ? "disabled" : "valid";
            if (declaration.status !== expectedStatus)
                break;
            prefixKey = sandboxValidationPrefixKey(prefixKey, signatures[index]);
            const entry = {
                id: declaration.id,
                prefixKey,
                kind: declaration.kind,
                status: expectedStatus
            };
            if (disabled) {
                entries.push(entry);
                continue;
            }
            if (declaration.hit) {
                entry.artifact = { kind: "hit" };
            }
            else if (declaration.inductive) {
                entry.artifact = { kind: "inductive" };
            }
            else if (declaration.kind === "definition") {
                let parsed;
                try {
                    parsed = parseSandboxStoredDeclaration(declaration.source);
                }
                catch {
                    break;
                }
                const body = this.engine.core.state.sysDefs[declaration.name]
                    ?? this.definitionBodies.get(declaration.name);
                const rawCache = this.engine.core.serializeDefinitionCache(declaration.name);
                if (!body
                    || !rawCache
                    || rawCache.kind !== "nbe"
                    || rawCache.metas.length
                    || sandboxAstHasInferenceHole(rawCache.type)
                    || sandboxAstHasInferenceHole(parsed.definitionAst)
                    || sandboxAstHasInferenceHole(parsed.typeAst))
                    break;
                entry.artifact = {
                    kind: "definition",
                    body: Core.clone(body),
                    cache: structuredClone(rawCache)
                };
            }
            else {
                const type = this.axiomTypes.get(declaration.name);
                if (!type)
                    break;
                entry.artifact = { kind: "axiom", type: Core.clone(type) };
            }
            entries.push(entry);
        }
        return {
            version: SANDBOX_VALIDATION_CACHE_VERSION,
            semanticEpoch: SANDBOX_VALIDATION_SEMANTIC_EPOCH,
            preludeKey: this.validationCachePreludeKey,
            entries
        };
    }
    restorePersistedValidationCache(rawCache, orderedDeclarations, layout, options, budget, started) {
        if (!sandboxValidationCacheWithinLimits(rawCache))
            return { status: "discarded", count: 0 };
        const cache = rawCache;
        if (cache.version !== SANDBOX_VALIDATION_CACHE_VERSION
            || cache.semanticEpoch !== SANDBOX_VALIDATION_SEMANTIC_EPOCH
            || cache.preludeKey !== this.validationCachePreludeKey
            || !Array.isArray(cache.entries)
            || cache.entries.length > orderedDeclarations.length
            || cache.entries.length > SANDBOX_VALIDATION_CACHE_MAX_ENTRIES) {
            return { status: "discarded", count: 0 };
        }
        if (!cache.entries.length)
            return { status: "discarded", count: 0 };
        const signatures = this.validationSignatures();
        let prefixKey = this.validationCachePreludeKey;
        for (let index = 0; index < cache.entries.length; index++) {
            const entry = cache.entries[index];
            const declaration = orderedDeclarations[index];
            prefixKey = sandboxValidationPrefixKey(prefixKey, signatures[index]);
            const disabled = !declaration.enabled || !!layout.get(declaration.id)?.disabled;
            if (!entry
                || entry.id !== declaration.id
                || entry.prefixKey !== prefixKey
                || entry.status !== (disabled ? "disabled" : "valid")
                || typeof entry.kind !== "string"
                || (!disabled && (!entry.artifact || typeof entry.artifact !== "object"))) {
                return { status: "discarded", count: 0 };
            }
        }
        const nextEngine = this.createEngine();
        const nextAxiomTypes = new Map();
        const nextBodies = new Map();
        const patches = [];
        const statusByName = new Map();
        try {
            return nextEngine.core.withSilentErrors(() => {
                for (let index = 0; index < cache.entries.length; index++) {
                    if (options.shouldCancel?.())
                        return { status: "cancelled", count: index };
                    if (budget.timeoutMs !== undefined && performance.now() - started >= budget.timeoutMs) {
                        return { status: "budget-exhausted", count: index };
                    }
                    const target = orderedDeclarations[index];
                    const entry = cache.entries[index];
                    const rowDisabled = !target.enabled || !!layout.get(target.id)?.disabled;
                    if (rowDisabled) {
                        patches.push({ target, value: { ...target, status: "disabled", error: undefined } });
                        for (const name of target.generatedNames ?? (target.name ? [target.name] : [])) {
                            statusByName.set(name, "disabled");
                        }
                        continue;
                    }
                    const parsed = parseSandboxStoredDeclaration(target.source);
                    const restored = {
                        ...target,
                        name: parsed.name,
                        typeSource: parsed.typeSource,
                        kind: parsed.hit
                            ? "hit"
                            : parsed.inductive
                                ? "inductive"
                                : parsed.definitionAst
                                    ? "definition"
                                    : declarationKind(parsed.typeAst),
                        status: "unchecked",
                        error: undefined,
                        dependencies: [],
                        inductive: undefined,
                        hit: undefined,
                        generatedNames: undefined
                    };
                    if (restored.kind !== entry.kind)
                        throw new Error("沙盒验证缓存声明种类不匹配");
                    if (parsed.hit) {
                        restored.hit = parsed.hit;
                        restored.generatedNames = sandboxHitGeneratedNames(parsed.hit);
                        restored.dependencies = collectHitDependencies(parsed.hit);
                    }
                    else if (parsed.inductive) {
                        restored.inductive = parsed.inductive;
                        restored.generatedNames = sandboxInductiveGeneratedNames(parsed.inductive);
                        restored.dependencies = collectInductiveDependencies(parsed.inductive);
                    }
                    else if (parsed.definitionAst) {
                        restored.dependencies = [
                            ...collectFreeNames(parsed.definitionAst),
                            ...(parsed.typeAst ? collectFreeNames(parsed.typeAst) : [])
                        ].filter((name, position, names) => names.indexOf(name) === position);
                    }
                    else {
                        restored.dependencies = collectFreeNames(parsed.typeAst);
                    }
                    const ownedNames = restored.generatedNames ?? [restored.name];
                    const conflict = ownedNames.find(name => this.builtinNames.has(name)
                        || nextEngine.core.hasConst(name)
                        || statusByName.has(name));
                    if (conflict)
                        throw new Error(`沙盒声明名称冲突：${conflict}`);
                    for (const dependency of restored.dependencies) {
                        if (dependency === restored.name) {
                            throw new Error(`不支持递归沙盒定义：${restored.name}`);
                        }
                        if (this.builtinNames.has(dependency))
                            continue;
                        if (statusByName.get(dependency) !== "valid") {
                            throw new Error(`依赖声明无效：${dependency}`);
                        }
                    }
                    const artifact = entry.artifact;
                    if (parsed.hit) {
                        if (artifact.kind !== "hit")
                            throw new Error("沙盒 HIT 缓存格式不匹配");
                        const bundle = lowerSandboxHit(parsed.hit);
                        nextEngine.core.registerSystemInductive(bundle);
                        restored.generatedNames = [...bundle.generatedNames];
                    }
                    else if (parsed.inductive) {
                        if (artifact.kind !== "inductive")
                            throw new Error("沙盒归纳缓存格式不匹配");
                        const bundle = lowerSandboxInductive(parsed.inductive);
                        nextEngine.core.registerSystemInductive(bundle);
                        restored.generatedNames = [...bundle.generatedNames];
                    }
                    else if (parsed.definitionAst) {
                        if (artifact.kind !== "definition")
                            throw new Error("沙盒定义缓存格式不匹配");
                        const body = this.restoreCachedDefinition(nextEngine, restored.name, parsed.definitionAst, parsed.typeAst, artifact.body, artifact.cache);
                        nextBodies.set(restored.name, Core.clone(body));
                    }
                    else {
                        if (artifact.kind !== "axiom")
                            throw new Error("沙盒公理缓存格式不匹配");
                        const sourceType = nextEngine.core.checkTypeFormation(parsed.typeAst, []);
                        const cachedType = nextEngine.core.checkTypeFormation(artifact.type, []);
                        const equality = nextEngine.checkAst({
                            type: "===",
                            name: "",
                            nodes: [Core.clone(sourceType), Core.clone(cachedType)]
                        });
                        if (!equality.ok)
                            throw new Error("沙盒公理缓存与声明源不匹配");
                        nextEngine.core.setSystemType(restored.name, Core.clone(sourceType));
                        nextEngine.core.syncSemanticTypes();
                        nextAxiomTypes.set(restored.name, Core.clone(sourceType));
                    }
                    restored.status = "valid";
                    patches.push({ target, value: restored });
                    for (const name of ownedNames)
                        statusByName.set(name, "valid");
                }
                for (const patch of patches)
                    Object.assign(patch.target, patch.value);
                this.engine = nextEngine;
                this.axiomTypes = nextAxiomTypes;
                this.definitionBodies = nextBodies;
                return { status: "restored", count: cache.entries.length };
            });
        }
        catch {
            return { status: "discarded", count: 0 };
        }
    }
    restoreCachedDefinition(engine, name, sourceBody, expectedType, cachedBody, rawCache) {
        if (!rawCache
            || rawCache.kind !== "nbe"
            || rawCache.metas.length
            || sandboxAstHasInferenceHole(rawCache.type)
            || sandboxAstHasInferenceHole(sourceBody)
            || sandboxAstHasInferenceHole(expectedType)) {
            throw new Error("沙盒透明定义缓存不可安全恢复");
        }
        const cache = rawCache;
        let verifiedBody;
        let verifiedType;
        if (expectedType) {
            const assertion = {
                type: ":",
                name: "",
                nodes: [Core.clone(sourceBody), Core.clone(expectedType)]
            };
            verifiedType = engine.core.checkType(assertion, [], false, undefined, false, true, false);
            verifiedBody = assertion.nodes[0];
        }
        else {
            const equality = {
                type: "===",
                name: "",
                nodes: [Core.clone(sourceBody), Core.clone(cachedBody)]
            };
            verifiedType = engine.core.checkType(equality, [], false, undefined, false, true, false);
            verifiedBody = equality.nodes[0];
        }
        engine.core.checkType({
            type: "===",
            name: "",
            nodes: [Core.clone(verifiedType), Core.clone(cache.type)]
        }, [], false, undefined, false, true, false);
        engine.core.setSystemDefinition(name, Core.clone(verifiedBody));
        engine.core.restoreCheckedDefinitionCache(name, cache);
        if (!engine.core.hasDefinitionCache(name)) {
            engine.core.setSystemDefinition(name);
            throw new Error("沙盒透明定义缓存未通过 NbE 编译");
        }
        return Core.clone(verifiedBody);
    }
    replayValidatedPrefix(orderedDeclarations, prefixLength, layout) {
        const previousBodies = this.definitionBodies;
        const previousAxiomTypes = this.axiomTypes;
        const nextAxiomTypes = new Map();
        const nextBodies = new Map();
        const nextEngine = this.createEngine();
        try {
            for (let index = 0; index < prefixLength; index++) {
                const declaration = orderedDeclarations[index];
                const rowState = layout.get(declaration.id);
                if (declaration.status !== "valid" || !declaration.enabled || rowState?.disabled)
                    continue;
                const parsed = parseSandboxStoredDeclaration(declaration.source);
                if (parsed.hit) {
                    nextEngine.core.registerSystemInductive(lowerSandboxHit(parsed.hit));
                    continue;
                }
                if (parsed.inductive) {
                    nextEngine.core.registerSystemInductive(lowerSandboxInductive(parsed.inductive));
                    continue;
                }
                if (parsed.definitionAst) {
                    const body = previousBodies.get(declaration.name);
                    if (!body) {
                        throw new Error(`缺少透明定义缓存：${declaration.name}`);
                    }
                    nextEngine.core.registerSystemDefinition(declaration.name, Core.clone(body));
                    nextBodies.set(declaration.name, Core.clone(body));
                    continue;
                }
                const type = previousAxiomTypes.get(declaration.name)
                    ?? nextEngine.core.checkTypeFormation(parsed.typeAst, []);
                nextEngine.core.setSystemType(declaration.name, Core.clone(type));
                nextEngine.core.syncSemanticTypes();
                nextAxiomTypes.set(declaration.name, Core.clone(type));
            }
        }
        catch (error) {
            throw new Error(`恢复沙盒增量前缀失败：${String(error)}`);
        }
        this.engine = nextEngine;
        this.axiomTypes = nextAxiomTypes;
        this.definitionBodies = nextBodies;
    }
    validationSignatures() {
        this.syncWorkspaceFromState();
        const layout = new Map(this.workspace.layout().map(item => [item.id, item]));
        const declarations = new Map(this.declarations.map(declaration => [declaration.id, declaration]));
        return this.workspace.snapshot()
            .filter((item) => item.kind === "theorem")
            .map(item => {
            const declaration = declarations.get(item.id);
            const rowState = layout.get(item.id);
            return JSON.stringify({
                id: item.id,
                source: declaration?.source ?? item.value,
                enabled: declaration?.enabled !== false,
                disabled: !!rowState?.disabled
            });
        });
    }
    orderedDeclarationIndex(id) {
        this.syncWorkspaceFromState();
        return this.workspace.snapshot()
            .filter((item) => item.kind === "theorem")
            .findIndex(item => item.id === id);
    }
    markWorkspaceChange(before) {
        const after = this.validationSignatures();
        const commonLength = Math.min(before.length, after.length);
        let index = 0;
        while (index < commonLength && before[index] === after[index])
            index++;
        if (index < before.length || index < after.length)
            this.markDirty(index);
    }
    find(id) {
        const declaration = this.declarations.find(item => item.id === id);
        if (!declaration)
            throw new Error(`找不到沙盒声明：${id}`);
        return declaration;
    }
    markDirty(index) {
        this.dirtyFrom = Math.min(this.dirtyFrom, Math.max(0, index));
    }
    markInvalid(declaration, error) {
        declaration.status = "invalid";
        declaration.error = String(error);
    }
    validationBudgetFor(options) {
        return {
            maxDeclarations: normalizeSandboxLimit(options.maxDeclarations ?? this.validationBudget.maxDeclarations),
            maxNodes: normalizeSandboxLimit(options.maxNodes ?? this.validationBudget.maxNodes),
            maxSteps: normalizeSandboxLimit(options.maxSteps ?? this.validationBudget.maxSteps),
            timeoutMs: normalizeSandboxLimit(options.timeoutMs ?? this.validationBudget.timeoutMs)
        };
    }
    validationBudgetFailure(started, budget, declarationCount, estimatedNodes, estimatedSteps) {
        if (budget.maxDeclarations !== undefined && declarationCount > budget.maxDeclarations) {
            return this.validationInterrupted("budget-exhausted", started, 0, 0, `沙盒验证资源上限：声明数量 ${declarationCount} 超过 ${budget.maxDeclarations}`);
        }
        if (budget.maxNodes !== undefined && estimatedNodes > budget.maxNodes) {
            return this.validationInterrupted("budget-exhausted", started, 0, 0, `沙盒验证资源上限：语法节点 ${estimatedNodes} 超过 ${budget.maxNodes}`);
        }
        if (budget.maxSteps !== undefined && estimatedSteps > budget.maxSteps) {
            return this.validationInterrupted("budget-exhausted", started, 0, 0, `沙盒验证资源上限：验证步骤 ${estimatedSteps} 超过 ${budget.maxSteps}`);
        }
        if (budget.timeoutMs !== undefined && budget.timeoutMs <= 0) {
            return this.validationInterrupted("budget-exhausted", started, 0, 0, "沙盒验证资源上限：时间预算已耗尽");
        }
        return undefined;
    }
    validationInterrupted(status, started, checkedDeclarations, replayedDeclarations, error) {
        // A validation run mutates the incremental Core as it walks the
        // suffix.  Leaving that partially-built Core behind would make the
        // next resumed run register the same names twice.  Mark the current
        // prefix dirty so the normal replay path rebuilds a clean suffix on
        // the next request; the last published bridge remains untouched.
        // Rebuild from the clean prelude on resume. The current run may have
        // registered a suffix declaration before cancellation, so merely
        // keeping `dirtyFrom === validatedThrough` would reuse a partially
        // mutated Core and cause duplicate-name failures on the next run.
        this.dirtyFrom = 0;
        this.lastValidationDurationMs = performance.now() - started;
        this.lastValidationStats = {
            checkedDeclarations,
            replayedDeclarations,
            validatedThrough: this.validatedThrough
        };
        return {
            ok: false,
            declarations: this.getDeclarations(),
            error: error ?? (status === "cancelled" ? "沙盒验证已取消" : "沙盒验证资源上限已耗尽"),
            status,
            validationStats: { ...this.lastValidationStats }
        };
    }
}
function declarationKind(type) {
    const rendered = parser.stringify(type).replaceAll(" ", "");
    if (/^U(?:[0-9]+)?$/.test(rendered))
        return "type";
    if (type.type === "=" || type.type === "~=" || type.type === "~")
        return "proposition";
    return "term";
}
function collectFreeNames(ast) {
    const names = new Set();
    const visit = (node, bound) => {
        if (!node)
            return;
        if (node.type === "var") {
            // `_` and `?meta` are elaboration holes, not declarations.  Keep
            // them out of dependency diagnostics so a valid definition can
            // infer them instead of being reported as an unknown sandbox
            // name.
            if (node.name && node.name !== "_" && !node.name.startsWith("?")
                && !bound.has(node.name) && !node.name.startsWith("@")) {
                names.add(node.name);
            }
            return;
        }
        if (node.type === "P" || node.type === "L" || node.type === "W" || node.type === "S") {
            visit(node.nodes?.[0], bound);
            const next = new Set(bound);
            if (node.name)
                next.add(node.name);
            visit(node.nodes?.[1], next);
            return;
        }
        for (const child of node.nodes ?? [])
            visit(child, bound);
    };
    visit(ast, new Set());
    return [...names];
}
//# sourceMappingURL=sandbox.js.map