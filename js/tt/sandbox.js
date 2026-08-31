import { ASTParser } from "./astparser.js";
import { Core } from "./core.js";
import { TTCoreEngine } from "./engine.js";
import { initTypeSystem } from "./initial.js";
import { TheoremWorkspace } from "./theorem-workspace.js";
const parser = new ASTParser();
export const SANDBOX_SAVE_VERSION = 1;
/** The sandbox is an authoring tool and is intentionally unavailable in survival. */
export function sandboxEnabledInMode(mode) {
    return mode === "creative";
}
const defaultSandboxSystemRuleIds = Object.freeze([...new Set(initTypeSystem().map(rule => rule.id))]);
/**
 * The complete system prelude used by a creative-mode type layer.  The UI
 * normally passes its current unlocked set explicitly; this export is useful
 * for non-DOM callers that want the same prelude without importing `initial`.
 */
export const creativeSandboxSystemRuleIds = defaultSandboxSystemRuleIds;
const isolatedSandboxSystemRuleIds = Object.freeze([
    "True", "False", "eq", "eq.="
]);
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
export function parseSandboxInductive(source) {
    const text = normalizeSandboxSource(source);
    const [rawHeader, ...rawConstructors] = splitInductiveSections(text);
    const header = new RegExp(String.raw `^inductive\s+(${sandboxNamePattern})([\s\S]*)$`, "i")
        .exec(rawHeader);
    if (!header) {
        throw new Error("普通归纳类型声明必须使用 inductive 名称 [(参数 : 类型)] : Universe 格式");
    }
    const name = header[1];
    let remainder = header[2].trim();
    const parameters = [];
    const indices = [];
    const parameterNames = new Set();
    while (remainder.startsWith("(")) {
        const end = findMatchingDelimiter(remainder, 0, "(", ")");
        if (end < 0)
            throw new Error(`归纳类型 ${name} 的参数括号未闭合`);
        const parameter = parseInductiveBinder(remainder.slice(1, end), `归纳类型 ${name}`);
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
        const indexBinder = parseInductiveBinder(remainder.slice(1, end), `归纳类型 ${name}`, "索引");
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
        universe = parser.parse(universeSource);
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
    for (const [constructorIndex, raw] of rawConstructors
        .map(part => part.trim())
        .filter(Boolean)
        .entries()) {
        const match = new RegExp(String.raw `^(${sandboxNamePattern})\s*(?::\s*([\s\S]*))?$`).exec(raw);
        if (!match)
            throw new Error(`归纳构造子格式错误：${raw}`);
        const constructorName = match[1];
        const explicitType = match[2]?.trim();
        if (!explicitType && indices.length) {
            throw new Error(`索引归纳构造子 ${constructorName} 必须显式写出返回索引`);
        }
        const typeSource = explicitType || parser.stringify(familyApplication);
        let type;
        try {
            type = parser.parse(typeSource);
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
                methodArgs.push(sandboxRecursiveCall(publicInductionHead, argumentVars[index], recursive, (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex => renameFreeInductiveNames(resultIndex, patternReplacements))));
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
                fullMethodArgs.push(sandboxRecursiveCall(fullInductionHead, argumentVars[index], recursive, (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex => renameFreeInductiveNames(resultIndex, patternReplacements))));
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
                publicRecursorArgs.push(sandboxRecursiveCall(publicRecursorHead, argumentVars[index], recursive, (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex => renameFreeInductiveNames(resultIndex, patternReplacements))));
                fullRecursorArgs.push(sandboxRecursiveCall(fullRecursorHead, argumentVars[index], recursive, (ctor.argumentAsts[index].recursiveResultIndices ?? []).map(resultIndex => renameFreeInductiveNames(resultIndex, patternReplacements))));
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
export function parseSandboxDeclaration(source) {
    const text = normalizeSandboxSource(source);
    if (!text)
        throw new Error("声明不能为空");
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
    const ast = parser.parse(text);
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
export function createSandboxDeclaration(source, id) {
    const text = normalizeSandboxSource(source);
    try {
        const parsed = parseSandboxDeclaration(text);
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
/**
 * Stage-1 sandbox model. It deliberately owns a fresh TTCoreEngine and never
 * writes to TTGui, GameSaveLoad, unlock state, theorem rows, or map state.
 */
export class SandboxEnvironment {
    builtinNames = new Set();
    systemRuleIds;
    engine;
    /** Fully elaborated body-less declaration types used by the bridge. */
    axiomTypes = new Map();
    /** Checked source bodies used for the read-only creative bridge. */
    definitionBodies = new Map();
    nextId = 1;
    nextFolderId = 1;
    dirtyFrom = 0;
    validatedThrough = 0;
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
        engine.configure({
            unlockedTypes: [...this.systemRuleIds],
            inferDisplayMode: "_",
            semanticResourceScale: 1
        });
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
    validate() {
        const started = performance.now();
        this.syncWorkspaceFromState();
        const workspaceItems = this.workspace.snapshot();
        const layout = new Map(this.workspace.layout().map(item => [item.id, item]));
        const orderedDeclarations = workspaceItems
            .filter((item) => item.kind === "theorem")
            .map(item => this.declarations.find(declaration => declaration.id === item.id))
            .filter((declaration) => !!declaration);
        let replayedDeclarations = 0;
        if (this.dirtyFrom < this.validatedThrough || this.validatedThrough > orderedDeclarations.length) {
            const prefixLength = Math.min(this.dirtyFrom, this.validatedThrough, orderedDeclarations.length);
            this.replayValidatedPrefix(orderedDeclarations, prefixLength, layout);
            this.validatedThrough = prefixLength;
            replayedDeclarations = prefixLength;
        }
        const allNames = new Set();
        const declarationByName = new Map();
        for (const candidate of this.declarations) {
            try {
                const parsed = parseSandboxDeclaration(candidate.source);
                if (parsed.inductive) {
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
                parsed = parseSandboxDeclaration(declaration.source);
                declaration.name = parsed.name;
                declaration.typeSource = parsed.typeSource;
                if (parsed.inductive) {
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
                if (parsed.inductive) {
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
        this.validatedThrough = orderedDeclarations.length;
        this.dirtyFrom = this.validatedThrough;
        this.lastValidationDurationMs = performance.now() - started;
        this.lastValidationStats = {
            checkedDeclarations,
            replayedDeclarations,
            validatedThrough: this.validatedThrough
        };
        return {
            ok: !this.declarations.some(declaration => declaration.status === "invalid"),
            declarations: this.getDeclarations(),
            error: firstError,
            bridge: this.bridge(),
            validationStats: { ...this.lastValidationStats }
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
            if (declaration.inductive) {
                try {
                    inductives.push(lowerSandboxInductive(declaration.inductive));
                    order.push({ kind: "inductive", name: declaration.name });
                }
                catch { }
                continue;
            }
            try {
                const parsed = parseSandboxDeclaration(declaration.source);
                if (parsed.definitionAst) {
                    const body = this.definitionBodies.get(declaration.name) ?? parsed.definitionAst;
                    definitions.push([declaration.name, Core.clone(body)]);
                    order.push({ kind: "definition", name: declaration.name });
                }
                else if (!parsed.inductive && parsed.typeAst) {
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
        const result = this.engine.check(source);
        return { ...result, source };
    }
    getDeclarations() {
        return this.declarations.map(declaration => ({ ...declaration, dependencies: [...declaration.dependencies] }));
    }
    toJSON() {
        this.syncWorkspaceFromState();
        const snapshot = this.workspace.snapshot();
        return {
            version: SANDBOX_SAVE_VERSION,
            declarations: this.getDeclarations(),
            folders: snapshot
                .filter((item) => item.kind === "folder")
                .map(folder => ({ ...folder })),
            order: snapshot.map(item => item.id)
        };
    }
    serialize() {
        return JSON.stringify(this.toJSON());
    }
    load(value) {
        const save = typeof value === "string" ? JSON.parse(value) : value;
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
        this.markDirty(commonPrefix);
        return this.validate();
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
                const parsed = parseSandboxDeclaration(declaration.source);
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