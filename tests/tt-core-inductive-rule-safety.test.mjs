import assert from "node:assert/strict";

import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import {
    creativeSandboxSystemRuleIds,
    lowerSandboxHit,
    lowerSandboxInductive,
    parseSandboxHit,
    parseSandboxInductive
} from "../js/tt/sandbox.js";

const parser = new ASTParser();
const parse = source => parser.parse(source);
const pattern = (...parts) => parts.map(parse);
const createCore = () => {
    const engine = new TTCoreEngine();
    engine.configure({ unlockedTypes: creativeSandboxSystemRuleIds });
    return engine.core;
};

function simpleBundle(name, computeRules) {
    return {
        type: [name, parse("U")],
        constructors: [
            [`zero${name}`, parse(name)],
            [`succ${name}`, parse(`${name}->${name}`)]
        ],
        eliminator: [`ind_${name}`, parse(`${name}->${name}`)],
        computeRules
    };
}

function assertRejected(bundle, expected, message) {
    const core = createCore();
    const bundleNames = [
        bundle.type[0],
        ...bundle.constructors.map(([name]) => name),
        ...(bundle.eliminator ? [bundle.eliminator[0]] : []),
        ...(bundle.recursor ? [bundle.recursor[0]] : []),
        ...(bundle.auxiliaryTypes ?? []).map(([name]) => name),
        ...(bundle.definitions ?? []).map(([name]) => name)
    ];
    assert.throws(() => core.registerSystemInductive(bundle), expected, message);
    for (const name of bundleNames) {
        assert.equal(core.hasConst(name), false, `${name} leaked from a rejected bundle`);
    }
    for (const head of Object.keys(bundle.computeRules ?? {})) {
        assert.equal(core.state.computeRules[head], undefined,
            `${head} compute rules leaked from a rejected bundle`);
        assert.equal(core.semanticKernel.hasComputeRules(head), false,
            `${head} semantic compute rules leaked from a rejected bundle`);
    }
}

assertRejected(simpleBundle("UnsafeHead", {
    arbitraryHead: [{
        pattern: pattern("arbitraryHead", "zeroUnsafeHead"),
        result: parse("zeroUnsafeHead")
    }]
}), /规则头只能属于本 bundle 的消去器或递归器/);

assertRejected(simpleBundle("MismatchedHead", {
    ind_MismatchedHead: [{
        pattern: pattern("otherHead", "zeroWrongPatternHead"),
        result: parse("zeroWrongPatternHead")
    }]
}), /pattern\[0\] 必须等于规则头/);

assertRejected(simpleBundle("MissingCtor", {
    ind_MissingCtor: [{
        pattern: pattern("ind_MissingCtor", "?value"),
        result: parse("?value")
    }]
}), /最后数据模式必须由当前点构造子形成/);

assertRejected(simpleBundle("OverlappingRules", {
    ind_OverlappingRules: [
        {
            pattern: pattern("ind_OverlappingRules", "?C", "succOverlappingRules ?n"),
            result: parse("?n")
        },
        {
            pattern: pattern("ind_OverlappingRules", "?D", "succOverlappingRules ?m"),
            result: parse("?m")
        }
    ]
}), /构造子 succOverlappingRules 上重叠/);

assertRejected(simpleBundle("EscapingMeta", {
    ind_EscapingMeta: [{
        pattern: pattern("ind_EscapingMeta", "?C", "zeroEscapingMeta"),
        result: parse("?notBoundOnTheLeft")
    }]
}), /右侧引用了左侧未绑定的元变量：\?notBoundOnTheLeft/);

assertRejected(simpleBundle("AnonymousHole", {
    ind_AnonymousHole: [{
        pattern: pattern("ind_AnonymousHole", "zeroAnonymousHole"),
        result: parse("_")
    }]
}), /右侧不能包含未绑定占位符/);

for (const [name, recursiveData] of [
    ["OriginalRecursive", "succOriginalRecursive ?n"],
    ["ReconstructedRecursive", "succReconstructedRecursive (succReconstructedRecursive ?n)"]
]) {
    const constructorName = `succ${name}`;
    assertRejected(simpleBundle(name, {
        [`ind_${name}`]: [{
            pattern: pattern(`ind_${name}`, "?C", "?cz", "?cs", `${constructorName} ?n`),
            result: parse(`ind_${name} ?C ?cz ?cs (${recursiveData})`)
        }]
    }), /明显非递减递归调用/);
}

const aliasRecursive = simpleBundle("AliasRecursive", {
    ind_AliasRecursive: [{
        pattern: pattern(
            "ind_AliasRecursive",
            "?C",
            "?cz",
            "?cs",
            "succAliasRecursive ?n"
        ),
        result: parse(
            "ind_AliasRecursive ?C ?cz ?cs (idAliasRecursive (succAliasRecursive ?n))"
        )
    }]
});
aliasRecursive.definitions = [[
    "idAliasRecursive",
    parse("Lx:AliasRecursive.x")
]];
assertRejected(aliasRecursive, /递归数据不是当前构造项的直接子项/);

// The safety boundary must accept every generated bundle shape currently
// emitted by the sandbox compiler, including full aliases and structural
// recursive calls under a recursive telescope.
const acceptedBundles = [
    lowerSandboxInductive(parseSandboxInductive(
        "inductive NatSafe : U | zeroNatSafe : NatSafe | succNatSafe : NatSafe -> NatSafe"
    )),
    lowerSandboxInductive(parseSandboxInductive(
        "inductive TreeSafe (A : U) : U "
        + "| leafTreeSafe : A -> TreeSafe A "
        + "| nodeTreeSafe : (nat -> TreeSafe A) -> TreeSafe A"
    )),
    lowerSandboxInductive(parseSandboxInductive(
        "inductive DepTreeSafe (A : U) : U "
        + "| depNodeTreeSafe : (A -> DepTreeSafe A) -> DepTreeSafe A"
    )),
    lowerSandboxInductive(parseSandboxInductive(
        "inductive VecSafe (A : U) [n : nat] : U "
        + "| nilVecSafe : VecSafe A 0 "
        + "| consVecSafe : Pn:nat,A -> VecSafe A n -> VecSafe A (succ n)"
    )),
    lowerSandboxHit(parseSandboxHit(
        "hit CircleSafe : U "
        + "| baseCircleSafe : CircleSafe "
        + "| loopCircleSafe : baseCircleSafe = baseCircleSafe"
    )),
    lowerSandboxHit(parseSandboxHit(
        "hit SurfaceSafe : U "
        + "| baseSurfaceSafe : SurfaceSafe "
        + "| leftSurfaceSafe : baseSurfaceSafe = baseSurfaceSafe "
        + "| rightSurfaceSafe : baseSurfaceSafe = baseSurfaceSafe "
        + "| path2 squareSurfaceSafe : leftSurfaceSafe = rightSurfaceSafe"
    ))
];
const dependentTreeBundle = acceptedBundles.find(bundle => bundle.type[0] === "DepTreeSafe");
assert.match(
    parser.stringify(dependentTreeBundle.computeRules.ind_DepTreeSafe[0].result),
    /λx:\?p0/,
    "recursive telescope domains must be instantiated with the LHS uniform parameter capture"
);

const wrongBranch = lowerSandboxInductive(parseSandboxInductive(
    "inductive WrongBranch : U | zeroWrongBranch : WrongBranch "
    + "| succWrongBranch : WrongBranch -> WrongBranch"
));
wrongBranch.computeRules.ind_WrongBranch[1].result = parse("?c0");
assertRejected(wrongBranch, /canonical 分支/,
    "a recursive constructor cannot compute to another constructor's branch");

const wrongMotive = lowerSandboxInductive(parseSandboxInductive(
    "inductive WrongMotive : U | zeroWrongMotive : WrongMotive "
    + "| succWrongMotive : WrongMotive -> WrongMotive"
));
wrongMotive.computeRules.ind_WrongMotive[1].result = parse(
    "?c1 ?a1_0 (ind_WrongMotive ?c0 ?c0 ?c1 ?a1_0)"
);
assertRejected(wrongMotive, /canonical 分支/,
    "a recursive call cannot replace its motive with a branch");

const forgedEliminatorType = lowerSandboxInductive(parseSandboxInductive(
    "inductive ForgedEliminatorType : U "
    + "| zeroForgedEliminatorType : ForgedEliminatorType "
    + "| succForgedEliminatorType : ForgedEliminatorType -> ForgedEliminatorType"
));
let forgedEliminatorResult = forgedEliminatorType.eliminator[1];
while ((forgedEliminatorResult.type === "P" || forgedEliminatorResult.type === "->")
    && forgedEliminatorResult.nodes?.[1]) {
    forgedEliminatorResult = forgedEliminatorResult.nodes[1];
}
Object.assign(forgedEliminatorResult, parse("False"));
assertRejected(forgedEliminatorType, /subject-reduction/,
    "same-arity forged eliminator codomains must be rejected before rule publication");

const wrongParameter = lowerSandboxInductive(parseSandboxInductive(
    "inductive ListSubject (A : U) : U "
    + "| nilListSubject : ListSubject A "
    + "| consListSubject : A -> ListSubject A -> ListSubject A"
));
wrongParameter.computeRules.ind_ListSubject[1].result = parse(
    "?c1 ?a1_0 ?a1_1 (ind_ListSubject ?a1_0 ?C ?c0 ?c1 ?a1_1)"
);
assertRejected(wrongParameter, /canonical 分支/,
    "a recursive call cannot replace a uniform parameter with constructor data");

const wrongChildIndex = lowerSandboxInductive(parseSandboxInductive(
    "inductive VecSubject (A : U) [n : nat] : U "
    + "| nilVecSubject : VecSubject A 0 "
    + "| consVecSubject : Pn:nat,A -> VecSubject A n -> VecSubject A (succ n)"
));
wrongChildIndex.computeRules.ind_VecSubject[1].result = parse(
    "?c1 ?a1_0 ?a1_1 ?a1_2 "
    + "(ind_VecSubject ?p0 ?C ?c0 ?c1 (succ ?a1_0) ?a1_2)"
);
assertRejected(wrongChildIndex, /canonical 分支/,
    "an indexed recursive call must use the recursive child's index");

const wrongFunctionChild = lowerSandboxInductive(parseSandboxInductive(
    "inductive TreeSubject (A : U) : U "
    + "| leafTreeSubject : A -> TreeSubject A "
    + "| nodeTreeSubject : (nat -> TreeSubject A) -> TreeSubject A"
));
wrongFunctionChild.computeRules.ind_TreeSubject[1].result = parse(
    "?c1 ?a1_0 (λx:nat.ind_TreeSubject ?p0 ?C ?c0 ?c1 (?a1_0 0))"
);
assertRejected(wrongFunctionChild, /canonical 分支/,
    "a function-valued recursive argument must recurse at the bound telescope variable");

const wrongHitBranch = lowerSandboxHit(parseSandboxHit(
    "hit HitBranchSubject : U "
    + "| leftHitBranchSubject : HitBranchSubject "
    + "| rightHitBranchSubject : HitBranchSubject "
    + "| loopHitBranchSubject : leftHitBranchSubject = leftHitBranchSubject"
));
wrongHitBranch.computeRules.ind_HitBranchSubject[1].result = parse("?c0");
assertRejected(wrongHitBranch, /canonical 分支/,
    "a HIT point constructor cannot compute to another point branch");

const aliasHead = lowerSandboxInductive(parseSandboxInductive(
    "inductive AliasHeadSubject : U "
    + "| zeroAliasHeadSubject : AliasHeadSubject "
    + "| succAliasHeadSubject : AliasHeadSubject -> AliasHeadSubject"
));
aliasHead.definitions = [[
    "aliasIndAliasHeadSubject",
    parse("ind_AliasHeadSubject")
]];
aliasHead.computeRules.ind_AliasHeadSubject[1].result = parse(
    "?c1 ?a1_0 (aliasIndAliasHeadSubject ?C ?c0 ?c1 ?a1_0)"
);
assertRejected(aliasHead, /canonical 分支|不允许附加未声明的系统定义/,
    "a transparent alias cannot hide a recursive eliminator head");

const downgradedSchema = lowerSandboxInductive(parseSandboxInductive(
    "inductive DowngradedSchema : U "
    + "| zeroDowngradedSchema : DowngradedSchema "
    + "| succDowngradedSchema : DowngradedSchema -> DowngradedSchema"
));
delete downgradedSchema.metadata.ruleSchemaVersion;
downgradedSchema.computeRules.ind_DowngradedSchema[1].result = parse("?c0");
assertRejected(downgradedSchema, /必须使用计算规则 schema v1/,
    "removing the schema marker must not downgrade a current sandbox bundle");

for (const [label, mutate] of [
    ["constructor", bundle => bundle.constructors.push(["escapeClosed", parse("False")])],
    ["auxiliary type", bundle => bundle.auxiliaryTypes.push(["escapeAux", parse("False")])],
    ["definition", bundle => { bundle.definitions = [["escapeDefinition", parse("true")]]; }]
]) {
    const injected = lowerSandboxInductive(parseSandboxInductive(
        `inductive Closed${label.replace(/\s/g, "")} : U `
        + `| baseClosed${label.replace(/\s/g, "")} : Closed${label.replace(/\s/g, "")}`
    ));
    mutate(injected);
    assertRejected(
        injected,
        /列表与 bundle 不一致|不允许附加未声明的系统定义/,
        `schema-v1 must reject an injected ${label}`
    );
}

const incompleteRules = lowerSandboxInductive(parseSandboxInductive(
    "inductive IncompleteRules : U "
    + "| zeroIncompleteRules : IncompleteRules "
    + "| succIncompleteRules : IncompleteRules -> IncompleteRules"
));
incompleteRules.computeRules.ind_IncompleteRules.pop();
assertRejected(incompleteRules, /未完整覆盖全部点构造子/,
    "a canonical rule table must cover every point constructor");

const forgedRecursiveMetadata = lowerSandboxInductive(parseSandboxInductive(
    "inductive MetadataVec (A : U) [n : nat] : U "
    + "| nilMetadataVec : MetadataVec A 0 "
    + "| consMetadataVec : Pn:nat,A -> MetadataVec A n -> MetadataVec A (succ n)"
));
forgedRecursiveMetadata.metadata.constructors[1]
    .recursiveArguments[0].resultIndices[0] = parse("succ n");
assertRejected(forgedRecursiveMetadata, /递归结果索引与 metadata 不一致/,
    "recursive metadata must be derived from the actual constructor argument type");

const publicationCore = createCore();
const publicationBundle = lowerSandboxInductive(parseSandboxInductive(
    "inductive PublicationOrder : U "
    + "| zeroPublicationOrder : PublicationOrder "
    + "| succPublicationOrder : PublicationOrder -> PublicationOrder"
));
const originalCheckTypeFormation = publicationCore.checkTypeFormation.bind(publicationCore);
let observedTypeChecks = 0;
publicationCore.checkTypeFormation = (ast, context) => {
    observedTypeChecks++;
    for (const head of Object.keys(publicationBundle.computeRules)) {
        assert.equal(publicationCore.state.computeRules[head], undefined,
            `${head} must stay unpublished while generated types are checked`);
        assert.equal(publicationCore.semanticKernel.hasComputeRules(head), false);
    }
    return originalCheckTypeFormation(ast, context);
};
publicationCore.registerSystemInductive(publicationBundle);
assert.ok(observedTypeChecks > 0);
for (const head of Object.keys(publicationBundle.computeRules)) {
    assert.equal(publicationCore.semanticKernel.hasComputeRules(head), true,
        `${head} must be published after type validation succeeds`);
}

const unsafeIndexedBase = lowerSandboxInductive(parseSandboxInductive(
    "inductive VecUnsafe (A : U) [n : nat] : U "
    + "| nilVecUnsafe : VecUnsafe A 0 "
    + "| consVecUnsafe : Pn:nat,A -> VecUnsafe A n -> VecUnsafe A (succ n)"
));
for (const [label, unsafeData] of [
    ["index", "?a1_0"],
    ["non-recursive value", "?a1_1"]
]) {
    const unsafeIndexed = structuredClone(unsafeIndexedBase);
    unsafeIndexed.computeRules.ind_VecUnsafe[1].result = parse(
        `ind_VecUnsafe ?p0 ?C ?c0 ?c1 ?a1_0 ${unsafeData}`
    );
    assertRejected(
        unsafeIndexed,
        /递归数据不是当前构造项的直接子项|canonical 分支/,
        `${label} argument must not be accepted as recursive data`
    );
}

for (const bundle of acceptedBundles) {
    const core = createCore();
    assert.doesNotThrow(() => core.registerSystemInductive(bundle), bundle.type[0]);
    for (const head of Object.keys(bundle.computeRules ?? {})) {
        assert.equal(core.semanticKernel.hasComputeRules(head), true,
            `${head} generated compute rules were not installed`);
    }
}

console.log("Core inductive compute-rule safety regression passed");
