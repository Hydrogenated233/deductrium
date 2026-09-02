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
        ...(bundle.auxiliaryTypes ?? []).map(([name]) => name)
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
        /递归数据不是当前构造项的直接子项/,
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
