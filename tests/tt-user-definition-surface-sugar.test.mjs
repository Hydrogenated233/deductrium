import assert from "node:assert/strict";

import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 30_000,
    language: "zh"
});

function define(source) {
    const ast = parser.parse(source);
    const result = engine.registerDefinition(ast);
    assert.equal(result.ok, true, result.error ?? source);
    // Mirror TTGui's storage path: keep the rendered declaration separately,
    // while the executable user definition receives the checked core syntax.
    const filled = result.filledDefinition;
    const body = ast.nodes[1].type === ":" ? filled.nodes[0] : filled;
    engine.core.setUserDefinition(
        ast.nodes[0].name,
        engine.core.desugar(body, true),
        true
    );
}

define("pairNat:=(0,0):(Σx:nat,nat)");
define("proj:=pr0 pairNat");
assert.equal(
    engine.check("proj === 0").ok,
    true,
    "NbE must execute a checked tuple definition with inferred family holes"
);

// A representative non-built-in natural-number division definition uses a
// dependent pair as its recursion state. Its computation relies on reducing
// the surface `(0,0)` state through `pr0`.
define(
    "eqNat:=ind_nat (Lx:nat.nat->Bool) "
    + "(ind_nat (Lz:nat.Bool) 1b (Lz:nat.L_:Bool.0b)) "
    + "(Lx:nat.Lf:nat->Bool.ind_nat (Lz:nat.Bool) 0b "
    + "(Lz:nat.L_:Bool.f z))"
);
define(
    "divStep:=Lb:nat.Ls:Σx:nat,nat.ind_Bool "
    + "(L_:Bool.Σx:nat,nat) (pr0 s,succ (pr1 s)) "
    + "(succ (pr0 s),0) (eqNat (succ (pr1 s)) (succ b))"
);
define(
    "divState:=La:nat.Lb:nat.ind_nat (L_:nat.Σx:nat,nat) (0,0) "
    + "(Lk:nat.Ls:Σx:nat,nat.divStep b s) a"
);
define(
    "div:=La:nat.Lb:nat.pr0 "
    + "(divState a b)"
);

const calculation = engine.check("div 10 1 === 5");
assert.equal(calculation.ok, true, calculation.error ?? "div 10 1 === 5");
assert.equal(engine.check("div 10 0 === 10").ok, true);

// The state theorem's projection must agree with the division definition.
// This is the proof-assistant path used by custom (non-built-in) division:
// `div` is the first projection and the zero-divisor state is `(x, 0)`.
engine.core.setSystemType(
    "divState_zero",
    engine.core.desugar(parser.parse("Πx:nat,(divState x 0)=(x,0)"), true)
);
const assist = new TTAssistEngine(engine);
const assistOptions = {
    disableMultipleApply: true,
    disableDestructConds: true,
    disableDestructEq: true
};
assist.start("Πx:nat,div x 0=x", assistOptions);
assist.apply("intro x");
assist.apply("exact ap pr0 (divState_zero x)");
assert.equal(assist.qed().theorem, "(Πx:nat,((div x 0)=x))");

// The opposite projection proves a different proposition and must not be
// accepted merely because the source theorem has the right Sigma shape.
const wrongProjection = new TTAssistEngine(engine);
wrongProjection.start("Πx:nat,div x 0=x", assistOptions);
wrongProjection.apply("intro x");
assert.throws(
    () => wrongProjection.apply("exact ap pr1 (divState_zero x)"),
    /类型断言失败|无法对类型|类型推断暂不支持/
);

console.log("user-definition surface-sugar NbE regression passed");
