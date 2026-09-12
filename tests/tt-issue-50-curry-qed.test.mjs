import assert from "node:assert/strict";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { ASTParser } from "../js/tt/astparser.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const config = {
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_", timeout: 30_000, language: "zh"
};
const options = {
    disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false
};
// Only the prerequisite from the reported save is needed to reproduce #50.
const lemma = "ttEqvOfIso:=(λa:U.(λb:U.(λf:(a→b).(λg:(b→a).(λh:(Πx:a,(x=(g (f x)))).(λk:(Πy:b,(y=(f (g y)))).pair (λf:(a→b).((Σg:(b→a),(Πx:a,(x=(g (f x)))))×(Σh:(b→a),(Πx:b,(x=(f (h x))))))) f (pair (λ_:(Σg:(b→a),(Πx:a,(x=(g (f x))))).(Σh:(b→a),(Πx:b,(x=(f (h x)))))) (pair (λg:(b→a).(Πx:a,(x=(g (f x))))) g h) (pair (λh:(b→a).(Πx:b,(x=(f (h x))))) g k)))))))):(Πa:U,(Πb:U,(Πf:(a→b),(Πg:(b→a),((Πx:a,(x=(g (f x))))→((Πy:b,(y=(f (g y))))→(eqv a b)))))))";
const target = "Πa:U,Πb:U,Πc:U,eqv (a×b→c) (a→b→c)";
const commands = [
    "intros a b c",
    "apply ttEqvOfIso (a×b→c) (a→b→c) (λf:a×b→c.λx:a.λy:b.f (x,y)) (λg:a→b→c.λp:a×b.ind_Prod (λx:a.b) (λp:a×b.c) (λx:a.λy:b.g x y) p)",
    "intro f", "fnext", "intro p", "cases p", "rfl",
    "intro g", "fnext", "intro x", "fnext", "intro y", "rfl"
];

function registerLemma(coreEngine) {
    const result = coreEngine.registerDefinition(parser.parseSurface(lemma));
    assert.equal(result.ok, true, result.error);
    assert.equal(result.inferenceComplete, true);
}

function checkExport(coreEngine, result) {
    const assertion = `${result.proof}:${result.theorem}`;
    const checked = coreEngine.checkAst(parser.parseSurface(assertion));
    assert.equal(checked.ok, true, checked.error);
    assert.equal(checked.inferenceComplete, true);
}

const engine = new TTAssistEngine();
engine.configure(config);
registerLemma(engine.engine);
engine.start(target, options);
let completed;
engine.engine.core.withSilentErrors(() => {
    for (const command of commands) completed = engine.apply(command);
});
assert.equal(commands.length, 13);
assert.equal(completed.goals.length, 0);
assert.deepEqual(completed.history, commands);
const result = engine.qed();
assert.equal(result.theorem, parser.stringify(parser.parseSurface(target)));
assert.match(result.proof, /@fnext/u, "qed must retain fnext's explicit family parameters");
assert.deepEqual(engine.qed(), result, "qed must leave the live proof unchanged");
assert.deepEqual(engine.snapshot(), completed);

const independent = new TTCoreEngine();
independent.configure(config);
registerLemma(independent);
checkExport(independent, result);
const saved = independent.registerDefinition(
    parser.parseSurface(`ttCurryEqv := ${result.proof}:${result.theorem}`));
assert.equal(saved.ok, true, saved.error);
assert.equal(saved.inferenceComplete, true);

engine.engine.core.withSilentErrors(() => {
    assert.equal(engine.undo().goals.length, 1);
    engine.apply("rfl");
    assert.deepEqual(engine.qed(), result);
    assert.deepEqual(engine.start(target, options, commands).history, commands);
});
checkExport(independent, engine.qed());

// A bare `fnext (lambda x. rfl)` also fails without the surrounding Curry
// proof. Cover constant, dependent and universe-polymorphic families.
for (const [proposition, intro] of [
    ["Πf:(nat→nat),f=f", "intro f"],
    ["Πa:U,Πb:a→U,Πf:(Πx:a,b x),f=f", "intros a b f"],
    ["Πx:U,Πb:x→U,Πf:(Πx:x,b x),f=f", "intros x b f"],
    ["Πu:U@,Πv:U@,Πa:Uu,Πb:a→Uv,Πf:(Πx:a,b x),f=f", "intros u v a b f"]
]) {
    const proofEngine = new TTAssistEngine();
    proofEngine.configure(config);
    proofEngine.start(proposition, options);
    let done;
    proofEngine.engine.core.withSilentErrors(() => {
        for (const command of [intro, "fnext", "intro x", "rfl"]) {
            done = proofEngine.apply(command);
        }
    });
    assert.equal(done.goals.length, 0);
    const exported = proofEngine.qed();
    const fresh = new TTCoreEngine();
    fresh.configure(config);
    checkExport(fresh, exported);
    assert.deepEqual(proofEngine.snapshot(), done);
}

// Explicit parameters supply inference information, not proof evidence.
// Deliberately corrupt a completed term and check qed still rejects it
// without mutating the live term/history or accepting goals=0 as sufficient.
const invalid = new TTAssistEngine();
invalid.configure(config);
invalid.start("Πf:(nat→nat),f=f", options);
invalid.engine.core.withSilentErrors(() => {
    for (const command of ["intro f", "fnext", "intro x", "rfl"]) invalid.apply(command);
});
const validTerm = invalid.assist.elem;
invalid.assist.elem = parser.parseSurface("λf:nat→nat.true");
const beforeFailure = invalid.snapshot();
invalid.engine.core.withSilentErrors(() => assert.throws(() => invalid.qed()));
assert.deepEqual(invalid.snapshot(), beforeFailure);
invalid.assist.elem = validTerm;
checkExport(independent, invalid.qed());
console.log("GitHub issue #50 Curry equivalence qed regression passed");
