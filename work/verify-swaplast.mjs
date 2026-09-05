import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 120_000,
    semanticResourceScale: 8,
    disableSimpleFn: false,
    disableSimpleEq: false
});

const definitions = [
`Fin:=ind_nat (λn:nat.U) False (λn:nat.λu:U.u+True)`,
`swap2fn:=λa:U.λz:(a+True)+True.
  ind_Sum (λ_:((a+True)+True).((a+True)+True))
    (λu:a+True.
      ind_Sum (λ_:a+True.((a+True)+True))
        (λx:a.inl (inl x))
        (λt:True.inr true) u)
    (λt:True.inl (inr true)) z`,
`liftlastfn:=λa:U.λf:a→a.λz:a+True.
  ind_Sum (λ_:a+True.a+True)
    (λx:a.inl (f x))
    (λt:True.inr t) z
: Πa:U,Πf:a→a,(a+True)→(a+True)`
];

for (const definition of definitions) {
    const source = definition.replace(/\s+/g, " ").trim();
    const result = engine.registerDefinition(parser.parse(source));
    console.log(source.slice(0, source.indexOf(":=")), result.ok, result.error ?? "", result.durationMs);
    if (!result.ok) process.exit(1);
}

const assist = new TTAssistEngine(engine);
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
let snapshot = assist.start("Πn:nat,(Fin n+True)→(Fin n+True)→(Fin n+True)", options);
for (const command of [
    "intro n", "induction n with m ih", "intro y", "intro z", "exact z",
    "intro y", "destruct y", "intro z",
    "exact liftlastfn (Fin(succ m)) (ih yl) (swap2fn (Fin m) (liftlastfn (Fin(succ m)) (ih yl) z))",
    "intro z", "exact z"
]) {
    snapshot = assist.apply(command);
    console.log(command, snapshot.goals.map(goal => ({
        context: goal.context.map(([name, type]) => `${name}:${parser.stringify(type)}`),
        target: parser.stringify(goal.type)
    })));
}
const result = assist.qed();
console.log(result.proof);
const registered = engine.registerDefinition(parser.parse(`swaplastfn:=(${result.proof}):${result.theorem}`));
console.log("swaplastfn", registered.ok, registered.error ?? "", registered.durationMs);
