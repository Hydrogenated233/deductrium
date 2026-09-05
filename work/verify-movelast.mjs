import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const core = new TTCoreEngine();
core.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 120_000,
    semanticResourceScale: 8,
    disableSimpleFn: false,
    disableSimpleEq: false,
    language: "zh"
});
const options = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};

function register(source) {
    const flat = source.replace(/\s+/g, " ").trim();
    const result = core.registerDefinition(parser.parse(flat));
    console.log(flat.slice(0, flat.indexOf(":=")), result.ok, result.error ?? "", result.durationMs);
    if (!result.ok) throw new Error(result.error);
}

function prove(name, target, commands) {
    const assist = new TTAssistEngine(core);
    let snapshot = assist.start(target, options);
    for (const command of commands) {
        snapshot = assist.apply(command);
        console.log(name, command, snapshot.goals.map(goal => parser.stringify(goal.type)));
    }
    const result = assist.qed();
    register(`${name}:=(${result.proof}):${result.theorem}`);
}

register(`Fin:=ind_nat (λn:nat.U) False (λn:nat.λu:U.u+True)`);
register(`mkeqv:=
λa:U.λb:U.λf:a→b.λg:b→a.λη:Πx:a,x=g(f x).
λh:b→a.λε:Πy:b,y=f(h y).
@pair _ _ (a→b)
  (λf:a→b.(Σg:b→a,Πx:a,x=g(f x))×
    (Σh:b→a,Πy:b,y=f(h y)))
  f
  ((@pair _ _ (b→a) (λg:b→a.Πx:a,x=g(f x)) g η),
   (@pair _ _ (b→a) (λh:b→a.Πy:b,y=f(h y)) h ε))`);
register(`eqvf:=(λa:U.λb:U.λe:eqv a b.pr0 e)
: Πa:U,Πb:U,(eqv a b)→(a→b)`);
register(`eqvl:=(λa:U.λb:U.λe:eqv a b.pr0 (pr0 (prd1 e)))
: Πa:U,Πb:U,(eqv a b)→(b→a)`);
register(`eqvlp:=(λa:U.λb:U.λe:eqv a b.prd1 (pr0 (prd1 e)))
: Πa:U,Πb:U,Πe:eqv a b,Πx:a,
  x=(pr0 (pr0 (prd1 e))) ((pr0 e) x)`);
register(`eqvr:=(λa:U.λb:U.λe:eqv a b.pr0 (pr1 (prd1 e)))
: Πa:U,Πb:U,(eqv a b)→(b→a)`);
register(`eqvrp:=(λa:U.λb:U.λe:eqv a b.prd1 (pr1 (prd1 e)))
: Πa:U,Πb:U,Πe:eqv a b,Πy:b,
  y=(pr0 e) ((pr0 (pr1 (prd1 e))) y)`);
prove("eqvcomp", "Πa:U,Πb:U,Πc:U,Πe:a≃b,Πk:b≃c,a≃c", [
    "intro a", "intro b", "intro c", "intro e", "intro k", "expand eqv", "ex",
    "intro x", "exact eqvf b c k (eqvf a b e x)", "constructor", "ex", "intro z",
    "exact eqvl a b e (eqvl b c k z)", "intro x",
    "apply @compeq _ _ _ (eqvl a b e (eqvf a b e x)) _",
    "exact eqvlp a b e x", "apply @ap _ _ _ _ (eqvl a b e)",
    "exact eqvlp b c k (eqvf a b e x)",
    "ex", "intro z", "exact eqvr a b e (eqvr b c k z)", "intro z",
    "apply @compeq _ _ _ (eqvf b c k (eqvr b c k z)) _",
    "exact eqvrp b c k z", "apply @ap _ _ _ _ (eqvf b c k)",
    "exact eqvrp a b e (eqvr b c k z)"
]);

prove("sumcongr",
    "Πa:U,Πb:U,Πc:U,Πd:U,Πe:a≃b,Πk:c≃d,(a+c)≃(b+d)", [
    "intro a", "intro b", "intro c", "intro d", "intro e", "intro k",
    "expand eqv", "ex", "intro z", "destruct z", "left", "exact (pr0 e) zl",
    "right", "exact (pr0 k) zr", "constructor", "ex", "intro z", "destruct z",
    "left", "exact (pr0 (pr0 (prd1 e))) zl", "right", "exact (pr0 (pr0 (prd1 k))) zr", "intro z",
    "destruct z", "apply ap inl", "exact (prd1 (pr0 (prd1 e))) zl", "apply ap inr",
    "exact (prd1 (pr0 (prd1 k))) zr", "ex", "intro z", "destruct z", "left",
    "exact (pr0 (pr1 (prd1 e))) zl", "right", "exact (pr0 (pr1 (prd1 k))) zr", "intro z",
    "destruct z", "apply ap inl", "exact (prd1 (pr1 (prd1 e))) zl", "apply ap inr",
    "exact (prd1 (pr1 (prd1 k))) zr"
]);

if (false) prove("prodcongr", "Πa:U,Πb:U,Πc:U,Πd:U,Πe:a≃b,Πk:c≃d,(a×c)≃(b×d)", [
    "intro a", "intro b", "intro c", "intro d", "intro e", "intro k",
    "expand eqv", "ex", "intro z", "destruct z", "case",
    "exact (pr0 e) z0", "exact (pr0 k) z1", "constructor", "ex",
    "intro z", "destruct z", "case", "exact (pr0 (pr0 (prd1 e))) z0", "exact (pr0 (pr0 (prd1 k))) z1",
    "intro z", "destruct z", "apply sigmapath a (λ_:a.c)",
    "exact (prd1 (pr0 (prd1 e))) z0",
    "exact (transconst ((prd1 (pr0 (prd1 e))) z0) z1)▪((prd1 (pr0 (prd1 k))) z1)",
    "ex", "intro z", "destruct z", "case", "exact (pr0 (pr1 (prd1 e))) z0",
    "exact (pr0 (pr1 (prd1 k))) z1", "intro z", "destruct z",
    "apply sigmapath b (λ_:b.d)", "exact (prd1 (pr1 (prd1 e))) z0",
    "exact (transconst ((prd1 (pr1 (prd1 e))) z0) z1)▪((prd1 (pr1 (prd1 k))) z1)"
]);

register(`swap2fn:=λa:U.λz:(a+True)+True.
  ind_Sum (λ_:((a+True)+True).((a+True)+True))
    (λu:a+True.
      ind_Sum (λ_:a+True.((a+True)+True))
        (λx:a.inl (inl x))
        (λt:True.inr true) u)
    (λt:True.inl (inr true)) z`);
prove("swap2self", "Πa:U,Πz:(a+True)+True,z=swap2fn a (swap2fn a z)", [
    "intro a", "intro z", "destruct z", "destruct zl", "rfl", "destruct zlr",
    "rfl", "destruct zr", "rfl"
]);
prove("swap2eqv", "Πa:U,((a+True)+True)≃((a+True)+True)", [
    "intro a", "expand eqv", "ex", "exact swap2fn a", "constructor", "ex",
    "exact swap2fn a", "intro z", "exact swap2self a z", "ex", "exact swap2fn a",
    "intro z", "exact swap2self a z"
]);

if (false) register(`movelast:=
ind_nat
  (λn:nat.Πy:Fin(succ n),eqv (Fin(succ n)) (Fin(succ n)))
  (λy:Fin(succ 0).eqvrefl (Fin(succ 0)))
  (λm:nat.
    λih:Πy:Fin(succ m),eqv (Fin(succ m)) (Fin(succ m)).
    λy:Fin(succ(succ m)).
    ind_Sum
      (λ_:Fin(succ(succ m)),eqv (Fin(succ(succ m))) (Fin(succ(succ m))))
      (λu:Fin(succ m).
        eqvcomp (Fin(succ(succ m))) (Fin(succ(succ m))) (Fin(succ(succ m)))
          (sumcongr (Fin(succ m)) (Fin(succ m)) True True
            (ih u) (eqvrefl True))
          (swap2eqv (Fin m)))
      (λt:True.eqvrefl (Fin(succ(succ m))))
      y)`);

if (false) {
const pointAssist = new TTAssistEngine(core);
let point = pointAssist.start(
    "Πn:nat,Πy:Fin(succ n),eqvf (Fin(succ n)) (Fin(succ n)) (movelast n y) y=inr true",
    options
);
for (const command of ["intro n", "induction n with m ih", "intro y", "destruct y"]) {
    point = pointAssist.apply(command);
    console.log("movelastpoint", command, point.goals.map(goal => ({
        context: goal.context.map(([name, type]) => `${name}:${parser.stringify(type)}`),
        target: parser.stringify(goal.type)
    })));
}
}
