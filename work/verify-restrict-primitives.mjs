import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreEngine } from "../js/tt/engine.js";
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
`sumcode:=λa:U.λb:U.λx:a+b.
  ind_Sum (λ_:a+b.(a+b)→U)
    (λu:a.λy:a+b.
      ind_Sum (λ_:a+b.U) (λv:a.u=v) (λv:b.False) y)
    (λu:b.λy:a+b.
      ind_Sum (λ_:a+b.U) (λv:a.False) (λv:b.u=v) y) x
: Πa:U,Πb:U,Πx:a+b,Πy:a+b,U`,
`sumcoderfl:=λa:U.λb:U.λx:a+b.
  ind_Sum (λz:a+b.sumcode a b z z) (λu:a.rfl) (λv:b.rfl) x
: Πa:U,Πb:U,Πx:a+b,sumcode a b x x`,
`sumencode:=λa:U.λb:U.λx:a+b.λy:a+b.λp:x=y.
  ind_eq x (λy:a+b.λp:x=y.sumcode a b x y)
    (sumcoderfl a b x) y p
: Πa:U,Πb:U,Πx:a+b,Πy:a+b,(x=y)→sumcode a b x y`,
`notinlr:=
λa:U.λx:a.λp:inl x=inr true.
  ind_False (λ_:False.False)
    (sumencode a True (inl x) (inr true) p)
: Πa:U,Πx:a,not (inl x=inr true)`,
`droplast:=
λa:U.λz:a+True.
  ind_Sum
    (λz:a+True,not (z=inr true)→a)
    (λx:a.λp:not (inl x=inr true).x)
    (λt:True.λp:not (inr t=inr true).
      ind_False (λ_:False.a)
        (p (ind_True (λt:True,inr t=inr true) rfl t)))
    z
: Πa:U,Πz:a+True,not (z=inr true)→a`,
`droplast_round:=
λa:U.λz:a+True.
  ind_Sum
    (λz:a+True,Πp:not (z=inr true),inl (droplast a z p)=z)
    (λx:a.λp:not (inl x=inr true).rfl)
    (λt:True.λp:not (inr t=inr true).
      ind_False
        (λ_:False,inl (droplast a (inr t) p)=inr t)
        (p (ind_True (λt:True,inr t=inr true) rfl t)))
    z
: Πa:U,Πz:a+True,Πp:not (z=inr true),inl (droplast a z p)=z`,
`droplast_inl:=
λa:U.λx:a.λp:not (inl x=inr true).rfl
: Πa:U,Πx:a,Πp:not (inl x=inr true),droplast a (inl x) p=x`,
`inlinj:=
λa:U.λx:a.λy:a.λp:inl x=inl y.
  sumencode a True (inl x) (inl y) p
: Πa:U,Πx:a,Πy:a,(inl x=inl y)→x=y`,
`eqvf:=(λa:U.λb:U.λe:eqv a b.pr0 e)
: Πa:U,Πb:U,(eqv a b)→(a→b)`,
`eqvl:=(λa:U.λb:U.λe:eqv a b.pr0 (pr0 (prd1 e)))
: Πa:U,Πb:U,(eqv a b)→(b→a)`,
`eqvlp:=(λa:U.λb:U.λe:eqv a b.prd1 (pr0 (prd1 e)))
: Πa:U,Πb:U,Πe:eqv a b,Πx:a,
  x=(pr0 (pr0 (prd1 e))) ((pr0 e) x)`,
`eqvr:=(λa:U.λb:U.λe:eqv a b.pr0 (pr1 (prd1 e)))
: Πa:U,Πb:U,(eqv a b)→(b→a)`,
`eqvrp:=(λa:U.λb:U.λe:eqv a b.prd1 (pr1 (prd1 e)))
: Πa:U,Πb:U,Πe:eqv a b,Πy:b,
  y=(pr0 e) ((pr0 (pr1 (prd1 e))) y)`,
`invagree:=
λa:U.λb:U.λe:eqv a b.λy:b.
  (ap (eqvl a b e) (eqvrp a b e y))▪
  (inveq (eqvlp a b e (eqvr a b e y)))
: Πa:U,Πb:U,Πe:eqv a b,Πy:b,eqvl a b e y=eqvr a b e y`,
`eqvlright:=
λa:U.λb:U.λe:eqv a b.λy:b.
  (eqvrp a b e y)▪
  (ap (eqvf a b e) (inveq (invagree a b e y)))
: Πa:U,Πb:U,Πe:eqv a b,Πy:b,y=eqvf a b e (eqvl a b e y)`
];

for (const definition of definitions) {
    const source = definition.replace(/\s+/g, " ").trim();
    const name = source.slice(0, source.indexOf(":="));
    const result = engine.registerDefinition(parser.parse(source));
    console.log(name, result.ok, result.error ?? "", result.durationMs);
    if (!result.ok) process.exit(1);
}
