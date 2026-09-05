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
`mkeqv:=
λa:U.λb:U.λf:a→b.λg:b→a.λη:Πx:a,x=g(f x).
λh:b→a.λε:Πy:b,y=f(h y).
@pair _ _ (a→b)
  (λf:a→b.(Σg:b→a,Πx:a,x=g(f x))×
    (Σh:b→a,Πy:b,y=f(h y)))
  f
  ((@pair _ _ (b→a) (λg:b→a.Πx:a,x=g(f x)) g η),
   (@pair _ _ (b→a) (λh:b→a.Πy:b,y=f(h y)) h ε))`,
`sigmapath:=
λa:U.λb:a→U.λx:Σz:a,b z.
ind_Prod b
  (λx:Σz:a,b z.Πy:Σz:a,b z.Πp:pr0 x=pr0 y.
    Πq:trans b p (prd1 x)=prd1 y.x=y)
  (λx0:a.λx1:b x0.λy:Σz:a,b z.
    ind_Prod b
      (λy:Σz:a,b z.Πp:x0=pr0 y.Πq:trans b p x1=prd1 y.
        @pair _ _ a b x0 x1=y)
      (λy0:a.λy1:b y0.λp:x0=y0.
        ind_eq x0
          (λy0:a.λp:x0=y0.Πy1:b y0.Πq:trans b p x1=y1.
            @pair _ _ a b x0 x1=@pair _ _ a b y0 y1)
          (λy1:b x0.λq:trans b rfl x1=y1.
            ind_eq x1
              (λy1:b x0.λq:x1=y1.
                @pair _ _ a b x0 x1=@pair _ _ a b x0 y1)
              rfl y1 q)
          y0 p y1)
      y)
  x`,
`piprop:=
λa:U.λb:a→U.λhb:Πx:a,isProp (b x).
λf:Πx:a,b x.λg:Πx:a,b x.
fnext (λx:a.hb x (f x) (g x))
: Πa:U,Πb:a→U,(Πx:a,isProp (b x))→isProp (Πx:a,b x)`,
`leftinvprop:=
λa:U.λb:U.λsa:isSet a.λf:a→b.λh:b→a.
λε:Πy:b,y=f(h y).
λl1:Σg:b→a,Πx:a,x=g(f x).
λl2:Σg:b→a,Πx:a,x=g(f x).
sigmapath (b→a) (λg:b→a.Πx:a,x=g(f x)) l1 l2
  (fnext (λy:b.
    (((ap (pr0 l1) (ε y))▪(inveq (prd1 l1 (h y))))▪
      (prd1 l2 (h y)))▪(inveq (ap (pr0 l2) (ε y)))))
  (piprop a (λx:a.x=(pr0 l2)(f x))
    (λx:a.sa x ((pr0 l2)(f x)))
    (trans (λg:b→a.Πx:a,x=g(f x))
      (fnext (λy:b.
        (((ap (pr0 l1) (ε y))▪(inveq (prd1 l1 (h y))))▪
          (prd1 l2 (h y)))▪(inveq (ap (pr0 l2) (ε y)))))
      (prd1 l1))
    (prd1 l2))
: Πa:U,Πb:U,isSet a→Πf:a→b,Πh:b→a,
  (Πy:b,y=f(h y))→isProp (Σg:b→a,Πx:a,x=g(f x))`,
`rightinvprop:=
λa:U.λb:U.λsb:isSet b.λf:a→b.λg:b→a.
λp:Πx:a,x=g(f x).
λr1:Σh:b→a,Πy:b,y=f(h y).
λr2:Σh:b→a,Πy:b,y=f(h y).
sigmapath (b→a) (λh:b→a.Πy:b,y=f(h y)) r1 r2
  (fnext (λy:b.
    (((p ((pr0 r1) y))▪(ap g (inveq (prd1 r1 y))))▪
      (ap g (prd1 r2 y)))▪(inveq (p ((pr0 r2) y)))))
  (piprop b (λy:b.y=f((pr0 r2)y))
    (λy:b.sb y (f((pr0 r2)y)))
    (trans (λh:b→a.Πy:b,y=f(h y))
      (fnext (λy:b.
        (((p ((pr0 r1) y))▪(ap g (inveq (prd1 r1 y))))▪
          (ap g (prd1 r2 y)))▪(inveq (p ((pr0 r2) y)))))
      (prd1 r1))
    (prd1 r2))
: Πa:U,Πb:U,isSet b→Πf:a→b,Πg:b→a,
  (Πx:a,x=g(f x))→isProp (Σh:b→a,Πy:b,y=f(h y))`,
`eqvdata:=
λa:U.λb:U.λf:a→b.
  (Σg:b→a,Πx:a,x=g(f x))×(Σh:b→a,Πy:b,y=f(h y))`,
`eqvdataprop:=
λa:U.λb:U.λsa:isSet a.λsb:isSet b.λf:a→b.
λd1:(Σg:b→a,Πx:a,x=g(f x))×(Σh:b→a,Πy:b,y=f(h y)).
λd2:(Σg:b→a,Πx:a,x=g(f x))×(Σh:b→a,Πy:b,y=f(h y)).
sigmapath
  (Σg:b→a,Πx:a,x=g(f x))
  (λ_:(Σg:b→a,Πx:a,x=g(f x)).
    Σh:b→a,Πy:b,y=f(h y))
  d1 d2
  (leftinvprop a b sa f
    (pr0 (prd1 d1)) (prd1 (prd1 d1))
    (pr0 d1) (pr0 d2))
  ((transconst
    (leftinvprop a b sa f
      (pr0 (prd1 d1)) (prd1 (prd1 d1))
      (pr0 d1) (pr0 d2))
    (prd1 d1))▪
   (rightinvprop a b sb f
    (pr0 (pr0 d2)) (prd1 (pr0 d2))
    (prd1 d1) (prd1 d2)))
: Πa:U,Πb:U,isSet a→isSet b→Πf:a→b,
  isProp ((Σg:b→a,Πx:a,x=g(f x))×(Σh:b→a,Πy:b,y=f(h y)))`,
`eqvpath:=
λa:U.λb:U.λsa:isSet a.λsb:isSet b.
λe:Σf:a→b,(Σg:b→a,Πx:a,x=g(f x))×
  (Σh:b→a,Πy:b,y=f(h y)).
λk:Σf:a→b,(Σg:b→a,Πx:a,x=g(f x))×
  (Σh:b→a,Πy:b,y=f(h y)).
λp:pr0 e=pr0 k.
sigmapath (a→b)
  (λf:a→b.(Σg:b→a,Πx:a,x=g(f x))×
    (Σh:b→a,Πy:b,y=f(h y)))
  e k p
  (eqvdataprop a b sa sb (pr0 k)
    (trans
      (λf:a→b.(Σg:b→a,Πx:a,x=g(f x))×
        (Σh:b→a,Πy:b,y=f(h y)))
      p (prd1 e))
    (prd1 k))`,
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
`prodmap:=
λa:U.λb:U.λc:U.λd:U.λf:a→b.λg:c→d.
λz:a×c.ind_Prod (λ_:a×c.b×d)
  (λx:a.λy:c.pair (λ_:b.d) (f x) (g y)) z`,
`prodround:=
λa:U.λb:U.λc:U.λd:U.
λf:a→b.λg:b→a.λp:Πx:a,x=g(f x).
λh:c→d.λk:d→c.λq:Πy:c,y=k(h y).
λz:a×c.
ind_Prod (λz:a×c,z=prodmap b a d c g k (prodmap a b c d f h z))
  (λx:a.λy:c.sigmapath a (λ_:a.c)
    (pair (λ_:a.c) x y)
    (pair (λ_:a.c) (g(f x)) (k(h y)))
    (p x) ((transconst (p x) y)▪(q y))) z`,
`prodcongr:=
λa:U.λb:U.λc:U.λd:U.λe:eqv a b.λk:eqv c d.
  mkeqv (a×c) (b×d)
    (prodmap a b c d (eqvf a b e) (eqvf c d k))
    (prodmap b a d c (eqvl a b e) (eqvl c d k))
    (prodround a b c d
      (eqvf a b e) (eqvl a b e) (eqvlp a b e)
      (eqvf c d k) (eqvl c d k) (eqvlp c d k))
    (prodmap b a d c (eqvr a b e) (eqvr c d k))
    (prodround b a d c
      (eqvr a b e) (eqvf a b e) (eqvrp a b e)
      (eqvr c d k) (eqvf c d k) (eqvrp c d k))`
];

const extraDefinitions = [
`notinlr:=
λa:U.λx:a.λp:inl x=inr true.
  ind_False (λ_:False.False)
    (sumencode a True (inl x) (inr true) p)`,
`droplast:=
λa:U.λz:a+True.λp:not (z=inr true).
  ind_Sum (λ_:a+True.a)
    (λx:a.x)
    (λt:True.ind_False (λ_:False.a) (p rfl)) z`,
`droplast_round:=
λa:U.λz:a+True.λp:not (z=inr true).
  ind_Sum (λz:a+True,inl (droplast a z p)=z)
    (λx:a.rfl)
    (λt:True.ind_False (λ_:False,inl (droplast a (inr t) p)=(inr t)) (p rfl)) z`,
`droplast_inl:=
λa:U.λx:a.λp:not (inl x=inr true).rfl`,
`inlinj:=
λa:U.λx:a.λy:a.λp:inl x=inl y.
  sumencode a True (inl x) (inl y) p`,
`extendfixed:=
λa:U.λe:eqv a a.sumcongr a a True True e (eqvrefl True)`,
`restrictfixed:=
λa:U.λe:eqv (a+True) (a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
  mkeqv a a
    (λx:a.droplast a (eqvf (a+True) (a+True) e (inl x))
      (λq:not (eqvf (a+True) (a+True) e (inl x)=inr true).
        notinlr a x
          ((eqvlp (a+True) (a+True) e (inl x))▪
           (ap (eqvl (a+True) (a+True) e) q)▪
           (ap (eqvl (a+True) (a+True) e) (inveq p))▪
           (inveq (eqvlp (a+True) (a+True) e (inr true))))))
    (λy:a.droplast a (eqvl (a+True) (a+True) e (inl y))
      (λq:not (eqvl (a+True) (a+True) e (inl y)=inr true).
        notinlr a y
          ((eqvrp (a+True) (a+True) e (inl y))▪
           (ap (eqvf (a+True) (a+True) e) q)▪p)))
    (λx:a.
      inlinj a
        (droplast a (eqvf (a+True) (a+True) e (inl x)) _)
        (droplast a (eqvl (a+True) (a+True) e
          (inl (droplast a (eqvf (a+True) (a+True) e (inl x)) _))) _)
        ((inveq (droplast_round a
          (eqvl (a+True) (a+True) e
            (inl (droplast a (eqvf (a+True) (a+True) e (inl x)) _))) _))▪
         (ap (eqvl (a+True) (a+True) e)
           (droplast_round a
             (eqvf (a+True) (a+True) e (inl x)) _))▪
         (eqvlp (a+True) (a+True) e (inl x))))
    (λx:a.
      inlinj a
        (droplast a (eqvf (a+True) (a+True) e
          (inl (droplast a (eqvl (a+True) (a+True) e (inl x)) _))) _)
        (droplast a (eqvl (a+True) (a+True) e (inl x)) _)
        ((inveq (droplast_round a
          (eqvf (a+True) (a+True) e
            (inl (droplast a (eqvl (a+True) (a+True) e (inl x)) _))) _))▪
         (ap (eqvf (a+True) (a+True) e)
           (droplast_round a
             (eqvl (a+True) (a+True) e (inl x)) _))▪
         (inveq (eqvlp (a+True) (a+True) e
           (inl (droplast a (eqvl (a+True) (a+True) e (inl x)) _))))))`
];

for (const definition of [...definitions, ...extraDefinitions]) {
    const name = definition.match(/^([^:=\s]+)/)?.[1] ?? "?";
    const source = definition.replace(/\s+/g, " ").trim();
    const result = engine.registerDefinition(parser.parse(source));
    console.log(name, result.ok, result.error ?? "", result.durationMs);
    if (!result.ok) { process.exitCode = 1; break; }
}
