import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 300_000,
    semanticResourceScale: 32,
    disableSimpleFn: false,
    disableSimpleEq: false,
    language: "zh"
});

export const definitions = [
`sumcode:=
λa:U.λb:U.λx:a+b.
  ind_Sum (λ_:a+b.(a+b)→U)
    (λu:a.λy:a+b.
      ind_Sum (λ_:a+b.U) (λv:a.u=v) (λv:b.False) y)
    (λu:b.λy:a+b.
      ind_Sum (λ_:a+b.U) (λv:a.False) (λv:b.u=v) y) x
: Πa:U,Πb:U,Πx:a+b,Πy:a+b,U`,
`sumcoderfl:=
λa:U.λb:U.λx:a+b.
  ind_Sum (λz:a+b.sumcode a b z z)
    (λu:a.rfl) (λv:b.rfl) x
: Πa:U,Πb:U,Πx:a+b,sumcode a b x x`,
`sumencode:=
λa:U.λb:U.λx:a+b.λy:a+b.λp:x=y.
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
`inlinj:=
λa:U.λx:a.λy:a.λp:inl x=inl y.
  sumencode a True (inl x) (inl y) p
: Πa:U,Πx:a,Πy:a,(inl x=inl y)→x=y`,
`mkeqv:=
λa:U.λb:U.λf:a→b.λg:b→a.λη:Πx:a,x=g(f x).
λh:b→a.λε:Πy:b,y=f(h y).
@pair _ _ (a→b)
  (λf:a→b.(Σg:b→a,Πx:a,x=g(f x))×
    (Σh:b→a,Πy:b,y=f(h y)))
  f
  ((@pair _ _ (b→a) (λg:b→a.Πx:a,x=g(f x)) g η),
   (@pair _ _ (b→a) (λh:b→a.Πy:b,y=f(h y)) h ε))
: Πa:U,Πb:U,Πf:a→b,Πg:b→a,
  (Πx:a,x=g(f x))→Πh:b→a,(Πy:b,y=f(h y))→a≃b`,
`eqvf:=λa:U.λb:U.λe:a≃b.pr0 e
: Πa:U,Πb:U,(a≃b)→(a→b)`,
`eqvl:=λa:U.λb:U.λe:a≃b.pr0 (pr0 (prd1 e))
: Πa:U,Πb:U,(a≃b)→(b→a)`,
`eqvlp:=λa:U.λb:U.λe:a≃b.prd1 (pr0 (prd1 e))
: Πa:U,Πb:U,Πe:a≃b,Πx:a,x=eqvl a b e (eqvf a b e x)`,
`eqvr:=λa:U.λb:U.λe:a≃b.pr0 (pr1 (prd1 e))
: Πa:U,Πb:U,(a≃b)→(b→a)`,
`eqvrp:=λa:U.λb:U.λe:a≃b.prd1 (pr1 (prd1 e))
: Πa:U,Πb:U,Πe:a≃b,Πy:b,y=eqvf a b e (eqvr a b e y)`,
`invagree:=
λa:U.λb:U.λe:a≃b.λy:b.
  (ap (eqvl a b e) (eqvrp a b e y))▪
  (inveq (eqvlp a b e (eqvr a b e y)))
: Πa:U,Πb:U,Πe:a≃b,Πy:b,eqvl a b e y=eqvr a b e y`,
`eqvlright:=
λa:U.λb:U.λe:a≃b.λy:b.
  (eqvrp a b e y)▪
  (ap (eqvf a b e) (inveq (invagree a b e y)))
: Πa:U,Πb:U,Πe:a≃b,Πy:b,y=eqvf a b e (eqvl a b e y)`,
`fwdnotlast:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λx:a.λq:eqvf (a+True) (a+True) e (inl x)=inr true.
  notinlr a x
    ((eqvlp (a+True) (a+True) e (inl x))▪
      (ap (eqvl (a+True) (a+True) e) q)▪
      (ap (eqvl (a+True) (a+True) e) (inveq p))▪
      (inveq (eqvlp (a+True) (a+True) e (inr true))))
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,
  Πx:a,not (eqvf (a+True) (a+True) e (inl x)=inr true)`,
`leftnotlast:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λx:a.λq:eqvl (a+True) (a+True) e (inl x)=inr true.
  notinlr a x
    ((eqvlright (a+True) (a+True) e (inl x))▪
      (ap (eqvf (a+True) (a+True) e) q)▪p)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,
  Πx:a,not (eqvl (a+True) (a+True) e (inl x)=inr true)`,
`rightnotlast:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λx:a.λq:eqvr (a+True) (a+True) e (inl x)=inr true.
  notinlr a x
    ((eqvrp (a+True) (a+True) e (inl x))▪
      (ap (eqvf (a+True) (a+True) e) q)▪p)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,
  Πx:a,not (eqvr (a+True) (a+True) e (inl x)=inr true)`,
`restrictfixed:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
  mkeqv a a
    (λx:a.droplast a
      (eqvf (a+True) (a+True) e (inl x))
      (fwdnotlast a e p x))
    (λy:a.droplast a
      (eqvl (a+True) (a+True) e (inl y))
      (leftnotlast a e p y))
    (λx:a.
      inlinj a x
        (droplast a
          (eqvl (a+True) (a+True) e
            (inl (droplast a
              (eqvf (a+True) (a+True) e (inl x))
              (fwdnotlast a e p x))))
          (leftnotlast a e p
            (droplast a
              (eqvf (a+True) (a+True) e (inl x))
              (fwdnotlast a e p x))) )
        ((eqvlp (a+True) (a+True) e (inl x))▪
          (ap (eqvl (a+True) (a+True) e)
            (inveq (droplast_round a
              (eqvf (a+True) (a+True) e (inl x))
              (fwdnotlast a e p x))))▪
          (inveq (droplast_round a
            (eqvl (a+True) (a+True) e
              (inl (droplast a
                (eqvf (a+True) (a+True) e (inl x))
                (fwdnotlast a e p x))))
            (leftnotlast a e p
              (droplast a
                (eqvf (a+True) (a+True) e (inl x))
                (fwdnotlast a e p x)))))))
    (λy:a.
      inlinj a y
        (droplast a
          (eqvf (a+True) (a+True) e
            (inl (droplast a
              (eqvr (a+True) (a+True) e (inl y))
              (rightnotlast a e p y))))
          (fwdnotlast a e p
            (droplast a
              (eqvr (a+True) (a+True) e (inl y))
              (rightnotlast a e p y))) )
        ((eqvrp (a+True) (a+True) e (inl y))▪
          (ap (eqvf (a+True) (a+True) e)
            (inveq (droplast_round a
              (eqvr (a+True) (a+True) e (inl y))
              (rightnotlast a e p y))))▪
          (inveq (droplast_round a
            (eqvf (a+True) (a+True) e
              (inl (droplast a
                (eqvr (a+True) (a+True) e (inl y))
                (rightnotlast a e p y))))
            (fwdnotlast a e p
              (droplast a
                (eqvr (a+True) (a+True) e (inl y))
                (rightnotlast a e p y)))))))
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,a≃a`
];

definitions.splice(-1, 1,
`rfwd:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λx:a.droplast a
  (eqvf (a+True) (a+True) e (inl x))
  (fwdnotlast a e p x)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,Πx:a,a`,
`rleft:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λy:a.droplast a
  (eqvl (a+True) (a+True) e (inl y))
  (leftnotlast a e p y)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,Πy:a,a`,
`rright:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λy:a.droplast a
  (eqvr (a+True) (a+True) e (inl y))
  (rightnotlast a e p y)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,Πy:a,a`,
`extendfixed:=
λa:U.λe:a≃a.
  mkeqv (a+True) (a+True)
    (λz:a+True.
      ind_Sum (λ_:a+True.a+True)
        (λx:a.inl (eqvf a a e x))
        (λt:True.inr t) z)
    (λz:a+True.
      ind_Sum (λ_:a+True.a+True)
        (λx:a.inl (eqvl a a e x))
        (λt:True.inr t) z)
    (λz:a+True.
      ind_Sum
        (λz:a+True,z=
          ind_Sum (λ_:a+True.a+True)
            (λx:a.inl (eqvl a a e x))
            (λt:True.inr t)
            (ind_Sum (λ_:a+True.a+True)
              (λx:a.inl (eqvf a a e x))
              (λt:True.inr t) z))
        (λx:a.ap inl (eqvlp a a e x))
        (λt:True.rfl) z)
    (λz:a+True.
      ind_Sum (λ_:a+True.a+True)
        (λx:a.inl (eqvr a a e x))
        (λt:True.inr t) z)
    (λz:a+True.
      ind_Sum
        (λz:a+True,z=
          ind_Sum (λ_:a+True.a+True)
            (λx:a.inl (eqvf a a e x))
            (λt:True.inr t)
            (ind_Sum (λ_:a+True.a+True)
              (λx:a.inl (eqvr a a e x))
              (λt:True.inr t) z))
        (λx:a.ap inl (eqvrp a a e x))
        (λt:True.rfl) z)
: Πa:U,(a≃a)→((a+True)≃(a+True))`,
`extendfixedfwd:=
λa:U.λe:a≃a.λx:a.rfl
: Πa:U,Πe:a≃a,Πx:a,
  eqvf (a+True) (a+True) (extendfixed a e) (inl x)=
    inl (eqvf a a e x)`,
`extendfixedlast:=
λa:U.λe:a≃a.rfl
: Πa:U,Πe:a≃a,
  eqvf (a+True) (a+True) (extendfixed a e) (inr true)=inr true`,
`restrictextendfwd:=
λa:U.λe:a≃a.λx:a.rfl
: Πa:U,Πe:a≃a,Πx:a,
  rfwd a (extendfixed a e) (extendfixedlast a e) x=eqvf a a e x`,
`rleftp:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λx:a.
  inlinj a x (rleft a e p (rfwd a e p x))
    ((eqvlp (a+True) (a+True) e (inl x))▪
      (ap (eqvl (a+True) (a+True) e)
        (inveq (droplast_round a
          (eqvf (a+True) (a+True) e (inl x))
          (fwdnotlast a e p x))))▪
      (inveq (droplast_round a
        (eqvl (a+True) (a+True) e (inl (rfwd a e p x)))
        (leftnotlast a e p (rfwd a e p x)))))
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,
  Πx:a,x=rleft a e p (rfwd a e p x)`,
`rrightp:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λy:a.
  inlinj a y (rfwd a e p (rright a e p y))
    ((eqvrp (a+True) (a+True) e (inl y))▪
      (ap (eqvf (a+True) (a+True) e)
        (inveq (droplast_round a
          (eqvr (a+True) (a+True) e (inl y))
          (rightnotlast a e p y))))▪
      (inveq (droplast_round a
        (eqvf (a+True) (a+True) e (inl (rright a e p y)))
        (fwdnotlast a e p (rright a e p y)))))
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,
  Πy:a,y=rfwd a e p (rright a e p y)`,
`restrictfixed:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
  mkeqv a a
    (rfwd a e p)
    (rleft a e p)
    (rleftp a e p)
    (rright a e p)
    (rrightp a e p)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,a≃a`,
`eqvcomp:=
λa:U.λb:U.λc:U.λe:a≃b.λk:b≃c.
  mkeqv a c
    (λx:a.eqvf b c k (eqvf a b e x))
    (λz:c.eqvl a b e (eqvl b c k z))
    (λx:a.(eqvlp a b e x)▪
      ap (eqvl a b e) (eqvlp b c k (eqvf a b e x)))
    (λz:c.eqvr a b e (eqvr b c k z))
    (λz:c.(eqvrp b c k z)▪
      ap (eqvf b c k) (eqvrp a b e (eqvr b c k z)))
: Πa:U,Πb:U,Πc:U,Πe:a≃b,Πk:b≃c,a≃c`,
`Fin:=ind_nat (λn:nat.U) False (λn:nat.λu:U.u+True)
: nat→U`,
`extendlast:=
λa:U.λf:a→a.λz:a+True.
  ind_Sum (λ_:a+True.a+True)
    (λx:a.inl (f x))
    (λt:True.inr t) z
: Πa:U,Πf:a→a,(a+True)→(a+True)`,
`extendlastself:=
λa:U.λf:a→a.λh:Πx:a,x=f(f x).λz:a+True.
  ind_Sum (λw:a+True.w=extendlast a f (extendlast a f w))
    (λx:a.ap inl (h x))
    (λt:True.rfl) z
: Πa:U,Πf:a→a,(Πx:a,x=f(f x))→Πz:a+True,
  z=extendlast a f (extendlast a f z)`,
`swap2fn:=
λa:U.λz:(a+True)+True.
  ind_Sum (λ_:((a+True)+True).((a+True)+True))
    (λu:a+True.
      ind_Sum (λ_:a+True.((a+True)+True))
        (λx:a.inl (inl x))
        (λt:True.inr true) u)
    (λt:True.inl (inr true)) z
: Πa:U,((a+True)+True)→((a+True)+True)`,
`swap2self:=
λa:U.λz:(a+True)+True.
  ind_Sum (λw:(a+True)+True.w=swap2fn a (swap2fn a w))
    (λu:a+True.
      ind_Sum (λv:a+True.inl v=swap2fn a (swap2fn a (inl v)))
        (λx:a.rfl)
        (λt:True.ind_True
          (λt:True.inl (inr t)=swap2fn a (swap2fn a (inl (inr t))))
          rfl t) u)
    (λt:True.ind_True
      (λt:True.inr t=swap2fn a (swap2fn a (inr t))) rfl t) z
: Πa:U,Πz:(a+True)+True,z=swap2fn a (swap2fn a z)`,
`conjself:=
λa:U.λf:a→a.λg:a→a.
λhf:Πz:a,z=f(f z).λhg:Πz:a,z=g(g z).λz:a.
  ((hf z)▪(ap f (hg (f z))))▪
  (ap (λw:a.f(g w)) (hf (g(f z))))`,
`swaplast:=
ind_nat (λn:nat.Fin(succ n)→Fin(succ n)→Fin(succ n))
  (λy:Fin(succ 0).λz:Fin(succ 0).z)
  (λn:nat.λih:Fin(succ n)→Fin(succ n)→Fin(succ n).
    λy:Fin(succ(succ n)).
    ind_Sum
      (λ_:Fin(succ(succ n)).Fin(succ(succ n))→Fin(succ(succ n)))
      (λu:Fin(succ n).λz:Fin(succ(succ n)).
        extendlast (Fin(succ n)) (ih u)
          (swap2fn (Fin n)
            (extendlast (Fin(succ n)) (ih u) z)))
      (λt:True.λz:Fin(succ(succ n)).z) y)
: Πn:nat,Fin(succ n)→Fin(succ n)→Fin(succ n)`,
`swaplastself:=
ind_nat (λn:nat.Πy:Fin(succ n),Πz:Fin(succ n),
  z=swaplast n y (swaplast n y z))
  (λy:Fin(succ 0).λz:Fin(succ 0).rfl)
  (λn:nat.λih:Πy:Fin(succ n),Πz:Fin(succ n),
    z=swaplast n y (swaplast n y z).
    λy:Fin(succ(succ n)).
    ind_Sum
      (λy:Fin(succ(succ n)).Πz:Fin(succ(succ n)),
        z=swaplast (succ n) y (swaplast (succ n) y z))
      (λu:Fin(succ n).λz:Fin(succ(succ n)).
        conjself (Fin(succ n)+True)
          (extendlast (Fin(succ n)) (swaplast n u))
          (swap2fn (Fin n))
          (extendlastself (Fin(succ n)) (swaplast n u) (ih u))
          (swap2self (Fin n)) z)
      (λt:True.λz:Fin(succ(succ n)).rfl) y)
: Πn:nat,Πy:Fin(succ n),Πz:Fin(succ n),
  z=swaplast n y (swaplast n y z)`,
`swaplastpoint:=
ind_nat (λn:nat.Πy:Fin(succ n),swaplast n y y=inr true)
  (λy:Fin(succ 0).
    ind_Sum (λy:Fin(succ 0).swaplast 0 y y=inr true)
      (λx:False.ind_False
        (λ_:False.swaplast 0 (inl x) (inl x)=inr true) x)
      (λt:True.ind_True
        (λt:True.swaplast 0 (inr t) (inr t)=inr true) rfl t) y)
  (λn:nat.λih:Πy:Fin(succ n),swaplast n y y=inr true.
    λy:Fin(succ(succ n)).
    ind_Sum (λy:Fin(succ(succ n)).
      swaplast (succ n) y y=inr true)
      (λu:Fin(succ n).
        ap (λv:Fin(succ n)+True.
          extendlast (Fin(succ n)) (swaplast n u)
            (swap2fn (Fin n) v))
          (ap inl (ih u)))
      (λt:True.ind_True
        (λt:True.swaplast (succ n) (inr t) (inr t)=inr true) rfl t) y)
: Πn:nat,Πy:Fin(succ n),swaplast n y y=inr true`,
`swaplastlast:=
ind_nat (λn:nat.Πy:Fin(succ n),swaplast n y (inr true)=y)
  (λy:Fin(succ 0).
    ind_Sum (λy:Fin(succ 0).swaplast 0 y (inr true)=y)
      (λx:False.ind_False
        (λ_:False.swaplast 0 (inl x) (inr true)=inl x) x)
      (λt:True.ind_True
        (λt:True.swaplast 0 (inr t) (inr true)=inr t) rfl t) y)
  (λn:nat.λih:Πy:Fin(succ n),swaplast n y (inr true)=y.
    λy:Fin(succ(succ n)).
    ind_Sum (λy:Fin(succ(succ n)).
      swaplast (succ n) y (inr true)=y)
      (λu:Fin(succ n).ap inl (ih u))
      (λt:True.ind_True
        (λt:True.swaplast (succ n) (inr t) (inr true)=inr t) rfl t) y)
: Πn:nat,Πy:Fin(succ n),swaplast n y (inr true)=y`,
`movelast:=
λn:nat.λy:Fin(succ n).
  mkeqv (Fin(succ n)) (Fin(succ n))
    (swaplast n y)
    (swaplast n y) (swaplastself n y)
    (swaplast n y) (swaplastself n y)
: Πn:nat,Πy:Fin(succ n),Fin(succ n)≃Fin(succ n)`,
`movelastpoint:=
λn:nat.λy:Fin(succ n).swaplastpoint n y
: Πn:nat,Πy:Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n)) (movelast n y) y=inr true`,
`movelastlast:=
λn:nat.λy:Fin(succ n).swaplastlast n y
: Πn:nat,Πy:Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n)) (movelast n y) (inr true)=y`,
`splitfix:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  movelastpoint n
    (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true))
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n))
    (eqvcomp (Fin(succ n)) (Fin(succ n)) (Fin(succ n)) e
      (movelast n (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true))))
    (inr true)=inr true`,
`splitfwd:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  @pair _ _ (Fin n≃Fin n)
    (λ_:Fin n≃Fin n.Fin(succ n))
    (restrictfixed (Fin n)
      (eqvcomp (Fin(succ n)) (Fin(succ n)) (Fin(succ n)) e
        (movelast n
          (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true))))
      (splitfix n e))
    (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true))
: Πn:nat,(Fin(succ n)≃Fin(succ n))→
  ((Fin n≃Fin n)×Fin(succ n))`,
`splitinv:=
λn:nat.λz:((Fin n≃Fin n)×Fin(succ n)).
  eqvcomp (Fin(succ n)) (Fin(succ n)) (Fin(succ n))
    (extendfixed (Fin n) (pr0 z))
    (movelast n (prd1 z))
: Πn:nat,((Fin n≃Fin n)×Fin(succ n))→
  (Fin(succ n)≃Fin(succ n))`,
`splitfwdsecond:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).rfl
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  prd1 (splitfwd n e)=
    eqvf (Fin(succ n)) (Fin(succ n)) e (inr true)`,
`splitinvlast:=
λn:nat.λz:((Fin n≃Fin n)×Fin(succ n)).
  movelastlast n (prd1 z)
: Πn:nat,Πz:((Fin n≃Fin n)×Fin(succ n)),
  eqvf (Fin(succ n)) (Fin(succ n)) (splitinv n z) (inr true)=prd1 z`
);

for (let index = 0; index < definitions.length; index++) {
    const source = definitions[index].replace(/\s+/gu, " ").trim();
    const name = source.slice(0, source.indexOf(":="));
    const result = session.validate(index, parser.parse(source));
    console.log(`${index} ${name} ok=${result.ok} ${result.error ?? ""}`);
    if (!result.ok) {
        const boundary = source.lastIndexOf(" : ");
        if (boundary >= 0) {
            const probe = session.validate(index, parser.parse(source.slice(0, boundary)));
            console.log(`probe ok=${probe.ok} type=${probe.type ? parser.stringify(probe.type) : ""} ${probe.error ?? ""}`);
        }
        process.exit(1);
    }
}
