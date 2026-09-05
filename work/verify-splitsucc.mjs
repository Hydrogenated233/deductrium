import { readFileSync } from "node:fs";
import { ASTParser } from "../js/tt/astparser.js";
import { TTCoreSession } from "../js/tt/core-session.js";
import { TTAssistEngine } from "../js/tt/assist-engine.js";
import { initTypeSystem } from "../js/tt/initial.js";

const parser = new ASTParser();
const session = new TTCoreSession();
session.configure({
    unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
    inferDisplayMode: "_",
    timeout: 300_000,
    semanticResourceScale: 48,
    disableSimpleFn: false,
    disableSimpleEq: false,
    language: "zh"
});

const restrictionSource = readFileSync(new URL("./verify-restrictfixed.mjs", import.meta.url), "utf8");
const structureSource = readFileSync(new URL("./verify-fin-structure.mjs", import.meta.url), "utf8");
const productSource = readFileSync(new URL("./verify-prod-finmul-session.mjs", import.meta.url), "utf8");
const documentSource = readFileSync(new URL("../docs/fin-self-equivalences-factorial.md", import.meta.url), "utf8");

function quotedDefinition(source, name) {
    const start = source.lastIndexOf(`\`${name}:=`);
    if (start < 0) throw new Error(`missing quoted definition ${name}`);
    const end = source.indexOf("`", start + 1);
    if (end < 0) throw new Error(`unterminated quoted definition ${name}`);
    return source.slice(start + 1, end);
}

function documentDefinition(name) {
    const start = documentSource.indexOf(`${name}:=`);
    if (start < 0) throw new Error(`missing documented definition ${name}`);
    const rest = documentSource.slice(start);
    const next = rest.search(/\n(?=[A-Za-z][A-Za-z0-9_]*:=)|\n~~~/u);
    if (next < 0) throw new Error(`unterminated documented definition ${name}`);
    return rest.slice(0, next).trim();
}

const restrictionDefinitions = [
    "sumcode", "sumcoderfl", "sumencode", "notinlr", "droplast",
    "droplast_round", "inlinj", "mkeqv", "eqvf", "eqvl", "eqvlp",
    "eqvr", "eqvrp", "invagree", "eqvlright", "fwdnotlast",
    "leftnotlast", "rightnotlast", "rfwd", "rleft", "rright",
    "extendfixed", "extendfixedfwd", "extendfixedlast",
    "restrictextendfwd", "rleftp", "rrightp", "restrictfixed",
    "eqvcomp", "Fin", "extendlast", "extendlastself", "swap2fn",
    "swap2self", "conjself", "swaplast", "swaplastself",
    "swaplastpoint", "swaplastlast", "movelast", "movelastpoint",
    "movelastlast", "splitfix", "splitfwd", "splitinv",
    "splitfwdsecond", "splitinvlast"
].map(name => quotedDefinition(restrictionSource, name));

const pathDefinitions = [
    "sigmapath", "piprop", "leftinvprop", "rightinvprop", "eqvdata",
    "eqvdataprop", "eqvpath"
].map(name => quotedDefinition(structureSource, name));

const finiteSetDefinitions = [
    "Contr", "contrpath", "contrtoprop", "contrtoset", "sumdecode",
    "sumdecodeencode", "sumencodedecode", "sumcodeprop", "sumset",
    "falseset", "truecontr", "trueset", "finset"
].map(documentDefinition);

const splitDefinitions = [
`pack:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  @pair _ _ (Fin n≃Fin n)
    (λ_:Fin n≃Fin n.Fin(succ n)) u y
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  ((Fin n≃Fin n)×Fin(succ n))`,
`corrected:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  eqvcomp (Fin(succ n)) (Fin(succ n)) (Fin(succ n)) e
    (movelast n
      (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true)) )
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  Fin(succ n)≃Fin(succ n)`,
`correctedfix:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  movelastpoint n
    (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true))
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n)) (corrected n e)
    (inr true)=inr true`,
`extendrestrictfwd:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λz:a+True.
  ind_Sum
    (λz:a+True.
      eqvf (a+True) (a+True)
        (extendfixed a (restrictfixed a e p)) z=
      eqvf (a+True) (a+True) e z)
    (λx:a.
      droplast_round a
        (eqvf (a+True) (a+True) e (inl x))
        (fwdnotlast a e p x))
    (λt:True.
      ind_True
        (λt:True.
          eqvf (a+True) (a+True)
            (extendfixed a (restrictfixed a e p)) (inr t)=
          eqvf (a+True) (a+True) e (inr t))
        (inveq p) t) z
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,Πz:a+True,
  eqvf (a+True) (a+True)
    (extendfixed a (restrictfixed a e p)) z=
  eqvf (a+True) (a+True) e z`,
`round1c:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  corrected n (splitinv n (pack n u y))
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  Fin(succ n)≃Fin(succ n)`,
`round1cp:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  correctedfix n (splitinv n (pack n u y))
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n)) (round1c n u y)
    (inr true)=inr true`,
`round1mid:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).λx:Fin n.
  ((ap (λw:Fin(succ n).
      swaplast n w
        (swaplast n y
          (eqvf (Fin(succ n)) (Fin(succ n))
            (extendfixed (Fin n) u) (inl x))))
    (splitinvlast n (pack n u y)))▪
    (inveq (swaplastself n y
      (eqvf (Fin(succ n)) (Fin(succ n))
        (extendfixed (Fin n) u) (inl x)))) )▪
  (extendfixedfwd (Fin n) u x)
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),Πx:Fin n,
  eqvf (Fin(succ n)) (Fin(succ n)) (round1c n u y) (inl x)=
  inl (eqvf (Fin n) (Fin n) u x)`,
`round1fwdcore:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).λx:Fin n.
  inlinj (Fin n)
    (rfwd (Fin n)
      (round1c n u y)
      (round1cp n u y) x)
    (eqvf (Fin n) (Fin n) u x)
    ((droplast_round (Fin n)
      (eqvf (Fin(succ n)) (Fin(succ n))
        (round1c n u y) (inl x))
      (fwdnotlast (Fin n)
        (round1c n u y)
        (round1cp n u y) x))▪
     (round1mid n u y x))
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),Πx:Fin n,
  rfwd (Fin n)
    (round1c n u y)
    (round1cp n u y) x=
  eqvf (Fin n) (Fin n) u x`,
`splitround1fwd:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).λx:Fin n.
  round1fwdcore n u y x
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),Πx:Fin n,
  eqvf (Fin n) (Fin n)
    (pr0 (splitfwd n (splitinv n (pack n u y)))) x=
  eqvf (Fin n) (Fin n) u x`,
`splitround1eqv:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  eqvpath (Fin n) (Fin n) (finset n) (finset n)
    (pr0 (splitfwd n (splitinv n (pack n u y)))) u
    (fnext (splitround1fwd n u y))
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  pr0 (splitfwd n (splitinv n (pack n u y)))=u`,
`prodpath:=
λa:U.λb:U.λx:a.λx':a.λy:b.λy':b.λp:x=x'.λq:y=y'.
  ind_eq x
    (λx':a.λp:x=x'.Πy:b.Πy':b,y=y'→
      @pair _ _ a (λ_:a.b) x y=
      @pair _ _ a (λ_:a.b) x' y')
    (λy:b.λy':b.λq:y=y'.
      ap (λz:b.@pair _ _ a (λ_:a.b) x z) q)
    x' p y y' q
: Πa:U,Πb:U,Πx:a,Πx':a,Πy:b,Πy':b,
  (x=x')→(y=y')→
  (@pair _ _ a (λ_:a.b) x y=@pair _ _ a (λ_:a.b) x' y')`,
`splitround1:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  prodpath (Fin n≃Fin n) (Fin(succ n))
    (pr0 (splitfwd n (splitinv n (pack n u y)))) u
    (prd1 (splitfwd n (splitinv n (pack n u y)))) y
    (splitround1eqv n u y)
    ((splitfwdsecond n (splitinv n (pack n u y)))▪
      (splitinvlast n (pack n u y)))
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  splitfwd n (splitinv n (pack n u y))=pack n u y`,
`splitround2fwd:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).λz:Fin(succ n).
  (ap
    (eqvf (Fin(succ n)) (Fin(succ n))
      (movelast n
        (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true))))
    (extendrestrictfwd (Fin n) (corrected n e)
      (correctedfix n e) z))▪
  (inveq (swaplastself n
    (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true))
    (eqvf (Fin(succ n)) (Fin(succ n)) e z)))
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),Πz:Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n))
    (splitinv n (splitfwd n e)) z=
  eqvf (Fin(succ n)) (Fin(succ n)) e z`,
`splitround2:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  eqvpath (Fin(succ n)) (Fin(succ n))
    (finset (succ n)) (finset (succ n))
    (splitinv n (splitfwd n e)) e
    (fnext (splitround2fwd n e))
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  splitinv n (splitfwd n e)=e`,
`spliteta:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  inveq (splitround2 n e)
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  e=splitinv n (splitfwd n e)`,
`splitepsilon:=
λn:nat.λz:((Fin n≃Fin n)×Fin(succ n)).
  ind_Prod (λ_:Fin n≃Fin n.Fin(succ n))
    (λz:((Fin n≃Fin n)×Fin(succ n)).
      z=splitfwd n (splitinv n z))
    (λu:Fin n≃Fin n.λy:Fin(succ n).
      inveq (splitround1 n u y)) z
: Πn:nat,Πz:((Fin n≃Fin n)×Fin(succ n)),
  z=splitfwd n (splitinv n z)`,
`splitsucc:=
λn:nat.
  mkeqv (Fin(succ n)≃Fin(succ n))
    ((Fin n≃Fin n)×Fin(succ n))
    (λe:Fin(succ n)≃Fin(succ n).splitfwd n e)
    (λz:((Fin n≃Fin n)×Fin(succ n)).splitinv n z)
    (spliteta n)
    (λz:((Fin n≃Fin n)×Fin(succ n)).splitinv n z)
    (splitepsilon n)
: Πn:nat,(Fin(succ n)≃Fin(succ n))≃
  ((Fin n≃Fin n)×Fin(succ n))`
];

const algebraDefinitions = [
`sumcongr:=
λa:U.λb:U.λc:U.λd:U.λe:a≃b.λk:c≃d.
  id2eqv
    ((ap (λx:U.x+c) (ua e))▪
     (ap (λx:U.b+x) (ua k)))
: Πa:U,Πb:U,Πc:U,Πd:U,
  (a≃b)→(c≃d)→((a+c)≃(b+d))`,
`prodcongr:=
λa:U.λb:U.λc:U.λd:U.λe:a≃b.λk:c≃d.
  id2eqv
    ((ap (λx:U.x×c) (ua e))▪
     (ap (λx:U.b×x) (ua k)))
: Πa:U,Πb:U,Πc:U,Πd:U,
  (a≃b)→(c≃d)→((a×c)≃(b×d))`
];

const finAlgebraDefinitions = [
    ...[
        "embed", "liftf", "liftg", "liftfembed", "liftroundl",
        "liftroundr", "finstep", "finadd", "finmuldistrib",
        "finmulcongr", "finmulmiddle", "finmulstep", "finmul"
    ].map(name => quotedDefinition(productSource, name))
];

const finalDefinitions = [
`autfalsecenter:=
λe:False≃False.
  eqvpath False False falseset falseset e (eqvrefl False)
    (fnext (λx:False.
      ind_False (λ_:False.
        eqvf False False e x=x) x))
: Πe:False≃False,e=eqvrefl False`,
`autbase:=
  mkeqv (False≃False) (False+True)
    (λe:False≃False.inr true)
    (λz:False+True.
      ind_Sum (λ_:False+True.False≃False)
        (λx:False.ind_False (λ_:False.False≃False) x)
        (λt:True.ind_True
          (λt:True.False≃False) (eqvrefl False) t) z)
    (λe:False≃False.autfalsecenter e)
    (λz:False+True.
      ind_Sum (λ_:False+True.False≃False)
        (λx:False.ind_False (λ_:False.False≃False) x)
        (λt:True.ind_True
          (λt:True.False≃False) (eqvrefl False) t) z)
    (λz:False+True.
      ind_Sum (λz:False+True.
        z=inr true)
        (λx:False.ind_False
          (λ_:False.inl x=inr true) x)
        (λt:True.ind_True
          (λt:True.inr t=inr true) rfl t) z)
: (Fin 0≃Fin 0)≃Fin(factorial 0)`,
`factorialsucc:=
λn:nat.rfl
: Πn:nat,factorial(succ n)=mul (factorial n) (succ n)`,
`finautprod:=
λn:nat.λih:(Fin n≃Fin n)≃Fin(factorial n).
  id2eqv
    ((ap (λx:U.x×Fin(succ n)) (ua ih))▪
     (ap (λx:U.Fin(factorial n)×x)
       (ua (eqvrefl (Fin(succ n))))) )
: Πn:nat,Πih:(Fin n≃Fin n)≃Fin(factorial n),
  ((Fin n≃Fin n)×Fin(succ n))≃
  (Fin(factorial n)×Fin(succ n))`,
`finautmul:=
λn:nat.finmul (factorial n) (succ n)
: Πn:nat,(Fin(factorial n)×Fin(succ n))≃
  Fin(mul (factorial n) (succ n))`,
`finautfact:=
λn:nat.id2eqv (ap Fin (inveq (factorialsucc n)))
: Πn:nat,Fin(mul (factorial n) (succ n))≃
  Fin(factorial(succ n))`,
`finautmiddle:=
λn:nat.λih:(Fin n≃Fin n)≃Fin(factorial n).
  eqvcomp ((Fin n≃Fin n)×Fin(succ n))
    (Fin(factorial n)×Fin(succ n))
    (Fin(mul (factorial n) (succ n)))
    (finautprod n ih)
    (finautmul n)
: Πn:nat,Πih:(Fin n≃Fin n)≃Fin(factorial n),
  ((Fin n≃Fin n)×Fin(succ n))≃
  Fin(mul (factorial n) (succ n))`,
`finautright:=
λn:nat.λih:(Fin n≃Fin n)≃Fin(factorial n).
  eqvcomp ((Fin n≃Fin n)×Fin(succ n))
    (Fin(mul (factorial n) (succ n)))
    (Fin(factorial(succ n)))
    (finautmiddle n ih)
    (finautfact n)
: Πn:nat,Πih:(Fin n≃Fin n)≃Fin(factorial n),
  ((Fin n≃Fin n)×Fin(succ n))≃
  Fin(factorial(succ n))`,
`finautstep:=
λn:nat.λih:(Fin n≃Fin n)≃Fin(factorial n).
  eqvcomp (Fin(succ n)≃Fin(succ n))
    ((Fin n≃Fin n)×Fin(succ n))
    (Fin(factorial(succ n)))
    (splitsucc n)
    (finautright n ih)
: Πn:nat,((Fin n≃Fin n)≃Fin(factorial n))→
  ((Fin(succ n)≃Fin(succ n))≃Fin(factorial(succ n)))`,
`finAutFactorial:=
ind_nat (λx:nat.(Fin x≃Fin x)≃Fin(factorial x))
  autbase
  finautstep
: Πx:nat,((Fin x)≃(Fin x))≃Fin(factorial x)`
];

const definitions = [
    ...restrictionDefinitions,
    ...pathDefinitions,
    ...finiteSetDefinitions,
    ...splitDefinitions,
    ...algebraDefinitions
];

let nextIndex = 0;
function validate(sourceText) {
    const source = sourceText.replace(/\s+/gu, " ").trim();
    const name = source.slice(0, source.indexOf(":="));
    const index = nextIndex++;
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

for (const definition of definitions) validate(definition);

const proofOptions = {
    disableMultipleApply: false,
    disableDestructConds: false,
    disableDestructEq: false
};
function prove(name, target, commands) {
    const assist = new TTAssistEngine(session.engine);
    assist.start(target, proofOptions);
    for (const command of commands) assist.apply(command);
    const result = assist.qed();
    validate(`${name}:=(${result.proof}):${result.theorem}`);
}

prove("sumfalse", "Πa:U,(a+False)≃a", [
    "intro a", "expand eqv", "ex", "intro z", "destruct z", "exact zl",
    "destruct zr", "constructor", "ex", "intro x", "exact inl x",
    "intro x", "destruct x", "rfl", "exact ind_False _ xr", "ex",
    "intro x", "exact inl x", "intro x", "rfl"
]);
prove("prodfalse", "Πa:U,(a×False)≃False", [
    "intro a", "expand eqv", "ex", "intro z", "destruct z",
    "exact ind_False _ z1", "constructor", "ex", "intro x",
    "exact ind_False _ x", "intro x", "destruct x", "exact ind_False _ x1",
    "ex", "intro x", "exact ind_False _ x", "intro x",
    "exact ind_False _ x"
]);
prove("prodtrue", "Πa:U,(a×True)≃a", [
    "intro a", "expand eqv", "ex", "intro z", "destruct z", "exact z0",
    "constructor", "ex", "intro x", "case", "exact x", "exact true",
    "intro x", "destruct x", "destruct x1", "rfl", "ex", "intro x",
    "case", "exact x", "exact true", "intro x", "rfl"
]);
prove("prodsum", "Πa:U,Πb:U,Πc:U,(a×(b+c))≃((a×b)+(a×c))", [
    "intro a", "intro b", "intro c", "expand eqv", "ex", "intro z",
    "destruct z", "destruct z1", "left", "case", "exact z0",
    "exact z1l", "right", "case", "exact z0", "exact z1r",
    "constructor", "ex", "intro z", "destruct z", "destruct zl",
    "case", "exact zl0", "left", "exact zl1", "destruct zr",
    "case", "exact zr0", "right", "exact zr1", "intro z",
    "destruct z", "destruct z1", "rfl", "rfl", "ex", "intro z",
    "destruct z", "destruct zl", "case", "exact zl0", "left",
    "exact zl1", "destruct zr", "case", "exact zr0", "right",
    "exact zr1", "intro z", "destruct z", "destruct zl", "rfl",
    "destruct zr", "rfl"
]);

for (const definition of finAlgebraDefinitions) validate(definition);
for (const definition of finalDefinitions) validate(definition);
