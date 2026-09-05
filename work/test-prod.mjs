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
const options = { disableMultipleApply: false, disableDestructConds: false, disableDestructEq: false };
const reg = source => {
    const result = core.registerDefinition(parser.parse(source.replace(/\s+/g, " ").trim()));
    console.log("REG", source.slice(0, source.indexOf(":=")), result.ok, result.error ?? "");
    if (!result.ok) throw new Error(result.error);
};
reg(`mkeqv:=λa:U.λb:U.λf:a→b.λg:b→a.λη:Πx:a,x=g(f x).λh:b→a.λε:Πy:b,y=f(h y).@pair _ _ (a→b) (λf:a→b.(Σg:b→a,Πx:a,x=g(f x))×(Σh:b→a,Πy:b,y=f(h y))) f ((@pair _ _ (b→a) (λg:b→a.Πx:a,x=g(f x)) g η),(@pair _ _ (b→a) (λh:b→a.Πy:b,y=f(h y)) h ε))`);
reg(`sigmapath:=λa:U.λb:a→U.λx:Σz:a,b z.ind_Prod b (λx:Σz:a,b z.Πy:Σz:a,b z.Πp:pr0 x=pr0 y.Πq:trans b p (prd1 x)=prd1 y.x=y) (λx0:a.λx1:b x0.λy:Σz:a,b z.ind_Prod b (λy:Σz:a,b z.Πp:x0=pr0 y.Πq:trans b p x1=prd1 y.@pair _ _ a b x0 x1=y) (λy0:a.λy1:b y0.λp:x0=y0.ind_eq x0 (λy0:a.λp:x0=y0.Πy1:b y0.Πq:trans b p x1=y1.@pair _ _ a b x0 x1=@pair _ _ a b y0 y1) (λy1:b x0.λq:trans b rfl x1=y1.ind_eq x1 (λy1:b x0.λq:x1=y1.@pair _ _ a b x0 x1=@pair _ _ a b x0 y1) rfl y1 q) y0 p y1) y) x`);
for (const [name, source] of [
    ["eqvf", `eqvf:=(λa:U.λb:U.λe:eqv a b.pr0 e)`],
    ["eqvl", `eqvl:=(λa:U.λb:U.λe:eqv a b.pr0 (pr0 (prd1 e)))`],
    ["eqvlp", `eqvlp:=(λa:U.λb:U.λe:eqv a b.prd1 (pr0 (prd1 e)))`],
    ["eqvr", `eqvr:=(λa:U.λb:U.λe:eqv a b.pr0 (pr1 (prd1 e)))`],
    ["eqvrp", `eqvrp:=(λa:U.λb:U.λe:eqv a b.prd1 (pr1 (prd1 e)))`]
]) reg(source);
reg(`prodmap:=λa:U.λb:U.λc:U.λd:U.λf:a→b.λg:c→d.λz:a×c.ind_Prod (λ_:a.c) (λ_:a×c.b×d) (λx:a.λy:c.pair (λ_:b.d) (f x) (g y)) z`);
const assist = new TTAssistEngine(core);
let s = assist.start("Πa:U,Πb:U,Πc:U,Πd:U,Πe:a≃b,Πk:c≃d,(a×c)≃(b×d)", options);
const run = command => {
    s = assist.apply(command);
    console.log(command, s.goals.map(goal => ({
        ctx: goal.context.map(([n,t]) => `${n}:${parser.stringify(t)}`),
        target: parser.stringify(goal.type)
    })));
};
for (const command of [
    "intro a", "intro b", "intro c", "intro d", "intro e", "intro k", "expand eqv", "ex",
    "intro z", "case", "exact (pr0 e) (pr0 z)", "exact (pr0 k) (prd1 z)",
    "constructor", "ex", "intro w", "case", "exact (pr0 (pr0 (prd1 e))) (pr0 w)",
    "exact (pr0 (pr0 (prd1 k))) (prd1 w)", "intro z",
    "apply sigmapath a (λ_:a.c)", "exact (prd1 (pr0 (prd1 e))) (pr0 z)",
    "exact (transconst ((prd1 (pr0 (prd1 e))) (pr0 z)) (prd1 z))▪((prd1 (pr0 (prd1 k))) (prd1 z))",
    "ex", "intro w", "case", "exact (pr0 (pr1 (prd1 e))) (pr0 w)",
    "exact (pr0 (pr1 (prd1 k))) (prd1 w)", "intro w",
    "apply sigmapath b (λ_:b.d)", "exact (prd1 (pr1 (prd1 e))) (pr0 w)",
    "exact (transconst ((prd1 (pr1 (prd1 e))) (pr0 w)) (prd1 w))▪((prd1 (pr1 (prd1 k))) (prd1 w))"
]) run(command);
const result = assist.qed();
console.log("QED", result.theorem, result.proof.length);
reg(`prodcongr:=(${result.proof}):${result.theorem}`);
