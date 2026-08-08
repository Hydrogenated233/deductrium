import { TTCoreEngine } from "../../js/tt/engine.js";
import { ASTParser } from "../../js/tt/astparser.js";
import { initTypeSystem } from "../../js/tt/initial.js";

const parser = new ASTParser();
const engine = new TTCoreEngine();
engine.configure({
  unlockedTypes: [...new Set(initTypeSystem().map(rule => rule.id))],
  inferDisplayMode: "_",
  timeout: 30000,
  language: "zh"
});

const sources = [
  `s1_encode_family:=(λx:S1.λp:base=x.trans (λx:S1.code_S1 x) p 0Z):(Πx:S1,(base=x)->code_S1 x)`,
  `s1_trans_comp:=(λx:S1.λy:S1.λp:x=y.ind_eq x (λy':S1.λp':x=y'.Πz:S1.Πq:y'=z.Πa:code_S1 x,trans (λt:S1.code_S1 t) (p'*q) a=trans (λt:S1.code_S1 t) q (trans (λt:S1.code_S1 t) p' a)) (λz:S1.λq:x=z.λa:code_S1 x.rfl) y p):(Πx:S1,Πy:S1,Πp:x=y,Πz:S1,Πq:y=z,Πa:code_S1 x,trans (λt:S1.code_S1 t) (p*q) a=trans (λt:S1.code_S1 t) q (trans (λt:S1.code_S1 t) p a))`,
  `s1_trans_apply:=(λx:S1.λy:S1.λp:x=y.λf:(code_S1 x→base=x).ind_eq x (λy':S1.λp':x=y'.Πz:code_S1 y',(trans (λt:S1.code_S1 t→base=t) p' f) z=trans (λt:S1,base=t) p' (f (trans (λt:S1.code_S1 t) (inveq p') z))) (λz:code_S1 x.rfl) y p):(Πx:S1,Πy:S1,Πp:x=y,Πf:(code_S1 x→base=x),Πz:code_S1 y,(trans (λt:S1.code_S1 t→base=t) p f) z=trans (λt:S1,base=t) p (f (trans (λt:S1.code_S1 t) (inveq p) z))))`,
  `s1_trans_base:=(λx:S1.λy:S1.λp:x=y.λq:base=x.transright p q):(Πx:S1,Πy:S1,Πp:x=y,Πq:base=x,trans (λt:S1,base=t) p q=q*p)`,
  `s1_trans_inv_r:=(λx:S1.λy:S1.λq:x=y.ind_eq x (λy':S1.λq':x=y'.Πz:code_S1 y',trans (λt:S1.code_S1 t) q' (trans (λt:S1.code_S1 t) (inveq q') z)=z) (λz:code_S1 x.rfl) y q):(Πx:S1,Πy:S1,Πq:x=y,Πz:code_S1 y,trans (λt:S1.code_S1 t) q (trans (λt:S1.code_S1 t) (inveq q) z)=z)`,
  `s1_trans_ap:=(λx:S1.λy:S1.λp:x=y.ind_eq x (λy':S1.λp':x=y'.Πz:code_S1 x,trans (λt:S1.code_S1 t) p' z=pr0 (id2eqv (ap code_S1 p')) z) (λz:code_S1 x.rfl) y p):(Πx:S1,Πy:S1,Πp:x=y,Πz:code_S1 x,trans (λt:S1.code_S1 t) p z=pr0 (id2eqv (ap code_S1 p)) z)`,
  `s1_code_loop:=(λz:Z.(s1_trans_ap base base loop z)*(happly code_S1_loop z)):(Πz:Z,trans (λt:S1.code_S1 t) loop z=succZ z)`,
  `s1_code_inv_loop:=(λz:Z.((inveq (pred_succZ (trans (λx:S1.code_S1 x) (inveq loop) z)))*(ap predZ ((inveq (s1_code_loop (trans (λx:S1.code_S1 x) (inveq loop) z)))*(s1_trans_inv_r base base loop z))))):(Πz:Z,trans (λx:S1.code_S1 x) (inveq loop) z=predZ z)`,
  `loop_pow_pos_comm:=(ind_nat (λn:nat,loop_pow (pos n)*loop=loop*loop_pow (pos n)) rfl (λn:nat.λih:(loop_pow (pos n)*loop=loop*loop_pow (pos n)).(compeqassoc loop (loop_pow (pos n)) loop)*(ap (λx:base=base.loop*x) ih))):(Πn:nat,loop_pow (pos n)*loop=loop*loop_pow (pos n))`,
  `loop_pow_neg_comm:=(ind_nat (λn:nat,inveq loop*loop_pow (neg n)=loop_pow (neg n)*inveq loop) rfl (λn:nat.λih:(inveq loop*loop_pow (neg n)=loop_pow (neg n)*inveq loop).(ap (λx:base=base.inveq loop*x) ih)*(inveq (compeqassoc (inveq loop) (loop_pow (neg n)) (inveq loop))))):(Πn:nat,inveq loop*loop_pow (neg n)=loop_pow (neg n)*inveq loop)`,
  `loop_pow_pred_right:=(ind_Z (λz:Z,loop_pow (predZ z)*loop=loop_pow z) (leftinveq loop) (ind_nat (λn:nat,loop_pow (predZ (pos n))*loop=loop_pow (pos n)) rfl (λn:nat.λih:(loop_pow (predZ (pos n))*loop=loop_pow (pos n)).loop_pow_pos_comm n)) (ind_nat (λn:nat,loop_pow (predZ (neg n))*loop=loop_pow (neg n)) ((compeqassoc (inveq loop) (inveq loop) loop)*(ap (λx:base=base.(inveq loop)*x) (leftinveq loop))*(rightrfl (inveq loop))) (λn:nat.λih:(loop_pow (predZ (neg n))*loop=loop_pow (neg n)).(compeqassoc (inveq loop) (loop_pow (neg (succ n))) loop)*(ap (λx:base=base.(inveq loop)*x) ih)))):(Πz:Z,loop_pow (predZ z)*loop=loop_pow z)`,
  `s1_decode_loop:=fnext (λz:Z.(s1_trans_apply base base loop loop_pow z)*(s1_trans_base base base loop (loop_pow (trans (λx:S1.code_S1 x) (inveq loop) z)))*(ap (λx:Z.loop_pow x*loop) (s1_code_inv_loop z))*(loop_pow_pred_right z)):(trans (λx:S1,code_S1 x→base=x) loop loop_pow=loop_pow)`,
  `s1_decode_family:=(ind_S1 (λx:S1,code_S1 x→base=x) loop_pow s1_decode_loop):(Πx:S1,code_S1 x→base=x)`,
  `s1_encode_pow:=(ind_Z (λz:Z,trans (λx:S1.code_S1 x) (loop_pow z) 0Z=z) rfl (ind_nat (λn:nat,trans (λx:S1.code_S1 x) (loop_pow (pos n)) 0Z=pos n) (s1_code_loop 0Z) (λn:nat.λih:(trans (λx:S1.code_S1 x) (loop_pow (pos n)) 0Z=pos n).(ap (λq:base=base.trans (λx:S1.code_S1 x) q 0Z) (inveq (loop_pow_pos_comm n)))*(s1_trans_comp base base (loop_pow (pos n)) base loop 0Z)*(ap (λu:Z.trans (λx:S1.code_S1 x) loop u) ih)*(s1_code_loop (pos n)))) (ind_nat (λn:nat,trans (λx:S1.code_S1 x) (loop_pow (neg n)) 0Z=neg n) (s1_code_inv_loop 0Z) (λn:nat.λih:(trans (λx:S1.code_S1 x) (loop_pow (neg n)) 0Z=neg n).(ap (λq:base=base.trans (λx:S1.code_S1 x) q 0Z) (loop_pow_neg_comm n))*(s1_trans_comp base base (loop_pow (neg n)) base (inveq loop) 0Z)*(ap (λu:Z.trans (λx:S1.code_S1 x) (inveq loop) u) ih)*(s1_code_inv_loop (neg n))))):(Πz:Z,trans (λx:S1.code_S1 x) (loop_pow z) 0Z=z)`,
  `s1_encode_decode:=(λz:Z.(inveq (s1_trans_ap base base (loop_pow z) 0Z))*(s1_encode_pow z)):(Πz:Z,pr0 (id2eqv (ap code_S1 (loop_pow z))) 0Z=z)`,
  `s1_decode_encode_family:=(λx:S1.λp:base=x.ind_eq base (λy:S1.λq:base=y,(ind_S1 (λx:S1,code_S1 x→base=x) loop_pow s1_decode_loop) y ((λx:S1.λp:base=x.trans (λx:S1.code_S1 x) p 0Z) y q)=q) rfl x p):(Πx:S1,Πp:base=x,(ind_S1 (λx:S1,code_S1 x→base=x) loop_pow s1_decode_loop) x ((λx:S1.λp:base=x.trans (λx:S1.code_S1 x) p 0Z) x p)=p)`,
  `s1_decode_encode_base:=(λp:base=base.(inveq (s1_decode_encode_family base p))*(ap loop_pow (s1_trans_ap base base p 0Z))):(Πp:base=base,p=loop_pow (pr0 (id2eqv (ap code_S1 p)) 0Z))`,
  `pi1S1:=(pair (λf:(base=base)->Z.((Σg:Z->base=base,Πp:base=base,p=g(f p)) X (Σh:Z->base=base,Πz:Z,z=f(h z)))) (λp:base=base.pr0 (id2eqv (ap code_S1 p)) 0Z) ((pair (λg:Z->base=base,Πp:base=base,p=g(pr0 (id2eqv (ap code_S1 p)) 0Z)) loop_pow s1_decode_encode_base),(pair (λh:Z->base=base,Πz:Z,z=pr0 (id2eqv (ap code_S1 (h z))) 0Z) loop_pow (λz:Z.inveq (s1_encode_decode z))))):(base=base)~=Z`
];

for (const source of sources) {
  const ast = parser.parse(source);
  const result = engine.registerDefinition(ast);
  if (!result.ok) throw new Error(`${source.slice(0, 40)}: ${result.error}`);
  engine.core.state.userDefs[source.split(":=")[0]] = result.filledDefinition;
  console.log(source.split(":=")[0], "OK");
}

console.log("final", engine.check("Πp:base=base,p=loop_pow (pr0 (id2eqv (ap code_S1 p)) 0Z)").ok);
console.log("pi1S1", engine.check("(base=base)~=Z").ok);
