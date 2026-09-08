# Set-Theoretic Induction Playthrough

Status: tactics reach no goals; final bare `qed` fails with
`无法生成匹配intro目标的最短条件演绎规则` at line 72.
The existing page has one premise-free theorem, the successor injection theorem.
No Peano arithmetic induction axiom is used.

Target:

```text
#rp(#nf($0,x),$1,{})>(Vx:(x@omega>(#rp(#nf($0,x),$1,x)>#rp(#nf($0,x),$1,xU{x})))>Vx:(x@omega>#rp(#nf($0,x),$1,x)))
```

Ordinary local specialization of `hs` at `yU{y}` puts that compound term
inside the variable argument of `#nf`. Explicit `a4` instances avoid this
and allow all tactics to validate, but materialization still fails.

```text
intros hbase hstep
have hsepall := .asep #a #b x #rp(#nf($0,x),$1,x)
have hsep := hsepall omega
obtain <#s,hs> := hsep
have hw := domega
have hw0 := hw {}
obtain <hw0o,hw0i> := hw0
have hzero : {}@omega
apply hw0i
intros x hx
obtain <hxzero,hxstep> := hx
exact hxzero
have hs0imp := a4 x ((x@#s)<>((x@omega)&#rp(#nf($0,x),$1,x))) {}
have hs0 := hs0imp hs
obtain <hs0o,hs0i> := hs0
have hszero : {}@#s
apply hs0i
constructor
exact hzero
exact hbase
have hsclosed : Vy:(y@#s>yU{y}@#s)
intros y hy
have hsyimp := a4 x ((x@#s)<>((x@omega)&#rp(#nf($0,x),$1,x))) y
have hsy := hsyimp hs
obtain <hsyo,hsyi> := hsy
have hypair := hsyo hy
obtain <hyomega,hyp> := hypair
have hwy := hw y
obtain <hwyo,hwyi> := hwy
have hyall := hwyo hyomega
have hwsy := hw (yU{y})
obtain <hwsyo,hwsyi> := hwsy
have hsuccomega : yU{y}@omega
apply hwsyi
intros x hx
obtain <hxzero,hxstep> := hx
have hxn := hyall x
have hyinx : y@x
apply hxn
constructor
exact hxzero
exact hxstep
have hxnext := hxstep y
apply hxnext
exact hyinx
have hspimp := a4 x (x@omega>(#rp(#nf($0,x),$1,x)>#rp(#nf($0,x),$1,xU{x}))) y
have hsp := hspimp hstep
specialize hsp hyomega
specialize hsp hyp
have hssimp := a4 x ((x@#s)<>((x@omega)&#rp(#nf($0,x),$1,x))) (yU{y})
have hss := hssimp hs
obtain <hsso,hssi> := hss
apply hssi
constructor
exact hsuccomega
exact hsp
intros x hx
have hwx := hw x
obtain <hwxo,hwxi> := hwx
have hxall := hwxo hx
have hxins := hxall #s
have hxs : x@#s
apply hxins
constructor
exact hszero
exact hsclosed
have hsx := hs x
obtain <hsxo,hsxi> := hsx
have hxpair := hsxo hxs
obtain <hxomega,hxp> := hxpair
exact hxp
qed
```
