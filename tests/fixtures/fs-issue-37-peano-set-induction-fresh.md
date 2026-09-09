# Issue 37: Fresh Closure Variable

Reported on 2026-09-09 after 6f3efe8. All 74 tactics complete, but bare
qed fails during conditional materialization. Keep the schematic constraints
and the explicit .Vcn conversion; do not use .pn5 or apn5 to prove the target.

```text
#rp(#nf($0,x),$1,{})>(Vx:(x@omega>(#rp(#nf($0,x),$1,x)>#rp(#nf($0,x),$1,xU{x})))>Vx:(x@omega>#rp(#nf($0,x),$1,x)))
```

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
have hsclosedFresh : V#n:(#n@#s>#nU{#n}@#s)
intros #n hy
have hsyimp := a4 x ((x@#s)<>((x@omega)&#rp(#nf($0,x),$1,x))) #n
have hsy := hsyimp hs
obtain <hsyo,hsyi> := hsy
have hypair := hsyo hy
obtain <hyomega,hyp> := hypair
have hwy := hw #n
obtain <hwyo,hwyi> := hwy
have hyall := hwyo hyomega
have hwsy := hw (#nU{#n})
obtain <hwsyo,hwsyi> := hwsy
have hsuccomega : #nU{#n}@omega
apply hwsyi
intros x hx
obtain <hxzero,hxstep> := hx
have hxn := hyall x
have hyinx : #n@x
apply hxn
constructor
exact hxzero
exact hxstep
have hxnext := hxstep #n
apply hxnext
exact hyinx
have hspimp := a4 x (x@omega>(#rp(#nf($0,x),$1,x)>#rp(#nf($0,x),$1,xU{x}))) #n
have hsp := hspimp hstep
specialize hsp hyomega
specialize hsp hyp
have hssimp := a4 x ((x@#s)<>((x@omega)&#rp(#nf($0,x),$1,x))) (#nU{#n})
have hss := hssimp hs
obtain <hsso,hssi> := hss
apply hssi
constructor
exact hsuccomega
exact hsp
have hsclosed : Vy:(y@#s>yU{y}@#s)
apply .Vcn $x=#n $1=(#n@#s>#nU{#n}@#s) $z=y
exact hsclosedFresh
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
