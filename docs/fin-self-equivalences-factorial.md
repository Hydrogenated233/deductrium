# Fin 自等价数与阶乘

## 大体思路

目标：

~~~text
Πx:nat,((Fin x)≃(Fin x))≃Fin (factorial x)
~~~

定义：

~~~text
Fin := ind_nat (λn:nat.U) False (λn:nat.λu:U.u+True)
~~~

因此 `Fin 0` 化简为 `False`，`Fin (succ n)` 化简为 `Fin n+True`。令
`Aut A := A≃A`。独立证明采用标准的“最后一个元素”分解：

~~~text
Aut (Fin (succ n)) ≃ Aut (Fin n) × Fin (succ n)
~~~

给 `e : Aut (Fin (succ n))`，取最后点的像 `y := e (inr true)`。构造一个
排列 `moveLast n y` 把 `y` 送到最后点，复合后得到固定最后点的等价；再把它
限制到 `Fin n`。反向是先延拓 `Aut (Fin n)`，再和 `moveLast n y` 的逆复合。

递归尾部：

~~~text
Aut (Fin (succ n))
  ≃ Aut (Fin n) × Fin (succ n)
  ≃ Fin (factorial n) × Fin (succ n)
  ≃ Fin (mul (factorial n) (succ n))
  ≡ Fin (factorial (succ n))
~~~

本稿没有读取、引用或复用 K609 存档中的常量、证明项或命名顺序。

## 录入约定

* 每个定义按本文顺序添加到类型层定理列表。
* `qed name` 使用本文给出的名字。
* `_` 是待推断孔，不是常量名。
* 全部小写的辅助常量名是有意的：当前表面语法中 `eqvLP` 一类名字会被解析器
  拆入语法记号，使用 `eqvlp`、`eqvrp` 更稳定。
* “已复核”表示当前 `TTAssistEngine.qed()` 或带显式类型断言的直接声明已实际
  通过；“待完成”表示数学接口已固定，但不应当宣称为完成的内核证明。
* `fnext` 是游戏内的内置策略和构造，不需要另行假设函数外延公理。

## 引理 1：mkeqv

**说明：** 将正向函数、两套逆函数和两条回转路径封装为 `≃` 记录。

**命题：**

~~~text
Πa:U,Πb:U,Πf:a→b,Πg:b→a,
Πη:Πx:a,x=(g (f x)),Πh:b→a,Πε:Πy:b,y=(f (h y)),a≃b
~~~

**引理 1 证明助手操作序列（已复核）：**

~~~text
intro a
intro b
intro f
intro g
intro η
intro h
intro ε
expand eqv
ex f
constructor
ex g
intro x
exact η x
ex h
intro y
exact ε y
qed mkeqv
~~~

## 引理 2：sigmapath

**说明：** 依赖对的路径构造。若首分量由 p 相等，且沿 p transport 后的
第二分量由 q 相等，就得到整个 Sigma 对相等。后面把 fnext 得到的函数相等提升为
完整等价记录相等时必须用它。

**直接定义（已复核）：**

~~~text
sigmapath:=
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
  x
~~~

**引理 2 证明助手操作序列：**

~~~text
直接声明上述定义。
~~~

## 引理 3：falsefunext

**说明：** 任意两个从空类型出发的函数相等。这里直接使用游戏内的 fnext；
这正是后面压缩 False≃False 全部字段的关键。

**命题：**

~~~text
Πa:U,Πf:False→a,Πg:False→a,f=g
~~~

**引理 3 证明助手操作序列（已复核）：**

~~~text
intro a
intro f
intro g
fnext
intro x
destruct x
qed falsefunext
~~~

## 引理 4：dfalsefunext

**说明：** 上一引理的依赖函数版本。等价记录中的回转路径是依赖函数，
所以不能只保留非依赖的 falsefunext。

**命题：**

~~~text
Πb:False→U,Πf:Πx:False,b x,Πg:Πx:False,b x,f=g
~~~

**引理 4 证明助手操作序列（已复核）：**

~~~text
intro b
intro f
intro g
fnext
intro x
destruct x
qed dfalsefunext
~~~

## 辅助引理 C：一般函数外延

**说明：** 后续证明不能把 `fnext` 当成普通公理常量直接 `exact`；在证明助手
中应先让 `fnext` 把目标变成逐点目标，再逐点给出路径。依赖函数版本使用
完全相同的操作序列。

**非依赖版本（已复核）：**

~~~text
目标：Πa:U,Πb:U,Πf:a→b,Πg:a→b,(Πx:a,f x=g x)→f=g
intro a
intro b
intro f
intro g
intro h
fnext
intro x
exact h x
qed funext
~~~

**依赖版本（已复核）：**

~~~text
目标：Πa:U,Πb:a→U,Πf:Πx:a,b x,Πg:Πx:a,b x,
  (Πx:a,f x=g x)→f=g
intro a
intro b
intro f
intro g
intro h
fnext
intro x
exact h x
qed dfunext
~~~

## 引理 5：空域收缩

**说明：** 把空域函数、空域依赖函数，以及由它们组成的 Sigma / 积类型收缩到
显式中心。contreqvfalse 因而给出 False≃False 的一个中心和从中心到任意
自等价的路径。

**直接定义（已复核；按顺序逐条声明）：**

~~~text
Contr:=λa:U.Σc:a,Πx:a,c=x

emptyfun:=λa:U.λx:False.ind_False (λ_:False.a) x
emptydfun:=λb:False→U.λx:False.ind_False b x

contrfunfalse:=
λa:U.@pair _ _ (False→a)
  (λc:False→a.Πf:False→a,c=f)
  (emptyfun a)
  (λf:False→a.falsefunext a (emptyfun a) f)

contrpifalse:=
λb:False→U.@pair _ _ (Πx:False,b x)
  (λc:Πx:False,b x.Πf:Πx:False,b x,c=f)
  (emptydfun b)
  (λf:Πx:False,b x.dfalsefunext b (emptydfun b) f)

contrsigma:=
λa:U.λb:a→U.λca:Contr a.λcb:Πx:a,Contr (b x).
@pair _ _ (Σx:a,b x)
  (λc:Σx:a,b x.Πz:Σx:a,b x,c=z)
  (@pair _ _ a b (pr0 ca) (pr0 (cb (pr0 ca))))
  (λz:Σx:a,b x.
    sigmapath a b
      (@pair _ _ a b (pr0 ca) (pr0 (cb (pr0 ca)))) z
      (prd1 ca (pr0 z))
      (ind_eq (pr0 ca)
        (λx:a.λq:(pr0 ca)=x.Πy:b x,
          trans b q (pr0 (cb (pr0 ca)))=y)
        (λy:b (pr0 ca).prd1 (cb (pr0 ca)) y)
        (pr0 z) (prd1 ca (pr0 z)) (prd1 z)))

contrprod:=
λa:U.λb:U.λca:Contr a.λcb:Contr b.
contrsigma a (λ_:a.b) ca (λ_:a.cb)

contrpath:=
λa:U.λc:a.λh:Πz:a,c=z.λx:a.λy:a.
@pair _ _ (x=y)
  (λq:x=y.Πp:x=y,q=p)
  ((inveq (h x))▪(h y))
  (λp:x=y.
    ind_eq x
      (λy:a.λp:x=y,((inveq (h x))▪(h y))=p)
      (leftinveq (h x)) y p)

contrtoprop:=
λa:U.λca:Contr a.λx:a.λy:a.
(inveq (prd1 ca x))▪(prd1 ca y)

contrtoset:=
λa:U.λca:isContr a.λx:a.λy:a.
contrtoprop (x=y)
  (contrpath a (pr0 ca) (prd1 ca) x y)

contreqvfalse:=
contrsigma (False→False)
  (λf:False→False.
    (Σg:False→False,Πx:False,x=g (f x))×
    (Σh:False→False,Πx:False,x=f (h x)))
  (contrfunfalse False)
  (λf:False→False.
    contrprod
      (Σg:False→False,Πx:False,x=g (f x))
      (Σh:False→False,Πx:False,x=f (h x))
      (contrsigma (False→False)
        (λg:False→False.Πx:False,x=g (f x))
        (contrfunfalse False)
        (λg:False→False.contrpifalse (λx:False.x=g (f x))))
      (contrsigma (False→False)
        (λh:False→False.Πx:False,x=f (h x))
        (contrfunfalse False)
        (λh:False→False.contrpifalse (λx:False.x=f (h x)))))
  : Contr (False≃False)
~~~

**引理 5 证明助手操作序列：**

~~~text
直接按上述顺序声明。这里的 `fnext` 实际来自引理 3、4，
不要把它们改写成假设的函数外延公理。
~~~

## 引理 6：有限集合上的等价记录外延

**说明：** `a≃b` 不只保存正向函数，还保存两套逆函数和两条回转路径。
因此，两个等价的正向函数逐点相等，并不能直接用一次 `fnext` 得到两个完整
等价记录相等。这里先证明：当 `a`、`b` 都是集合时，给定正向函数后的逆函数
及回转证明构成命题；然后把 `fnext` 得到的正向函数路径提升为完整记录路径。

这是后面 `splitSucc` 两个往返证明的关键压缩步骤。没有它，就必须逐层比较
等价记录中四个证明字段。

**直接定义（已在独立内核会话中逐项复核）：**

~~~text
piprop:=
λa:U.λb:a→U.λhb:Πx:a,isProp (b x).
λf:Πx:a,b x.λg:Πx:a,b x.
fnext (λx:a.hb x (f x) (g x))
: Πa:U,Πb:a→U,(Πx:a,isProp (b x))→isProp (Πx:a,b x)

leftinvprop:=
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
  (Πy:b,y=f(h y))→isProp (Σg:b→a,Πx:a,x=g(f x))

rightinvprop:=
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
  (Πx:a,x=g(f x))→isProp (Σh:b→a,Πy:b,y=f(h y))

eqvdataprop:=
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
  isProp ((Σg:b→a,Πx:a,x=g(f x))×(Σh:b→a,Πy:b,y=f(h y)))

eqvpath:=
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
    (prd1 k))
~~~

**引理 6 证明助手操作序列：**

建议直接按上面的顺序声明。`piprop` 的核心就是 `fnext`；`leftinvprop` 与
`rightinvprop` 先用 `fnext` 比较逆函数，再用 `piprop` 比较回转证明；
`eqvpath` 最后用一次 `sigmapath` 提升正向函数路径。

这里有一个当前表面语法上的注意点：泛型定义内部直接写 `e:a≃b` 可能让旧的
隐式宇宙别名参与推断。上面的 `eqvpath` 故意把 `≃` 的 Sigma 结构写全，调用时
仍可直接传入 `e:a≃b`，二者定义相等。

## 引理 7：等价投影

**说明：** 为嵌套 Sigma 形式的等价记录提供稳定、可读的投影名称。

**直接定义：**

~~~text
eqvf  := λa:U.λb:U.λe:a≃b.pr0 e
eqvl  := λa:U.λb:U.λe:a≃b.pr0 (pr0 (prd1 e))
eqvlp := λa:U.λb:U.λe:a≃b.prd1 (pr0 (prd1 e))
eqvr  := λa:U.λb:U.λe:a≃b.pr0 (pr1 (prd1 e))
eqvrp := λa:U.λb:U.λe:a≃b.prd1 (pr1 (prd1 e))
~~~

**引理 7 证明助手操作序列：**

~~~text
直接逐条声明上述五个定义。
~~~

## 引理 8：eqvcomp

**说明：** 复合 `e:a≃b` 和 `k:b≃c`。正向函数是 `k∘e`；两条回转路径
分别由 `eqvlp` 与 `eqvrp` 加上 `ap` 得到。

**直接定义（已通过带类型断言的直接类型检查）：**

~~~text
eqvcomp :=
  λa:U.λb:U.λc:U.λe:a≃b.λk:b≃c.
  mkeqv a c
    (λx:a.eqvf b c k (eqvf a b e x))
    (λz:c.eqvl a b e (eqvl b c k z))
    (λx:a.(eqvlp a b e x) ▪
      ap (eqvl a b e) (eqvlp b c k (eqvf a b e x)))
    (λz:c.eqvr a b e (eqvr b c k z))
    (λz:c.(eqvrp b c k z) ▪
      ap (eqvf b c k) (eqvrp a b e (eqvr b c k z)))
  : (Πa:U,Πb:U,Πc:U,Πe:a≃b,Πk:b≃c,a≃c)
~~~

**引理 8 证明助手操作序列：**

~~~text
直接声明上述定义。
~~~

## 引理 9：sumcongr

**说明：** 分支地搬运两个等价：`a≃b` 与 `c≃d` 给出 `(a+c)≃(b+d)`。

**命题：**

~~~text
Πa:U,Πb:U,Πc:U,Πd:U,Πe:a≃b,Πk:c≃d,(a+c)≃(b+d)
~~~

**引理 9 证明助手操作序列（已复核）：**

~~~text
intro a
intro b
intro c
intro d
intro e
intro k
expand eqv
ex
intro z
destruct z
left
exact eqvf a b e zl
right
exact eqvf c d k zr
constructor
ex
intro z
destruct z
left
exact eqvl a b e zl
right
exact eqvl c d k zr
intro z
destruct z
apply ap inl
exact eqvlp a b e zl
apply ap inr
exact eqvlp c d k zr
ex
intro z
destruct z
left
exact eqvr a b e zl
right
exact eqvr c d k zr
intro z
destruct z
apply ap inl
exact eqvrp a b e zl
apply ap inr
exact eqvrp c d k zr
qed sumcongr
~~~

## 引理 10：sumfalse

**说明：** `a+False≃a`。正向映射消去右支，逆映射为 `inl`。

**命题：**

~~~text
Πa:U,(a+False)≃a
~~~

**引理 10 证明助手操作序列（已复核）：**

~~~text
intro a
expand eqv
ex
intro z
destruct z
exact zl
destruct zr
constructor
ex
intro x
exact inl x
intro x
destruct x
rfl
exact ind_False _ xr
ex
intro x
exact inl x
intro x
rfl
qed sumfalse
~~~

## 引理 11：sumassoc

**说明：** 三个和类型的重括号，不改变任何元素。

**命题：**

~~~text
Πa:U,Πb:U,Πc:U,(a+(b+c))≃((a+b)+c)
~~~

**引理 11 证明助手操作序列（已复核）：**

~~~text
intro a
intro b
intro c
expand eqv
ex
intro x
destruct x
left
left
exact xl
destruct xr
left
right
exact xrl
right
exact xrr
constructor
ex
intro x
destruct x
destruct xl
left
exact xll
right
left
exact xlr
right
right
exact xr
intro x
destruct x
rfl
destruct xr
rfl
rfl
ex
intro x
destruct x
destruct xl
left
exact xll
right
left
exact xlr
right
right
exact xr
intro x
destruct x
destruct xl
rfl
rfl
rfl
qed sumassoc
~~~

## 引理 12：prodfalse

**说明：** `a×False` 没有元素，因此等价于 `False`。

**命题：**

~~~text
Πa:U,(a×False)≃False
~~~

**引理 12 证明助手操作序列（已复核）：**

~~~text
intro a
expand eqv
ex
intro z
destruct z
exact ind_False _ z1
constructor
ex
intro x
exact ind_False _ x
intro x
destruct x
exact ind_False _ x1
ex
intro x
exact ind_False _ x
intro x
exact ind_False _ x
qed prodfalse
~~~

## 引理 13：prodtrue

**说明：** `a×True` 与 `a` 等价；逆向把 `x` 送到 `(x,true)`。

**命题：**

~~~text
Πa:U,(a×True)≃a
~~~

**引理 13 证明助手操作序列（已复核）：**

~~~text
intro a
expand eqv
ex
intro z
destruct z
exact z0
constructor
ex
intro x
case
exact x
exact true
intro x
destruct x
destruct x1
rfl
ex
intro x
case
exact x
exact true
intro x
rfl
qed prodtrue
~~~

## 引理 14：prodsum

**说明：** 分配律 `a×(b+c)≃(a×b)+(a×c)`。

**命题：**

~~~text
Πa:U,Πb:U,Πc:U,(a×(b+c))≃((a×b)+(a×c))
~~~

**引理 14 证明助手操作序列（已复核）：**

~~~text
intro a
intro b
intro c
expand eqv
ex
intro z
destruct z
destruct z1
left
case
exact z0
exact z1l
right
case
exact z0
exact z1r
constructor
ex
intro z
destruct z
destruct zl
case
exact zl0
left
exact zl1
destruct zr
case
exact zr0
right
exact zr1
intro z
destruct z
destruct z1
rfl
rfl
ex
intro z
destruct z
destruct zl
case
exact zl0
left
exact zl1
destruct zr
case
exact zr0
right
exact zr1
intro z
destruct z
destruct zl
rfl
destruct zr
rfl
qed prodsum
~~~

## 辅助引理 A：Fin 的集合性

**说明：** 后继分解中需要把两个有限等价记录的证明字段视为命题。先对和
类型给出“同支可相等、异支为空”的编码/解码，再归纳得到 `isSet (Fin n)`。
这里的编码不是把等式自动当作 alpha-equivalence，而是显式按 `ind_Sum` 分支
构造。

**直接定义（已复核）：**

~~~text
sumcode:=λa:U.λb:U.λx:a+b.
  ind_Sum (λ_:a+b.(a+b)→U)
    (λu:a.λy:a+b.
      ind_Sum (λ_:a+b.U)
        (λv:a.u=v)
        (λv:b.False)
        y)
    (λu:b.λy:a+b.
      ind_Sum (λ_:a+b.U)
        (λv:a.False)
        (λv:b.u=v)
        y)
    x

sumcoderfl:=λa:U.λb:U.λx:a+b.
  ind_Sum (λz:a+b.sumcode a b z z)
    (λu:a.rfl)
    (λv:b.rfl)
    x

sumencode:=λa:U.λb:U.λx:a+b.λy:a+b.λp:x=y.
  ind_eq x
    (λy:a+b.λp:x=y.sumcode a b x y)
    (sumcoderfl a b x)
    y p

sumdecode:=λa:U.λb:U.λx:a+b.λy:a+b.
  ind_Sum (λx:a+b.Πy:a+b,sumcode a b x y→x=y)
    (λu:a.λy:a+b.
      ind_Sum (λy:a+b.sumcode a b (inl u) y→(inl u)=y)
        (λv:a.λq:u=v.ap inl q)
        (λv:b.λq:False.ind_False (λ_:False.(inl u)=(inr v)) q)
        y)
    (λu:b.λy:a+b.
      ind_Sum (λy:a+b.sumcode a b (inr u) y→(inr u)=y)
        (λv:a.λq:False.ind_False (λ_:False.(inr u)=(inl v)) q)
        (λv:b.λq:u=v.ap inr q)
        y)
    x y

sumdecodeencode:=λa:U.λb:U.λx:a+b.λy:a+b.λp:x=y.
  ind_eq x
    (λy:a+b.λp:x=y.sumdecode a b x y (sumencode a b x y p)=p)
    (ind_Sum (λz:a+b.sumdecode a b z z (sumencode a b z z rfl)=rfl)
      (λu:a.rfl) (λv:b.rfl) x)
    y p

sumencodedecode:=λa:U.λb:U.λx:a+b.
  ind_Sum (λx:a+b.Πy:a+b,Πc:sumcode a b x y,
    sumencode a b x y (sumdecode a b x y c)=c)
    (λu:a.λy:a+b.
      ind_Sum (λy:a+b.Πc:sumcode a b (inl u) y,
        sumencode a b (inl u) y (sumdecode a b (inl u) y c)=c)
        (λv:a.λc:u=v.
          ind_eq u
            (λv:a.λc:u=v.sumencode a b (inl u) (inl v)
              (sumdecode a b (inl u) (inl v) c)=c)
            rfl v c)
        (λv:b.λc:False.ind_False
          (λ_:False.sumencode a b (inl u) (inr v)
            (sumdecode a b (inl u) (inr v) c)=c) c)
        y)
    (λu:b.λy:a+b.
      ind_Sum (λy:a+b.Πc:sumcode a b (inr u) y,
        sumencode a b (inr u) y (sumdecode a b (inr u) y c)=c)
        (λv:a.λc:False.ind_False
          (λ_:False.sumencode a b (inr u) (inl v)
            (sumdecode a b (inr u) (inl v) c)=c) c)
        (λv:b.λc:u=v.
          ind_eq u
            (λv:b.λc:u=v.sumencode a b (inr u) (inr v)
              (sumdecode a b (inr u) (inr v) c)=c)
            rfl v c)
        y)
    x

sumcodeprop:=λa:U.λb:U.λsa:isSet a.λsb:isSet b.
  λx:a+b.λy:a+b.
  ind_Sum (λx:a+b.Πy:a+b,isProp (sumcode a b x y))
    (λu:a.λy:a+b.
      ind_Sum (λy:a+b.isProp (sumcode a b (inl u) y))
        (λv:a.λp:u=v.λq:u=v.sa u v p q)
        (λv:b.λp:False.ind_False (λ_:False.Πq:False,p=q) p)
        y)
    (λu:b.λy:a+b.
      ind_Sum (λy:a+b.isProp (sumcode a b (inr u) y))
        (λv:a.λp:False.ind_False (λ_:False.Πq:False,p=q) p)
        (λv:b.λp:u=v.λq:u=v.sb u v p q)
        y)
    x y

sumset:=λa:U.λb:U.λsa:isSet a.λsb:isSet b.
  λx:a+b.λy:a+b.λp:x=y.λq:x=y.
  ((inveq (sumdecodeencode a b x y p)) ▪
    (ap (sumdecode a b x y)
      (sumcodeprop a b sa sb x y
        (sumencode a b x y p)
        (sumencode a b x y q)))) ▪
    (sumdecodeencode a b x y q)

falseset:=λx:False.
  ind_False (λ_:False.Πy:False,Πp:x=y,Πq:x=y,p=q) x

truecontr:=@pair _ _ True
  (λc:True.Πx:True,c=x)
  true
  (λx:True.ind_True (λx:True.true=x) rfl x)

trueset:=contrtoset True truecontr

finset:=ind_nat (λn:nat.isSet (Fin n))
  falseset
  (λn:nat.λih:isSet (Fin n).
    sumset (Fin n) True ih trueset)
~~~

上面 `falseset`、`truecontr`、`trueset` 和 `finset` 均已逐项通过内核检查。
其中 `trueset` 依赖空域/收缩辅助定义；不要把构造子名称 `pair` 单独当作
`isSet True` 的证明项。

可直接使用下面这个 `trueset` 展开式（若希望不依赖 `contrtoset`）：

~~~text
truecontr:=@pair _ _ True (λc:True.Πx:True,c=x) true
  (λx:True.ind_True (λx:True.true=x) rfl x)
trueset:=contrtoset True truecontr
~~~

**状态：** `sumcode`、`sumencode`、`sumdecode`、两条 round-trip、`sumcodeprop`、
`sumset` 和上述 `finset` 逐项通过内核检查；`finset` 的证明助手序列可按
`intro n`、`induction n with m ih`、分别 `exact falseset`/`exact sumset ...`
录入。`sumset` 的长项建议直接声明，不要在证明助手中逐字符重建。

这个引理的单体证明项约 4.6k 字符。低资源限制下，策略树可无目标但最终
`qed` 仍可能报资源耗尽；提高类型论资源上限后已经通过本地内核复核。

## 引理 15：finstep

**说明：** 这是有限和类型向右增加一个末点的核心构造。若
`e : (a+b)≃d`，它把旧的左、右支嵌入 `a+(b+True)`，并把新 `True`
末点对应到 `d+True` 的新末点，得到
`a+(b+True)≃d+True`。它不使用泛型等价复合，因此避开当前内核对高阶用户
定义应用的不稳定路径。

**命题：**

~~~text
Πa:U,Πb:U,Πd:U,Πe:(a+b)≃d,(a+(b+True))≃(d+True)
~~~

**引理 15 证明助手操作序列（已复核）：**

按以下顺序直接声明；每项的类型断言不能省略。

~~~text
embed:=
λa:U.λb:U.λz:a+b.
  ind_Sum (λ_:a+b.(a+(b+True)))
    (λx:a.inl x)
    (λy:b.inr (inl y)) z
: Πa:U,Πb:U,(a+b)→(a+(b+True))

liftf:=
λa:U.λb:U.λd:U.λf:(a+b)→d.λz:a+(b+True).
  ind_Sum (λ_:a+(b+True).(d+True))
    (λx:a.inl (f (inl x)))
    (λw:b+True.
      ind_Sum (λ_:b+True.(d+True))
        (λy:b.inl (f (inr y)))
        (λt:True.inr t) w) z
: Πa:U,Πb:U,Πd:U,Πf:(a+b)→d,(a+(b+True))→(d+True)

liftg:=
λa:U.λb:U.λd:U.λg:d→a+b.λz:d+True.
  ind_Sum (λ_:d+True.(a+(b+True)))
    (λy:d.embed a b (g y))
    (λt:True.inr (inr t)) z
: Πa:U,Πb:U,Πd:U,Πg:d→(a+b),(d+True)→(a+(b+True))

liftfembed:=
λa:U.λb:U.λd:U.λf:(a+b)→d.λu:a+b.
  ind_Sum (λw:a+b.inl (f w)=liftf a b d f (embed a b w))
    (λx:a.rfl)
    (λy:b.rfl) u
: Πa:U,Πb:U,Πd:U,Πf:(a+b)→d,Πu:a+b,
  inl (f u)=liftf a b d f (embed a b u)

liftroundl:=
λa:U.λb:U.λd:U.λf:(a+b)→d.λg:d→a+b.
λp:Πu:a+b,u=(g(f u)).λz:a+(b+True).
  ind_Sum (λw:a+(b+True).w=liftg a b d g (liftf a b d f w))
    (λx:a.ap (embed a b) (p (inl x)))
    (λw:b+True.
      ind_Sum
        (λt:b+True.inr t=liftg a b d g (liftf a b d f (inr t)))
        (λy:b.ap (embed a b) (p (inr y)))
        (λt:True.rfl) w) z
: Πa:U,Πb:U,Πd:U,Πf:(a+b)→d,Πg:d→(a+b),
  Πp:Πu:a+b,u=(g(f u)),Πz:a+(b+True),
  z=liftg a b d g (liftf a b d f z)

liftroundr:=
λa:U.λb:U.λd:U.λf:(a+b)→d.λg:d→a+b.
λq:Πv:d,v=(f(g v)).λz:d+True.
  ind_Sum (λw:d+True.w=liftf a b d f (liftg a b d g w))
    (λv:d.(ap inl (q v))▪(liftfembed a b d f (g v)))
    (λt:True.rfl) z
: Πa:U,Πb:U,Πd:U,Πf:(a+b)→d,Πg:d→(a+b),
  Πq:Πv:d,v=(f(g v)),Πz:d+True,
  z=liftf a b d f (liftg a b d g z)

finstep:=
λa:U.λb:U.λd:U.λe:(a+b)≃d.
  mkeqv (a+(b+True)) (d+True)
    (liftf a b d (eqvf (a+b) d e))
    (liftg a b d (eqvl (a+b) d e))
    (liftroundl a b d
      (eqvf (a+b) d e)
      (eqvl (a+b) d e)
      (eqvlp (a+b) d e))
    (liftg a b d (eqvr (a+b) d e))
    (liftroundr a b d
      (eqvf (a+b) d e)
      (eqvr (a+b) d e)
      (eqvrp (a+b) d e))
: Πa:U,Πb:U,Πd:U,Πe:(a+b)≃d,(a+(b+True))≃(d+True)
~~~

`liftroundl` 的内层归纳动机必须写成
`inr t = liftg ... (inr t)`；若误写成 `t = ...`，两边分别属于 `True` 和
和类型，内核会正确报“函数作用类型不匹配”。

## 引理 16：finadd

**说明：** 对第二个自然数归纳。基例是 `a+0=a`；后继步调用刚才的
`finstep`，而 `Fin (succ n)` 与 `Fin n+True`、
`Fin (succ (add a n))` 与 `Fin (add a n)+True` 都按定义化简。

**命题：**

~~~text
Πa:nat,Πb:nat,(Fin a+Fin b)≃Fin (add a b)
~~~

**引理 16 证明助手操作序列（已复核）：**

~~~text
finadd:=
λa:nat.
  ind_nat (λb:nat.(Fin a+Fin b)≃Fin (add a b))
    (sumfalse (Fin a))
    (λn:nat.λih:(Fin a+Fin n)≃Fin (add a n).
      finstep (Fin a) (Fin n) (Fin (add a n)) ih)
: Πa:nat,Πb:nat,(Fin a+Fin b)≃Fin (add a b)
~~~

上面七项在空白的新 `TTCoreSession` 内按顺序注册，均返回 `ok:true`，
定义缓存为 `nbe`。

## 引理 17：prodcongr

**说明：** 两个等价逐分量作用在乘积上。最初的草稿手工构造乘积的正向、
逆向函数，再用 `sigmapath` 比较依赖对；这条路线虽然可行，但会制造一个很长的
transport 证明。这里改用游戏内已有的单值公理：先用 `ua` 把两个等价变为类型
相等，对乘积类型构造分别取 `ap`，复合两条类型路径后用 `id2eqv` 转回等价。

**命题：**

~~~text
Πa:U,Πb:U,Πc:U,Πd:U,Πe:a≃b,Πk:c≃d,(a×c)≃(b×d)
~~~

**直接定义（已在独立内核会话中复核）：**

~~~text
prodcongr:=
λa:U.λb:U.λc:U.λd:U.λe:a≃b.λk:c≃d.
  id2eqv
    ((ap (λx:U.x×c) (ua e))▪
     (ap (λx:U.b×x) (ua k)))
: Πa:U,Πb:U,Πc:U,Πd:U,
  (a≃b)→(c≃d)→((a×c)≃(b×d))
~~~

**引理 17 证明助手操作序列：**

~~~text
直接声明上述定义。
~~~

这一定义没有借用 K609 的任何排列编码。它只使用 `ua`、`ap`、路径复合和
`id2eqv`，并已在当前工作区的空白 `TTCoreEngine` 中返回 `ok:true`。

## 引理 18：finmul

**说明：** 这是有限积的基数同构。对第二个自然数归纳：Fin a×Fin 0 是空型；后继步先把乘积对和分配，再把归纳假设和 Fin a×True≃Fin a 分别作用到两个和支，最后用 finadd 收束。

**命题：**

~~~text
Πa:nat,Πb:nat,(Fin a×Fin b)≃Fin (mul a b)
~~~

**引理 18 证明助手操作序列（已复核）：**

按以下顺序直接声明。finmulcongr 的第一个参数必须是 Fin a×Fin n，不能误写为 Fin a。

~~~text
finmuldistrib:=
λa:nat.λn:nat.λih:(Fin a×Fin n)≃Fin (mul a n).
  prodsum (Fin a) (Fin n) True
: Πa:nat,Πn:nat,((Fin a×Fin n)≃Fin (mul a n))→
  (Fin a×(Fin n+True))≃((Fin a×Fin n)+(Fin a×True))

finmulcongr:=
λa:nat.λn:nat.λih:(Fin a×Fin n)≃Fin (mul a n).
  sumcongr (Fin a×Fin n) (Fin (mul a n))
    (Fin a×True) (Fin a) ih (prodtrue (Fin a))
: Πa:nat,Πn:nat,Πih:(Fin a×Fin n)≃Fin (mul a n),
  ((Fin a×Fin n)+(Fin a×True))≃(Fin (mul a n)+Fin a)

finmulmiddle:=
λa:nat.λn:nat.λih:(Fin a×Fin n)≃Fin (mul a n).
  eqvcomp (Fin a×(Fin n+True))
    ((Fin a×Fin n)+(Fin a×True))
    (Fin (mul a n)+Fin a)
    (finmuldistrib a n ih)
    (finmulcongr a n ih)
: Πa:nat,Πn:nat,Πih:(Fin a×Fin n)≃Fin (mul a n),
  (Fin a×(Fin n+True))≃(Fin (mul a n)+Fin a)

finmulstep:=
λa:nat.λn:nat.λih:(Fin a×Fin n)≃Fin (mul a n).
  eqvcomp (Fin a×(Fin n+True))
    (Fin (mul a n)+Fin a)
    (Fin (add (mul a n) a))
    (finmulmiddle a n ih)
    (finadd (mul a n) a)
: Πa:nat,Πn:nat,Πih:(Fin a×Fin n)≃Fin (mul a n),
  (Fin a×(Fin n+True))≃Fin (add (mul a n) a)

finmul:=
λa:nat.
  ind_nat (λb:nat.(Fin a×Fin b)≃Fin (mul a b))
    (prodfalse (Fin a))
    (λn:nat.λih:(Fin a×Fin n)≃Fin (mul a n).
      finmulstep a n ih)
: Πa:nat,Πb:nat,(Fin a×Fin b)≃Fin (mul a b)
~~~

本组在持久 NbE 会话中逐项通过；finmul 是后续阶乘归纳使用的有限乘法接口。

## 辅助引理 B：末点交换与 moveLast

**说明：** 对 y:Fin(succ n) 构造真正自逆的排列 movelast n y。它把 y 送到末点 inr true，同时把末点送回 y。后继步把归纳得到的交换扩张一层，再交换最外面的两个末点。

**命题：**

~~~text
Πn:nat,Πy:Fin(succ n),Fin(succ n)≃Fin(succ n)
~~~

**引理 19 证明助手操作序列（已复核）：**

直接按顺序声明下面定义。conjself 是两个自逆函数的共轭仍自逆的路径；其类型由系统推断，不要改写其括号结构。

~~~text
extendlast:=
λa:U.λf:a→a.λz:a+True.
  ind_Sum (λ_:a+True.a+True)
    (λx:a.inl (f x))
    (λt:True.inr t) z
: Πa:U,Πf:a→a,(a+True)→(a+True)

extendlastself:=
λa:U.λf:a→a.λh:Πx:a,x=f(f x).λz:a+True.
  ind_Sum (λw:a+True.w=extendlast a f (extendlast a f w))
    (λx:a.ap inl (h x))
    (λt:True.rfl) z
: Πa:U,Πf:a→a,(Πx:a,x=f(f x))→Πz:a+True,
  z=extendlast a f (extendlast a f z)

swap2fn:=
λa:U.λz:(a+True)+True.
  ind_Sum (λ_:((a+True)+True).((a+True)+True))
    (λu:a+True.
      ind_Sum (λ_:a+True.((a+True)+True))
        (λx:a.inl (inl x))
        (λt:True.inr true) u)
    (λt:True.inl (inr true)) z
: Πa:U,((a+True)+True)→((a+True)+True)

swap2self:=
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
: Πa:U,Πz:(a+True)+True,z=swap2fn a (swap2fn a z)

conjself:=
λa:U.λf:a→a.λg:a→a.
λhf:Πz:a,z=f(f z).λhg:Πz:a,z=g(g z).λz:a.
  ((hf z)▪(ap f (hg (f z))))▪
  (ap (λw:a.f(g w)) (hf (g(f z))))

swaplast:=
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
: Πn:nat,Fin(succ n)→Fin(succ n)→Fin(succ n)

swaplastself:=
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
  z=swaplast n y (swaplast n y z)

swaplastpoint:=
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
: Πn:nat,Πy:Fin(succ n),swaplast n y y=inr true

swaplastlast:=
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
: Πn:nat,Πy:Fin(succ n),swaplast n y (inr true)=y

movelast:=
λn:nat.λy:Fin(succ n).
  mkeqv (Fin(succ n)) (Fin(succ n))
    (swaplast n y)
    (swaplast n y) (swaplastself n y)
    (swaplast n y) (swaplastself n y)
: Πn:nat,Πy:Fin(succ n),Fin(succ n)≃Fin(succ n)

movelastpoint:=
λn:nat.λy:Fin(succ n).swaplastpoint n y
: Πn:nat,Πy:Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n)) (movelast n y) y=inr true

movelastlast:=
λn:nat.λy:Fin(succ n).swaplastlast n y
: Πn:nat,Πy:Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n)) (movelast n y) (inr true)=y
~~~

因此可直接使用 movelastpoint n y 和 movelastlast n y 这两条计算式；它们与 swaplastself 都已经在同一内核会话中验证。

## 辅助引理 D：固定末点的限制与延拓

**说明：** restrictfixed 把固定末点的 a+True 自等价限制为 a 的自等价。核心是先证明左注入的像不可能落在末点，再用 droplast 取回左支。反向的 extendfixed 逐支作用于 a 并固定 True。restrictextendfwd 和 extendrestrictfwd 是两个正向计算规则。

**接口：**

~~~text
extendfixed : Πa:U,(a≃a)→((a+True)≃(a+True))
restrictfixed :
  Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,a≃a
~~~

**引理 20 证明助手操作序列（已复核）：**

前文的 sumcode、sumencode、eqvf、eqvl、eqvlp、eqvr、eqvrp 与 mkeqv 已存在时，按下列顺序直接声明：

~~~text
notinlr:=
λa:U.λx:a.λp:inl x=inr true.
  ind_False (λ_:False.False)
    (sumencode a True (inl x) (inr true) p)
: Πa:U,Πx:a,not (inl x=inr true)

droplast:=
λa:U.λz:a+True.
  ind_Sum
    (λz:a+True,not (z=inr true)→a)
    (λx:a.λp:not (inl x=inr true).x)
    (λt:True.λp:not (inr t=inr true).
      ind_False (λ_:False.a)
        (p (ind_True (λt:True,inr t=inr true) rfl t)))
    z
: Πa:U,Πz:a+True,not (z=inr true)→a

droplast_round:=
λa:U.λz:a+True.
  ind_Sum
    (λz:a+True,Πp:not (z=inr true),inl (droplast a z p)=z)
    (λx:a.λp:not (inl x=inr true).rfl)
    (λt:True.λp:not (inr t=inr true).
      ind_False
        (λ_:False,inl (droplast a (inr t) p)=inr t)
        (p (ind_True (λt:True,inr t=inr true) rfl t)))
    z
: Πa:U,Πz:a+True,Πp:not (z=inr true),inl (droplast a z p)=z

inlinj:=
λa:U.λx:a.λy:a.λp:inl x=inl y.
  sumencode a True (inl x) (inl y) p
: Πa:U,Πx:a,Πy:a,(inl x=inl y)→x=y

invagree:=
λa:U.λb:U.λe:a≃b.λy:b.
  (ap (eqvl a b e) (eqvrp a b e y))▪
  (inveq (eqvlp a b e (eqvr a b e y)))
: Πa:U,Πb:U,Πe:a≃b,Πy:b,eqvl a b e y=eqvr a b e y

eqvlright:=
λa:U.λb:U.λe:a≃b.λy:b.
  (eqvrp a b e y)▪
  (ap (eqvf a b e) (inveq (invagree a b e y)))
: Πa:U,Πb:U,Πe:a≃b,Πy:b,y=eqvf a b e (eqvl a b e y)

fwdnotlast:=
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
  Πx:a,not (eqvf (a+True) (a+True) e (inl x)=inr true)

leftnotlast:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λx:a.λq:eqvl (a+True) (a+True) e (inl x)=inr true.
  notinlr a x
    ((eqvlright (a+True) (a+True) e (inl x))▪
      (ap (eqvf (a+True) (a+True) e) q)▪p)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,
  Πx:a,not (eqvl (a+True) (a+True) e (inl x)=inr true)

rightnotlast:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λx:a.λq:eqvr (a+True) (a+True) e (inl x)=inr true.
  notinlr a x
    ((eqvrp (a+True) (a+True) e (inl x))▪
      (ap (eqvf (a+True) (a+True) e) q)▪p)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,
  Πx:a,not (eqvr (a+True) (a+True) e (inl x)=inr true)

rfwd:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λx:a.droplast a
  (eqvf (a+True) (a+True) e (inl x))
  (fwdnotlast a e p x)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,Πx:a,a

rleft:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λy:a.droplast a
  (eqvl (a+True) (a+True) e (inl y))
  (leftnotlast a e p y)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,Πy:a,a

rright:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
λy:a.droplast a
  (eqvr (a+True) (a+True) e (inl y))
  (rightnotlast a e p y)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,Πy:a,a

extendfixed:=
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
: Πa:U,(a≃a)→((a+True)≃(a+True))

extendfixedfwd:=
λa:U.λe:a≃a.λx:a.rfl
: Πa:U,Πe:a≃a,Πx:a,
  eqvf (a+True) (a+True) (extendfixed a e) (inl x)=
    inl (eqvf a a e x)

extendfixedlast:=
λa:U.λe:a≃a.rfl
: Πa:U,Πe:a≃a,
  eqvf (a+True) (a+True) (extendfixed a e) (inr true)=inr true

restrictextendfwd:=
λa:U.λe:a≃a.λx:a.rfl
: Πa:U,Πe:a≃a,Πx:a,
  rfwd a (extendfixed a e) (extendfixedlast a e) x=eqvf a a e x

rleftp:=
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
  Πx:a,x=rleft a e p (rfwd a e p x)

rrightp:=
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
  Πy:a,y=rfwd a e p (rright a e p y)

restrictfixed:=
λa:U.λe:(a+True)≃(a+True).
λp:eqvf (a+True) (a+True) e (inr true)=inr true.
  mkeqv a a
    (rfwd a e p)
    (rleft a e p)
    (rleftp a e p)
    (rright a e p)
    (rrightp a e p)
: Πa:U,Πe:(a+True)≃(a+True),
  Πp:eqvf (a+True) (a+True) e (inr true)=inr true,a≃a
~~~

droplast 的动机必须依赖于不等于末点的证明；把该证明放在 ind_Sum 之外会得到错误的非依赖 eliminator 类型。

## 引理 21：splitSucc

**说明：** 这是排列分解主体：Aut(Fin(succ n))≃Aut(Fin n)×Fin(succ n)。对 e，先记录 e(last)，再以 moveLast 右复合，把这个像送回 last，得到固定末点的等价并限制到 Fin n。反向则先延拓小排列，再用同一个自逆 moveLast 左复合。两边完整等价记录路径通过 eqvpath 和 finset 收束；乘积对的最后路径使用专门的 prodpath，避免不必要的 dependent transport 展开。

**命题：**

~~~text
Πn:nat,(Fin(succ n)≃Fin(succ n))
  ≃ ((Fin n≃Fin n)×Fin(succ n))
~~~

**引理 21 证明助手操作序列（已复核）：**

直接按顺序声明。这里引用前文已验证的 eqvpath、finset、mkeqv 与本节的 restrictfixed、extendfixed。

~~~text
pack:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  @pair _ _ (Fin n≃Fin n)
    (λ_:Fin n≃Fin n.Fin(succ n)) u y
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  ((Fin n≃Fin n)×Fin(succ n))

corrected:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  eqvcomp (Fin(succ n)) (Fin(succ n)) (Fin(succ n)) e
    (movelast n
      (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true)) )
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  Fin(succ n)≃Fin(succ n)

correctedfix:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  movelastpoint n
    (eqvf (Fin(succ n)) (Fin(succ n)) e (inr true))
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n)) (corrected n e)
    (inr true)=inr true

extendrestrictfwd:=
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
  eqvf (a+True) (a+True) e z

round1c:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  corrected n (splitinv n (pack n u y))
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  Fin(succ n)≃Fin(succ n)

round1cp:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  correctedfix n (splitinv n (pack n u y))
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  eqvf (Fin(succ n)) (Fin(succ n)) (round1c n u y)
    (inr true)=inr true

round1mid:=
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
  inl (eqvf (Fin n) (Fin n) u x)

round1fwdcore:=
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
  eqvf (Fin n) (Fin n) u x

splitround1fwd:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).λx:Fin n.
  round1fwdcore n u y x
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),Πx:Fin n,
  eqvf (Fin n) (Fin n)
    (pr0 (splitfwd n (splitinv n (pack n u y)))) x=
  eqvf (Fin n) (Fin n) u x

splitround1eqv:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  eqvpath (Fin n) (Fin n) (finset n) (finset n)
    (pr0 (splitfwd n (splitinv n (pack n u y)))) u
    (fnext (splitround1fwd n u y))
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  pr0 (splitfwd n (splitinv n (pack n u y)))=u

prodpath:=
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
  (@pair _ _ a (λ_:a.b) x y=@pair _ _ a (λ_:a.b) x' y')

splitround1:=
λn:nat.λu:Fin n≃Fin n.λy:Fin(succ n).
  prodpath (Fin n≃Fin n) (Fin(succ n))
    (pr0 (splitfwd n (splitinv n (pack n u y)))) u
    (prd1 (splitfwd n (splitinv n (pack n u y)))) y
    (splitround1eqv n u y)
    ((splitfwdsecond n (splitinv n (pack n u y)))▪
      (splitinvlast n (pack n u y)))
: Πn:nat,Πu:Fin n≃Fin n,Πy:Fin(succ n),
  splitfwd n (splitinv n (pack n u y))=pack n u y

splitround2fwd:=
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
  eqvf (Fin(succ n)) (Fin(succ n)) e z

splitround2:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  eqvpath (Fin(succ n)) (Fin(succ n))
    (finset (succ n)) (finset (succ n))
    (splitinv n (splitfwd n e)) e
    (fnext (splitround2fwd n e))
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  splitinv n (splitfwd n e)=e

spliteta:=
λn:nat.λe:Fin(succ n)≃Fin(succ n).
  inveq (splitround2 n e)
: Πn:nat,Πe:Fin(succ n)≃Fin(succ n),
  e=splitinv n (splitfwd n e)

splitepsilon:=
λn:nat.λz:((Fin n≃Fin n)×Fin(succ n)).
  ind_Prod (λ_:Fin n≃Fin n.Fin(succ n))
    (λz:((Fin n≃Fin n)×Fin(succ n)).
      z=splitfwd n (splitinv n z))
    (λu:Fin n≃Fin n.λy:Fin(succ n).
      inveq (splitround1 n u y)) z
: Πn:nat,Πz:((Fin n≃Fin n)×Fin(succ n)),
  z=splitfwd n (splitinv n z)

splitsucc:=
λn:nat.
  mkeqv (Fin(succ n)≃Fin(succ n))
    ((Fin n≃Fin n)×Fin(succ n))
    (λe:Fin(succ n)≃Fin(succ n).splitfwd n e)
    (λz:((Fin n≃Fin n)×Fin(succ n)).splitinv n z)
    (spliteta n)
    (λz:((Fin n≃Fin n)×Fin(succ n)).splitinv n z)
    (splitepsilon n)
: Πn:nat,(Fin(succ n)≃Fin(succ n))≃
  ((Fin n≃Fin n)×Fin(succ n))
~~~

splitround1 的方向是 splitfwd(splitinv z)=z。封装为 mkeqv 时，右回转字段使用 inveq splitround1，左回转字段使用 inveq splitround2；方向颠倒会报函数作用类型不匹配。

## 引理 22：autbase

**说明：** Fin 0=False，而 Fin(factorial 0)=Fin 1=False+True。False≃False 的正向函数空间可由空域外延压缩；这里用有限集合等价记录外延给出短基例。

**引理 22 证明助手操作序列（已复核）：**

~~~text
autfalsecenter:=
λe:False≃False.
  eqvpath False False falseset falseset e (eqvrefl False)
    (fnext (λx:False.
      ind_False (λ_:False.
        eqvf False False e x=x) x))
: Πe:False≃False,e=eqvrefl False

autbase:=
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
: (Fin 0≃Fin 0)≃Fin(factorial 0)
~~~

## 定理：finAutFactorial

**说明：** 对自然数归纳。基例用 autbase；后继步依次做 splitsucc、归纳假设作用到乘积第一个分量、finmul，再用 id2eqv 与 factorialsucc 把 Fin(mul (factorial n) (succ n)) 改写为 Fin(factorial(succ n))。当前内核不会总在泛型声明边界自动把 factorial(succ n) delta 化简，所以 factorialsucc 必须显式保留。

**待证命题：**

~~~text
Πx:nat,((Fin x)≃(Fin x))≃Fin(factorial x)
~~~

**定理证明助手操作序列（已复核）：**

按以下顺序直接声明：

~~~text
factorialsucc:=
λn:nat.rfl
: Πn:nat,factorial(succ n)=mul (factorial n) (succ n)

finautprod:=
λn:nat.λih:(Fin n≃Fin n)≃Fin(factorial n).
  id2eqv
    ((ap (λx:U.x×Fin(succ n)) (ua ih))▪
     (ap (λx:U.Fin(factorial n)×x)
       (ua (eqvrefl (Fin(succ n))))) )
: Πn:nat,Πih:(Fin n≃Fin n)≃Fin(factorial n),
  ((Fin n≃Fin n)×Fin(succ n))≃
  (Fin(factorial n)×Fin(succ n))

finautmul:=
λn:nat.finmul (factorial n) (succ n)
: Πn:nat,(Fin(factorial n)×Fin(succ n))≃
  Fin(mul (factorial n) (succ n))

finautfact:=
λn:nat.id2eqv (ap Fin (inveq (factorialsucc n)))
: Πn:nat,Fin(mul (factorial n) (succ n))≃
  Fin(factorial(succ n))

finautmiddle:=
λn:nat.λih:(Fin n≃Fin n)≃Fin(factorial n).
  eqvcomp ((Fin n≃Fin n)×Fin(succ n))
    (Fin(factorial n)×Fin(succ n))
    (Fin(mul (factorial n) (succ n)))
    (finautprod n ih)
    (finautmul n)
: Πn:nat,Πih:(Fin n≃Fin n)≃Fin(factorial n),
  ((Fin n≃Fin n)×Fin(succ n))≃
  Fin(mul (factorial n) (succ n))

finautright:=
λn:nat.λih:(Fin n≃Fin n)≃Fin(factorial n).
  eqvcomp ((Fin n≃Fin n)×Fin(succ n))
    (Fin(mul (factorial n) (succ n)))
    (Fin(factorial(succ n)))
    (finautmiddle n ih)
    (finautfact n)
: Πn:nat,Πih:(Fin n≃Fin n)≃Fin(factorial n),
  ((Fin n≃Fin n)×Fin(succ n))≃
  Fin(factorial(succ n))

finautstep:=
λn:nat.λih:(Fin n≃Fin n)≃Fin(factorial n).
  eqvcomp (Fin(succ n)≃Fin(succ n))
    ((Fin n≃Fin n)×Fin(succ n))
    (Fin(factorial(succ n)))
    (splitsucc n)
    (finautright n ih)
: Πn:nat,((Fin n≃Fin n)≃Fin(factorial n))→
  ((Fin(succ n)≃Fin(succ n))≃Fin(factorial(succ n)))

finAutFactorial:=
ind_nat (λx:nat.(Fin x≃Fin x)≃Fin(factorial x))
  autbase
  finautstep
: Πx:nat,((Fin x)≃(Fin x))≃Fin(factorial x)
~~~

## 当前状态

本文已经完成并通过独立验证。运行：

~~~text
node work/verify-splitsucc.mjs
~~~

该脚本在一个持续的 TTCoreSession 中按声明顺序注册 113 项定义：有限集合性、moveLast、restrictfixed、splitSucc、有限乘法、基例和最终归纳项均返回 ok=true，最终 finAutFactorial 也返回 ok=true。本文没有读取、引用或复用 K609 存档中的常量、证明项或命名顺序。
