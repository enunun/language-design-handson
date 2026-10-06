# 言語仕様書

Miniの構文と意味と型，そしてMiniで成り立つべき性質を定める．

## 構文

式$t$の抽象構文を次のBNFで定める．$n$は自然数を，$x$は変数の名前を表す．

```math
\begin{array}{rcll}
t & ::= & n & \text{数} \\
  & \mid & t + t \mid t - t \mid t * t & \text{算術} \\
  & \mid & \mathsf{true} \mid \mathsf{false} & \text{真偽値} \\
  & \mid & \mathsf{if}\ t\ \mathsf{then}\ t\ \mathsf{else}\ t & \text{条件分岐} \\
  & \mid & \mathsf{iszero}\ t & \text{0かどうかの判定} \\
  & \mid & x & \text{変数} \\
  & \mid & \mathsf{let}\ x = t\ \mathsf{in}\ t & \text{変数の束縛} \\
  & \mid & \mathsf{fun}\ (x : T) \Rightarrow t & \text{関数} \\
  & \mid & t\ t & \text{関数適用} \\
  & \mid & \mathsf{fix}\ f\ (x : T) : T \Rightarrow t & \text{再帰関数}
\end{array}
```

各構文とLeanの`Mini.Term`の構成子は，次のように対応する．

| 構文 | `Term`の構成子 |
| --- | --- |
| $n$ | `num n` |
| $t_1 + t_2$，$t_1 - t_2$，$t_1 * t_2$ | `add t₁ t₂`，`sub t₁ t₂`，`mul t₁ t₂` |
| $\mathsf{true}$，$\mathsf{false}$ | `tru`，`fls` |
| $\mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e$ | `ite c t e` |
| $\mathsf{iszero}\ t$ | `iszero t` |
| $x$ | `var x` |
| $\mathsf{let}\ x = t\ \mathsf{in}\ u$ | `let_ x t u` |
| $\mathsf{fun}\ (x : A) \Rightarrow t$ | `lam x A t` |
| $t\ u$ | `app t u` |
| $\mathsf{fix}\ f\ (x : A) : B \Rightarrow t$ | `fix f x A B t` |

具体構文では，`*`は`+`と`-`より強く結合し，同じ強さの演算子は左から結合する．
関数適用と`iszero`は`*`より強く結合し，関数適用は左から結合する．
`if`の`else`の後の式，`let`の`in`の後の式，`fun`と`fix`の`=>`の後の式は，できるだけ長く読む．
かっこで結合の順序を変えられる．

$\mathsf{let}\ x = t\ \mathsf{in}\ u$と$\mathsf{fun}\ (x : A) \Rightarrow u$は，$u$の中の$x$を束縛する．
$\mathsf{fix}\ f\ (x : A) : B \Rightarrow u$は，$u$の中の$f$と$x$を束縛する．
$u$の中の$f$は，この再帰関数自身を表す．
束縛されていない変数を，自由な変数という．
自由な変数を持たない式を，閉じた式という．

## 値

評価の結果の値$v$は，自然数，真偽値，関数，再帰関数である(`Mini.Value`)．

```math
v ::= n \mid \mathrm{true} \mid \mathrm{false} \mid \mathsf{fun}\ (x : A) \Rightarrow t \mid \mathsf{fix}\ f\ (x : A) : B \Rightarrow t
```

値は，それを表す式と同一視する(`Value.toTerm`)．
プログラムの評価で現れる値を表す式は，閉じている．

### 値を表す式`IsValue`

```math
\frac{}{\mathit{value}(n)}\ \textsf{num}
\qquad
\frac{}{\mathit{value}(\mathsf{true})}\ \textsf{tru}
\qquad
\frac{}{\mathit{value}(\mathsf{false})}\ \textsf{fls}
\qquad
\frac{}{\mathit{value}(\mathsf{fun}\ (x : A) \Rightarrow t)}\ \textsf{lam}
\qquad
\frac{}{\mathit{value}(\mathsf{fix}\ f\ (x : A) : B \Rightarrow t)}\ \textsf{fix}
```

## 意味

### 置換

$t[x := v]$は，式$t$の中の自由な$x$を，すべて$v$で置き換えた式である(`subst x v t`)．

```math
\begin{aligned}
x[x := v] &= v \\
y[x := v] &= y \quad (y \neq x) \\
(\mathsf{let}\ x = t\ \mathsf{in}\ u)[x := v] &= \mathsf{let}\ x = t[x := v]\ \mathsf{in}\ u \\
(\mathsf{let}\ y = t\ \mathsf{in}\ u)[x := v] &= \mathsf{let}\ y = t[x := v]\ \mathsf{in}\ u[x := v] \quad (y \neq x) \\
(\mathsf{fun}\ (x : A) \Rightarrow u)[x := v] &= \mathsf{fun}\ (x : A) \Rightarrow u \\
(\mathsf{fun}\ (y : A) \Rightarrow u)[x := v] &= \mathsf{fun}\ (y : A) \Rightarrow u[x := v] \quad (y \neq x) \\
(\mathsf{fix}\ g\ (y : A) : B \Rightarrow u)[x := v] &= \mathsf{fix}\ g\ (y : A) : B \Rightarrow u \quad (g = x \text{ または } y = x) \\
(\mathsf{fix}\ g\ (y : A) : B \Rightarrow u)[x := v] &= \mathsf{fix}\ g\ (y : A) : B \Rightarrow u[x := v] \quad (g \neq x \text{ かつ } y \neq x)
\end{aligned}
```

- ほかの構文では，すべての部分式を置き換える．
- 置換する式$v$は，閉じた値を表す式に限って使う．そのため，$v$の中の変数が，置換した先の$\mathsf{let}$に束縛されてしまうことはない．

### 大ステップ意味論`Eval`

$t \Downarrow v$は，「式$t$を評価すると値$v$になる」ことを表す．

```math
\frac{}{n \Downarrow n}\ \textsf{num}
\qquad
\frac{t_1 \Downarrow n_1 \quad t_2 \Downarrow n_2}{t_1 + t_2 \Downarrow n_1 + n_2}\ \textsf{add}
\qquad
\frac{t_1 \Downarrow n_1 \quad t_2 \Downarrow n_2}{t_1 - t_2 \Downarrow n_1 \mathbin{\dot{-}} n_2}\ \textsf{sub}
\qquad
\frac{t_1 \Downarrow n_1 \quad t_2 \Downarrow n_2}{t_1 * t_2 \Downarrow n_1 \times n_2}\ \textsf{mul}
```

```math
\frac{}{\mathsf{true} \Downarrow \mathrm{true}}\ \textsf{tru}
\qquad
\frac{}{\mathsf{false} \Downarrow \mathrm{false}}\ \textsf{fls}
\qquad
\frac{t \Downarrow n}{\mathsf{iszero}\ t \Downarrow (n = 0)}\ \textsf{iszero}
```

```math
\frac{c \Downarrow \mathrm{true} \quad t \Downarrow v}{\mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e \Downarrow v}\ \textsf{iteTrue}
\qquad
\frac{c \Downarrow \mathrm{false} \quad e \Downarrow v}{\mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e \Downarrow v}\ \textsf{iteFalse}
```

```math
\frac{t \Downarrow v \quad u[x := v] \Downarrow w}{\mathsf{let}\ x = t\ \mathsf{in}\ u \Downarrow w}\ \textsf{let\_}
```

```math
\frac{}{\mathsf{fun}\ (x : A) \Rightarrow t \Downarrow \mathsf{fun}\ (x : A) \Rightarrow t}\ \textsf{lam}
\qquad
\frac{t_1 \Downarrow \mathsf{fun}\ (x : A) \Rightarrow b \quad t_2 \Downarrow v_2 \quad b[x := v_2] \Downarrow v}{t_1\ t_2 \Downarrow v}\ \textsf{app}
```

```math
\frac{}{\mathsf{fix}\ f\ (x : A) : B \Rightarrow t \Downarrow \mathsf{fix}\ f\ (x : A) : B \Rightarrow t}\ \textsf{fix}
```

```math
\frac{t_1 \Downarrow F \quad t_2 \Downarrow v_2 \quad b[x := v_2][f := F] \Downarrow v}{t_1\ t_2 \Downarrow v}\ \textsf{appFix}
\quad (F = \mathsf{fix}\ f\ (x : A) : B \Rightarrow b)
```

- $\dot{-}$は自然数の引き算で，引く数のほうが大きいときは$0$になる．
- $(n = 0)$は，$n$が$0$なら$\mathrm{true}$，そうでなければ$\mathrm{false}$である．
- 変数を評価する規則はないので，自由な変数を含む式には値がない．
- 再帰関数の適用では，本体の$x$を引数の値で，$f$を再帰関数$F$自身で置き換える．評価が終わらない式には値がない．

### 小ステップ意味論`Step`

$t \longrightarrow t'$は，「式$t$は1ステップで$t'$に簡約される」ことを表す．
演算子の左の部分式を先に，数になるまで簡約する．
`if`は条件だけを先に簡約し，条件が真偽値になってから枝を選ぶ．
`let`は束縛する式を値まで簡約してから，本体の変数をその値で置き換える(値呼び)．
関数適用は，関数と引数を左から順に値まで簡約してから，関数の本体の変数を引数の値で置き換える(値呼び)．
再帰関数の適用では，さらに本体の関数の名前を再帰関数自身で置き換える．

```math
\frac{t_1 \longrightarrow t_1'}{t_1 + t_2 \longrightarrow t_1' + t_2}\ \textsf{addL}
\qquad
\frac{t_2 \longrightarrow t_2'}{n_1 + t_2 \longrightarrow n_1 + t_2'}\ \textsf{addR}
\qquad
\frac{}{n_1 + n_2 \longrightarrow n}\ \textsf{add}\ (n = n_1 + n_2)
```

```math
\frac{t_1 \longrightarrow t_1'}{t_1 - t_2 \longrightarrow t_1' - t_2}\ \textsf{subL}
\qquad
\frac{t_2 \longrightarrow t_2'}{n_1 - t_2 \longrightarrow n_1 - t_2'}\ \textsf{subR}
\qquad
\frac{}{n_1 - n_2 \longrightarrow n}\ \textsf{sub}\ (n = n_1 \mathbin{\dot{-}} n_2)
```

```math
\frac{t_1 \longrightarrow t_1'}{t_1 * t_2 \longrightarrow t_1' * t_2}\ \textsf{mulL}
\qquad
\frac{t_2 \longrightarrow t_2'}{n_1 * t_2 \longrightarrow n_1 * t_2'}\ \textsf{mulR}
\qquad
\frac{}{n_1 * n_2 \longrightarrow n}\ \textsf{mul}\ (n = n_1 \times n_2)
```

```math
\frac{}{\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ t\ \mathsf{else}\ e \longrightarrow t}\ \textsf{iteTrue}
\qquad
\frac{}{\mathsf{if}\ \mathsf{false}\ \mathsf{then}\ t\ \mathsf{else}\ e \longrightarrow e}\ \textsf{iteFalse}
\qquad
\frac{c \longrightarrow c'}{\mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e \longrightarrow \mathsf{if}\ c'\ \mathsf{then}\ t\ \mathsf{else}\ e}\ \textsf{ite}
```

```math
\frac{}{\mathsf{iszero}\ 0 \longrightarrow \mathsf{true}}\ \textsf{iszeroZero}
\qquad
\frac{}{\mathsf{iszero}\ (n + 1) \longrightarrow \mathsf{false}}\ \textsf{iszeroSucc}
\qquad
\frac{t \longrightarrow t'}{\mathsf{iszero}\ t \longrightarrow \mathsf{iszero}\ t'}\ \textsf{iszero}
```

```math
\frac{t \longrightarrow t'}{\mathsf{let}\ x = t\ \mathsf{in}\ u \longrightarrow \mathsf{let}\ x = t'\ \mathsf{in}\ u}\ \textsf{letL}
\qquad
\frac{\mathit{value}(v)}{\mathsf{let}\ x = v\ \mathsf{in}\ u \longrightarrow u[x := v]}\ \textsf{letV}
```

```math
\frac{t_1 \longrightarrow t_1'}{t_1\ t_2 \longrightarrow t_1'\ t_2}\ \textsf{app1}
\qquad
\frac{\mathit{value}(v_1) \quad t_2 \longrightarrow t_2'}{v_1\ t_2 \longrightarrow v_1\ t_2'}\ \textsf{app2}
\qquad
\frac{\mathit{value}(v)}{(\mathsf{fun}\ (x : A) \Rightarrow b)\ v \longrightarrow b[x := v]}\ \textsf{beta}
```

```math
\frac{\mathit{value}(v)}{F\ v \longrightarrow b[x := v][f := F]}\ \textsf{betaFix}
\quad (F = \mathsf{fix}\ f\ (x : A) : B \Rightarrow b)
```

- 規則の中の$n_1$，$n_2$，$n$は数の式である．$\mathsf{iszero}\ (n + 1)$は，$0$でない数の式を表す．
- 関数`step`は，この意味論で1ステップ簡約した式を計算する．

### 多ステップ簡約`Steps`

$t \longrightarrow^{*} t'$は，「式$t$は0ステップ以上で$t'$に簡約される」ことを表す．

```math
\frac{}{t \longrightarrow^{*} t}\ \textsf{refl}
\qquad
\frac{t \longrightarrow t' \quad t' \longrightarrow^{*} t''}{t \longrightarrow^{*} t''}\ \textsf{step}
```

### 正規形と行き詰まった式

- どの規則でも簡約できない式を，正規形という(`Normal`)．
- 正規形だが値を表す式でないものを，行き詰まった式という(`Stuck`)．$1 + \mathsf{true}$，自由な変数$x$，関数でない値の適用$1\ 2$は行き詰まっている．

### 評価器

評価器`eval`は，燃料$k$を受け取り，`step`を最大$k$回繰り返して式を簡約する．
式が値を表す式になったら，その値を返す．
簡約できない式になったら，行き詰まったことを返す．
燃料を使い切ったら，燃料切れを返す．
評価が終わらない式は，どれだけ燃料を与えても燃料切れになる．

## 型

型$T$を次のBNFで定める(`Mini.Ty`)．

```math
T ::= \mathsf{Nat} \mid \mathsf{Bool} \mid T \rightarrow T
```

$A \rightarrow B$は，$A$型の引数を受け取り$B$型の値を返す関数の型である．
$\rightarrow$は右に結合する．

型付け文脈$\Gamma$は，変数とその型の組の列である(`Mini.Ctx`)．
$\Gamma(x)$は，$\Gamma$の中で最も内側に束縛された$x$の型である．

### 型付け規則`HasType`

$\Gamma \vdash t : T$は，「文脈$\Gamma$のもとで，式$t$は型$T$を持つ」ことを表す．

```math
\frac{}{\Gamma \vdash n : \mathsf{Nat}}\ \textsf{num}
\qquad
\frac{\Gamma \vdash t_1 : \mathsf{Nat} \quad \Gamma \vdash t_2 : \mathsf{Nat}}{\Gamma \vdash t_1 + t_2 : \mathsf{Nat}}\ \textsf{add}
\qquad
\frac{\Gamma \vdash t_1 : \mathsf{Nat} \quad \Gamma \vdash t_2 : \mathsf{Nat}}{\Gamma \vdash t_1 - t_2 : \mathsf{Nat}}\ \textsf{sub}
\qquad
\frac{\Gamma \vdash t_1 : \mathsf{Nat} \quad \Gamma \vdash t_2 : \mathsf{Nat}}{\Gamma \vdash t_1 * t_2 : \mathsf{Nat}}\ \textsf{mul}
```

```math
\frac{}{\Gamma \vdash \mathsf{true} : \mathsf{Bool}}\ \textsf{tru}
\qquad
\frac{}{\Gamma \vdash \mathsf{false} : \mathsf{Bool}}\ \textsf{fls}
\qquad
\frac{\Gamma \vdash c : \mathsf{Bool} \quad \Gamma \vdash t : T \quad \Gamma \vdash e : T}{\Gamma \vdash \mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e : T}\ \textsf{ite}
\qquad
\frac{\Gamma \vdash t : \mathsf{Nat}}{\Gamma \vdash \mathsf{iszero}\ t : \mathsf{Bool}}\ \textsf{iszero}
```

```math
\frac{\Gamma(x) = T}{\Gamma \vdash x : T}\ \textsf{var}
\qquad
\frac{\Gamma \vdash t : T \quad (x : T), \Gamma \vdash u : U}{\Gamma \vdash \mathsf{let}\ x = t\ \mathsf{in}\ u : U}\ \textsf{let\_}
```

```math
\frac{(x : A), \Gamma \vdash t : B}{\Gamma \vdash \mathsf{fun}\ (x : A) \Rightarrow t : A \rightarrow B}\ \textsf{lam}
\qquad
\frac{\Gamma \vdash t_1 : A \rightarrow B \quad \Gamma \vdash t_2 : A}{\Gamma \vdash t_1\ t_2 : B}\ \textsf{app}
```

```math
\frac{(x : A), (f : A \rightarrow B), \Gamma \vdash t : B}{\Gamma \vdash \mathsf{fix}\ f\ (x : A) : B \Rightarrow t : A \rightarrow B}\ \textsf{fix}
```

- `if`の2つの枝は，同じ型を持たなければならない．
- 再帰関数の本体は，結果の型の注釈$B$を持たなければならない．本体の型を求める前に$f$の型$A \rightarrow B$が要るので，$B$を注釈で与える．
- $(x : T), \Gamma$は，$\Gamma$の先頭に$x : T$を加えた文脈である．$\Gamma$に同じ名前の変数があれば，それを隠す．
- 型検査器`typeOf`は，この規則で式の型を求める関数である．型が付かないときは，型が合わなかった位置と期待した型と実際の型，定義されていない変数，関数でない式の適用のいずれかを返す．
- プログラムは空の文脈で型を検査し，型の付かない式は評価しない．

## 性質

式$t$と$u$が同じ値に評価される(どちらも値がない場合も含む)とき，$t$と$u$は等価であるという．

- `add_comm`：$t_1 + t_2$と$t_2 + t_1$は等価である．
- `add_assoc`：$(t_1 + t_2) + t_3$と$t_1 + (t_2 + t_3)$は等価である．
- `mul_comm`：$t_1 * t_2$と$t_2 * t_1$は等価である．
- `mul_assoc`：$(t_1 * t_2) * t_3$と$t_1 * (t_2 * t_3)$は等価である．
- `mul_one`：$t$の値が数なら，$t * 1$の値もその数である．
- `mul_one_not_equiv`：$t * 1$と$t$は，等価とは限らない．
- `sub_not_assoc`：$(t_1 - t_2) - t_3$と$t_1 - (t_2 - t_3)$は，等価とは限らない．
- `bigstep_deterministic`：$t \Downarrow v$かつ$t \Downarrow w$ならば$v = w$である(大ステップ意味論の決定性)．
- `num_normal`：数はそれ以上簡約できない．
- `value_normal`：値を表す式は正規形である．
- `step_deterministic`：$t \longrightarrow t_1$かつ$t \longrightarrow t_2$ならば$t_1 = t_2$である(小ステップ意味論の決定性)．
- `stepEager_not_deterministic`：`if`の`then`の枝を条件より先に簡約してもよいとすると，決定性が成り立たない．
- `bigstep_iff_steps`：$t \Downarrow v$と$t \longrightarrow^{*} v$は同値である(2つの意味論の一致)．
- `step_sound`：`step t = some t'`ならば$t \longrightarrow t'$である．
- `step_complete`：$t \longrightarrow t'$ならば`step t = some t'`である．
- `eval_sound`：燃料$k$で`eval`が値$v$を返すならば，$t \Downarrow v$である(評価器の健全性)．
- `eval_complete`：$t \Downarrow v$ならば，ある燃料$k$で`eval`は値$v$を返す(評価器の完全性)．
- `eval_stuck`：`eval`が式$t'$で行き詰まったと返すなら，$t \longrightarrow^{*} t'$であり，$t'$は行き詰まっている．
- `typeOf_sound`：`typeOf Γ t = .ok T`ならば$\Gamma \vdash t : T$である(型検査器の健全性)．
- `typeOf_complete`：$\Gamma \vdash t : T$ならば`typeOf Γ t = .ok T`である(型検査器の完全性)．
- `type_unique`：$\Gamma \vdash t : T$かつ$\Gamma \vdash t : U$ならば$T = U$である(型の一意性)．
- `weaken`：文脈を広げても，型付けは保たれる(弱化)．
- `subst_typing`：文脈$\Gamma$に$x : A$を加えた文脈で$u : B$であり，空の文脈で$v : A$ならば，$\Gamma$のもとで$u[x := v]$も型$B$を持つ(置換補題)．
- `progress`：空の文脈で型の付く式は，値であるか，1ステップ簡約できる(進行)．
- `preservation`：空の文脈で$t : T$かつ$t \longrightarrow t'$ならば$t' : T$である(保存)．
- `type_safety`：空の文脈で型の付く式は，何ステップ簡約しても行き詰まらない(型安全性)．
- `eval_not_stuck`：空の文脈で型の付く式を`eval`で評価しても，行き詰まらない．
- `run_of_eval`：構文解析と型検査と評価に成功した文字列を実行すると，その値が表示される．
- `run_well_typed`：型検査を通った文字列を実行すると，値が表示されるか，燃料切れになる．実行時エラーにはならない．
