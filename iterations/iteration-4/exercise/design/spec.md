# 言語仕様書

Miniの構文と意味，そしてMiniで成り立つべき性質を定める．

## 構文

式$t$の抽象構文を次のBNFで定める．$n$は自然数を表す．

```math
\begin{array}{rcll}
t & ::= & n & \text{数} \\
  & \mid & t + t \mid t - t \mid t * t & \text{算術} \\
  & \mid & \mathsf{true} \mid \mathsf{false} & \text{真偽値} \\
  & \mid & \mathsf{if}\ t\ \mathsf{then}\ t\ \mathsf{else}\ t & \text{条件分岐} \\
  & \mid & \mathsf{iszero}\ t & \text{0かどうかの判定}
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

具体構文では，`*`は`+`と`-`より強く結合し，同じ強さの演算子は左から結合する．
`iszero`は`*`より強く結合する．
`if`の`else`の後の式は，できるだけ長く読む．
かっこで結合の順序を変えられる．

## 値

評価の結果の値$v$は，自然数か真偽値である(`Mini.Value`)．

```math
v ::= n \mid \mathrm{true} \mid \mathrm{false}
```

値は，それを表す式と同一視する(`Value.toTerm`)．
$n$は数の式$n$を，$\mathrm{true}$と$\mathrm{false}$は$\mathsf{true}$と$\mathsf{false}$を表す．

## 意味

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

- $\dot{-}$は自然数の引き算で，引く数のほうが大きいときは$0$になる．
- $(n = 0)$は，$n$が$0$なら$\mathrm{true}$，そうでなければ$\mathrm{false}$である．
- 算術の規則は，部分式の値が数のときだけ使える．$1 + \mathsf{true}$のように規則の当てはまらない式には，値がない．
- 評価器`eval`は，この意味論を計算する関数である．値がない式には`none`を返す．

### 小ステップ意味論`Step`

$t \longrightarrow t'$は，「式$t$は1ステップで$t'$に簡約される」ことを表す．
演算子の左の部分式を先に，数になるまで簡約する．
`if`は条件だけを先に簡約し，条件が真偽値になってから枝を選ぶ．

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
- 正規形だが値を表す式でないものを，行き詰まった式という(`Stuck`)．$1 + \mathsf{true}$や$\mathsf{if}\ 1\ \mathsf{then}\ 2\ \mathsf{else}\ 3$は行き詰まっている．

## 性質

$\mathit{eval}(t) = \mathit{eval}(u)$のとき，式$t$と$u$は等価であるという．
`eval`は大ステップ意味論に従うので，これは2つの式が同じ値に評価されること(値がないことも含めて)と同じである．

- `eval_add_comm`：$t_1 + t_2$と$t_2 + t_1$は等価である．
- `eval_add_assoc`：$(t_1 + t_2) + t_3$と$t_1 + (t_2 + t_3)$は等価である．
- `eval_mul_comm`：$t_1 * t_2$と$t_2 * t_1$は等価である．
- `eval_mul_assoc`：$(t_1 * t_2) * t_3$と$t_1 * (t_2 * t_3)$は等価である．
- `eval_mul_one`：$t$の値が数なら，$t * 1$の値もその数である．
- `eval_mul_one_not_equiv`：$t * 1$と$t$は，等価とは限らない．$\mathsf{true} * 1$には値がない．
- `eval_sub_not_assoc`：$(t_1 - t_2) - t_3$と$t_1 - (t_2 - t_3)$は，等価とは限らない．
- `eval_sound`：`eval t = some v`ならば$t \Downarrow v$である(評価器の健全性)．
- `eval_complete`：$t \Downarrow v$ならば`eval t = some v`である(評価器の完全性)．
- `eval_deterministic`：$t \Downarrow v$かつ$t \Downarrow w$ならば$v = w$である(大ステップ意味論の決定性)．
- `num_normal`：数はそれ以上簡約できない．
- `value_normal`：値を表す式は正規形である．
- `step_deterministic`：$t \longrightarrow t_1$かつ$t \longrightarrow t_2$ならば$t_1 = t_2$である(小ステップ意味論の決定性)．
- `stepEager_not_deterministic`：`if`の`then`の枝を条件より先に簡約してもよいとすると，決定性が成り立たない．
- `bigstep_iff_steps`：$t \Downarrow v$と$t \longrightarrow^{*} v$は同値である(2つの意味論の一致)．
- `step_sound`：`step t = some t'`ならば$t \longrightarrow t'$である．
- `step_complete`：$t \longrightarrow t'$ならば`step t = some t'`である．
- `run_of_eval`：構文解析と評価に成功した文字列を実行すると，その値が表示される．
