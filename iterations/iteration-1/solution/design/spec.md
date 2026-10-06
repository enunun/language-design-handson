# 言語仕様書

Miniの構文と意味，そしてMiniで成り立つべき性質を定める．

## 構文

式$t$の抽象構文を次のBNFで定める．$n$は自然数を表す．

```math
\begin{array}{rcll}
t & ::= & n & \text{数} \\
  & \mid & t + t & \text{足し算} \\
  & \mid & t - t & \text{引き算} \\
  & \mid & t * t & \text{掛け算}
\end{array}
```

各構文とLeanの`Mini.Term`の構成子は，次のように対応する．

| 構文 | `Term`の構成子 |
| --- | --- |
| $n$ | `num n` |
| $t_1 + t_2$ | `add t₁ t₂` |
| $t_1 - t_2$ | `sub t₁ t₂` |
| $t_1 * t_2$ | `mul t₁ t₂` |

具体構文では，`*`は`+`と`-`より強く結合し，同じ強さの演算子は左から結合する．
かっこで結合の順序を変えられる．

## 意味

### 大ステップ意味論`Eval`

$t \Downarrow n$は，「式$t$を評価すると自然数$n$になる」ことを表す．
次の推論規則で定める．

```math
\frac{}{n \Downarrow n}\ \textsf{num}
\qquad
\frac{t_1 \Downarrow n_1 \quad t_2 \Downarrow n_2}{t_1 + t_2 \Downarrow n_1 + n_2}\ \textsf{add}
```

```math
\frac{t_1 \Downarrow n_1 \quad t_2 \Downarrow n_2}{t_1 - t_2 \Downarrow n_1 \mathbin{\dot{-}} n_2}\ \textsf{sub}
\qquad
\frac{t_1 \Downarrow n_1 \quad t_2 \Downarrow n_2}{t_1 * t_2 \Downarrow n_1 \times n_2}\ \textsf{mul}
```

- 規則の左辺の$n$は数の式，右辺の$n$は自然数である．
- $\dot{-}$は自然数の引き算で，引く数のほうが大きいときは$0$になる．
- 評価器`eval`は，この意味論を計算する関数である．`eval`が意味論に従うことを，性質`eval_sound`と`eval_complete`で保証する．

## 性質

$\mathit{eval}(t) = \mathit{eval}(u)$のとき，式$t$と$u$は等価であるという．`eval`は大ステップ意味論に従うので，これは2つの式が同じ値に評価されることと同じである．
等価な式は，どの文脈で使っても同じ値になる．

- `eval_add_comm`：$t_1 + t_2$と$t_2 + t_1$は等価である．
- `eval_add_assoc`：$(t_1 + t_2) + t_3$と$t_1 + (t_2 + t_3)$は等価である．
- `eval_mul_comm`：$t_1 * t_2$と$t_2 * t_1$は等価である．
- `eval_mul_assoc`：$(t_1 * t_2) * t_3$と$t_1 * (t_2 * t_3)$は等価である．
- `eval_mul_one`：$t * 1$と$t$は等価である．
- `eval_sub_not_assoc`：$(t_1 - t_2) - t_3$と$t_1 - (t_2 - t_3)$は，等価とは限らない．
- `eval_sound`：`eval t = n`ならば$t \Downarrow n$である(評価器の健全性)．
- `eval_complete`：$t \Downarrow n$ならば`eval t = n`である(評価器の完全性)．
- `eval_deterministic`：$t \Downarrow n$かつ$t \Downarrow m$ならば$n = m$である(大ステップ意味論の決定性)．
- `run_of_parse`：構文解析に成功した文字列を実行すると，その式の値が表示される．
