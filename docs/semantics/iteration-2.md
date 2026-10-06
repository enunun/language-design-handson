# Iteration 2 小ステップ意味論

Iteration 2で扱う意味論の考え方を説明する．
例には，これまでと同じ真偽値の式の言語を使う．

## 1ステップずつ簡約する

大ステップ意味論は，式と最終的な値の関係を定めた．
小ステップ意味論は，式を1ステップだけ書き換える関係$b \longrightarrow b'$を定める．
これを繰り返して値に着くまでの列が，評価の過程を表す．

```math
\mathsf{not}\ (\mathsf{true} \mathbin{\|} \mathsf{false})
\longrightarrow \mathsf{not}\ \mathsf{true}
\longrightarrow \mathsf{false}
```

小ステップ意味論の規則には，2種類がある．

- 計算の規則：部分式がすべて値になった式を，1ステップで計算する．
- 合同規則：部分式を1ステップ簡約したら，式全体も1ステップ簡約されたとみなす．

```math
\frac{}{\mathsf{true} \mathbin{\|} b \longrightarrow \mathsf{true}}\ \textsf{orTrue}
\qquad
\frac{}{\mathsf{false} \mathbin{\|} b \longrightarrow b}\ \textsf{orFalse}
\qquad
\frac{b_1 \longrightarrow b_1'}{b_1 \mathbin{\|} b_2 \longrightarrow b_1' \mathbin{\|} b_2}\ \textsf{orL}
```

`orL`が合同規則，残りの2つが計算の規則である．

## 評価の順序

小ステップ意味論では，どの部分式から簡約するかを規則で決める．
上の規則では，$\|$の左の式だけを簡約し，左が値になったら計算する．
右の式は，必要になるまで簡約しない．
この選択は，左の式が$\mathsf{true}$なら右の式を評価しない「短絡評価」を表している．

評価の順序は，利用者から見える振る舞いを左右する．
評価の途中で誤りの起きる式や，評価の終わらない式があると，どの部分式を先に評価するかで結果が変わる．
大ステップ意味論では評価の途中を書かないので，この違いを表しにくい．

## 正規形

どの規則でも簡約できない式を，正規形という．
値は正規形である．
値でないのに正規形である式は，評価の途中で行き詰まった式である．
Iteration 3で，このような式が現れる．

## 多ステップ簡約

0ステップ以上の簡約$b \longrightarrow^{*} b'$は，1ステップの簡約を何回でも繰り返してよい関係である．
これは，1ステップの簡約の反射推移閉包である．

```math
\frac{}{b \longrightarrow^{*} b}\ \textsf{refl}
\qquad
\frac{b \longrightarrow b' \quad b' \longrightarrow^{*} b''}{b \longrightarrow^{*} b''}\ \textsf{step}
```

- 反射：どの式も，0ステップで自分自身に簡約される．
- 推移：$b \longrightarrow^{*} b'$と$b' \longrightarrow^{*} b''$なら，$b \longrightarrow^{*} b''$である．この性質は規則から証明できる．

## 決定性

小ステップ意味論が決定的であるとは，どの式も，1ステップで簡約した結果がたかだか1つに決まることである．

```math
b \longrightarrow b_1 \land b \longrightarrow b_2 \implies b_1 = b_2
```

規則の左辺が重ならないように書けば，決定性が成り立つ．
たとえば，`orL`の前提$b_1 \longrightarrow b_1'$は，$b_1$が値のときには成り立たない．
そのため，$\mathsf{true} \mathbin{\|} b$には`orTrue`しか当てはまらない．

決定性は，導出についての帰納法で証明する．
一方の導出の規則で場合を分け，もう一方の導出も同じ規則でしかありえないことを示す．

## 2つの意味論の一致

同じ言語に2つの意味論を定めたら，それらが同じ意味を与えることを確かめる．

```math
b \Downarrow v \iff b \longrightarrow^{*} v
```

右向きは，大ステップの導出についての帰納法で示す．
部分式の簡約列を，合同規則で式全体の簡約列に持ち上げてつなぐ．

左向きは，次の補題を使う．

```math
b \longrightarrow b' \land b' \Downarrow v \implies b \Downarrow v
```

1ステップ簡約した式の値は，簡約する前の式の値でもある．
これを簡約列に沿って繰り返し使う．

2つの意味論はそれぞれの役割を持つ．
大ステップ意味論は評価器の仕様として読みやすい．
小ステップ意味論は評価の途中を表せるので，Iteration 4で型安全性を述べるのに使う．
