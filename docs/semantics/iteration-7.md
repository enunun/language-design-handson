# Iteration 7 一般再帰と停止しない評価

Iteration 7で扱う意味論の考え方を説明する．
例には，自然数と関数を持つ小さな言語の式を使う．

## 再帰関数

$\mathsf{fun}$で作る関数は，本体の中で自分自身を呼べない．
関数に名前を付ける$\mathsf{let}$も，束縛する式の中ではその名前を使えない．
そこで，自分自身を表す名前$f$を本体の中で使える再帰関数を足す．

```math
\mathsf{fix}\ f\ (x : A) : B \Rightarrow t
```

この式は，$A$型の引数$x$を受け取り，$B$型の値を返す関数である．
本体$t$の中の$f$は，この関数自身を表す．
たとえば，階乗は次のように書ける．

```math
\mathsf{fix}\ \mathit{fact}\ (n : \mathsf{Nat}) : \mathsf{Nat} \Rightarrow \mathsf{if}\ \mathsf{iszero}\ n\ \mathsf{then}\ 1\ \mathsf{else}\ n * \mathit{fact}\ (n - 1)
```

どんな再帰でも書けるので，この仕組みを一般再帰という．

## 再帰関数の適用

再帰関数$F = \mathsf{fix}\ f\ (x : A) : B \Rightarrow b$を値$v$に適用すると，本体の$x$を$v$で，$f$を$F$自身で置き換える．

```math
F\ v \longrightarrow b[x := v][f := F]
```

本体の中の$f$は，置き換えた後には再帰関数$F$そのものになる．
再帰呼び出し$F\ (n - 1)$を簡約すると，同じ規則でもう一度本体が展開される．
再帰関数は値なので，置換する式が閉じた値に限られることは変わらない．

## 停止しない評価

一般再帰があると，評価が終わらない式を書ける．

```math
\mathit{loop} = \mathsf{fix}\ \mathit{loop}\ (n : \mathsf{Nat}) : \mathsf{Nat} \Rightarrow \mathit{loop}\ n
```

$\mathit{loop}\ 0$を1ステップ簡約すると，$\mathit{loop}\ 0$に戻る．

```math
\mathit{loop}\ 0 \longrightarrow \mathit{loop}\ 0 \longrightarrow \mathit{loop}\ 0 \longrightarrow \cdots
```

小ステップ意味論では，終わらない評価は無限に続く簡約列として現れる．
$\mathit{loop}\ 0$は行き詰まってもいないし，値に着くこともない．

大ステップ意味論では，終わらない評価には導出がない．
$\mathit{loop}\ 0 \Downarrow v$の導出があったとすると，その前提には$\mathit{loop}\ 0 \Downarrow v$のもっと小さい導出が要る．
導出は有限の木なので，そのような導出はない．
大ステップ意味論は，評価が終わらない式と行き詰まった式を区別できない．
どちらも値がない式になる．

燃料つきの評価器は，燃料を使い切ったことを返す．
燃料切れは，評価が終わらないことの証拠ではない．
もっと燃料を与えれば値に着く式もあるからである．

## 型安全性と停止性

再帰関数の型付け規則は，本体の型を求めるときに，$x$と$f$の型を文脈に加える．

```math
\frac{(x : A), (f : A \rightarrow B), \Gamma \vdash t : B}{\Gamma \vdash \mathsf{fix}\ f\ (x : A) : B \Rightarrow t : A \rightarrow B}
```

本体の中で$f$を呼ぶには，$f$の型$A \rightarrow B$が要る．
しかし$B$は，本体の型を求めるまでわからない．
そこで，結果の型$B$を注釈で与える．

$\mathit{loop}\ 0$には型$\mathsf{Nat}$が付く．
型が付くことは，評価が終わることを意味しない．
Iteration 6の言語では，型の付く式の評価は必ず終わった(正規化)．
一般再帰を足すと，正規化は成り立たなくなる．

それでも型安全性は成り立つ．
型安全性が保証するのは，「行き詰まらない」ことであり，「値に着く」ことではない．
型の付く式は，値に着くか，簡約が無限に続くかのどちらかである．

## 値呼びと名前呼び，ふたたび

Iteration 6では，値呼びと名前呼びで結果が変わるのは，評価が終わらない式を引数にするときだと述べた．

```math
(\mathsf{fun}\ (x : \mathsf{Nat}) \Rightarrow 1)\ (\mathit{loop}\ 0)
```

値呼びでは，引数$\mathit{loop}\ 0$の評価が終わらないので，式全体の評価も終わらない．
名前呼びでは，引数を評価せずに本体へ置換するので，1ステップで$1$になる．
この式には型が付く．
型の付く式でも，評価戦略によって値に着くかどうかが変わる．
