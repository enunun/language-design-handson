# Iteration 6 名前のない仮定を扱う

Iteration 6で使うLeanのtacticを説明する．
例には，2つのリストの先頭を調べる小さな関数を使う．

## 証明の途中の状態を表示する：`trace_state`

`trace_state`は，その位置のゴールと仮定を表示するtacticである．
エディタではInfoviewで見られるが，`lake build`の出力やエラーの位置から離れた場所の状態を見たいときに使う．

```lean
def firstOf (xs ys : List Nat) : Option Nat :=
  match xs.head?, ys.head? with
  | some x, _ => some x
  | none, some y => some y
  | none, none => none

theorem firstOf_some {xs ys : List Nat} {n : Nat} (h : firstOf xs ys = some n) :
    xs.head? = some n ∨ ys.head? = some n := by
  unfold firstOf at h
  split at h
  · trace_state
    sorry
  · sorry
  · contradiction
```

1つ目の場合で表示される状態は次のとおりである．

```text
case h_1
xs ys : List Nat
n : Nat
x✝² x✝¹ : Option Nat
x✝ : Nat
heq✝ : xs.head? = some x✝
h : some x✝ = some n
⊢ xs.head? = some n ∨ ys.head? = some n
```

`split`は，`match`の場合ごとに，その場合になる条件を仮定に加える．
ここでは`heq✝ : xs.head? = some x✝`が加わっている．
名前に`✝`が付いた仮定は，そのままでは証明の中で名前を書いて使えない．

## 名前を付ける：`next`

`next a b c => tac`は，名前のない仮定のうち最後の3つに，順に`a`，`b`，`c`という名前を付けてから`tac`を実行する．
名前の要らない位置には`_`を書く．

```lean
theorem firstOf_some' {xs ys : List Nat} {n : Nat} (h : firstOf xs ys = some n) :
    xs.head? = some n ∨ ys.head? = some n := by
  unfold firstOf at h
  split at h
  · next x _ hx =>
    cases h
    exact .inl hx
  · next y _ hy =>
    cases h
    exact .inr hy
  · contradiction
```

1つ目の場合の名前のない仮定は，`x✝²`，`x✝¹`，`x✝`，`heq✝`の順に並んでいる．
`next x _ hx`は最後の3つに名前を付けるので，`x✝¹`が`x`に，`heq✝`が`hx`になる．

付ける名前の数は，`trace_state`やInfoviewで名前のない仮定を数えて決める．
`match`で比べる値の数や，パターンの中の変数の数によって変わる．
