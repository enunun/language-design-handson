# Iteration 8 再帰的な値についての帰納法

Iteration 8で使うLeanの証明の書き方を説明する．
例には，自然数を葉に持つ二分木を使う．

```lean
inductive Tree where
  | leaf (n : Nat)
  | node (l r : Tree)

def Tree.sum : Tree → Nat
  | .leaf n => n
  | .node l r => l.sum + r.sum

def Tree.mirror : Tree → Tree
  | .leaf n => .leaf n
  | .node l r => .node r.mirror l.mirror
```

`Tree.mirror`は，木の左右を入れ替える関数である．
`node`は，部分木として`Tree`自身を2つ持つ．
このように，構成子の引数にその型自身を持つ型を，再帰的な型という．

## `cases`では足りない場合

木の左右を入れ替えても，葉の合計は変わらない．
`cases`で場合を分けると，`node`の場合で行き詰まる．

```lean
theorem sum_mirror (t : Tree) : t.mirror.sum = t.sum := by
  cases t with
  | leaf n => rfl
  | node l r =>
    simp only [Tree.mirror, Tree.sum]
    trace_state
    sorry
```

```text
case node
l r : Tree
⊢ r.mirror.sum + l.mirror.sum = l.sum + r.sum
```

部分木`l`と`r`について，`l.mirror.sum = l.sum`がわからないので，先へ進めない．
`cases`は場合を分けるだけで，部分木についての仮定を加えない．

## 値についての帰納法：`induction`

`induction`は，部分木についての帰納法の仮定を加える．

```lean
theorem sum_mirror (t : Tree) : t.mirror.sum = t.sum := by
  induction t with
  | leaf n => rfl
  | node l r ihl ihr =>
    simp only [Tree.mirror, Tree.sum]
    rw [ihl, ihr, Nat.add_comm]
```

`node`の場合の状態は次のとおりである．

```text
case node
l r : Tree
ihl : l.mirror.sum = l.sum
ihr : r.mirror.sum = r.sum
⊢ r.mirror.sum + l.mirror.sum = l.sum + r.sum
```

再帰的な型の値について性質を示すときは，`cases`ではなく`induction`を使う．
`Nat`についての帰納法も，`Nat.succ n`が`Nat`自身を持つ再帰的な型だから使えるのである．

## 帰納的述語についての帰納法

帰納的述語も，前提にその述語自身を持つなら再帰的である．
次の`AllEven t`は，「木`t`の葉がすべて偶数である」ことを表す．

```lean
inductive AllEven : Tree → Prop where
  | leaf {n : Nat} : n % 2 = 0 → AllEven (.leaf n)
  | node {l r : Tree} : AllEven l → AllEven r → AllEven (.node l r)

theorem allEven_sum {t : Tree} (h : AllEven t) : t.sum % 2 = 0 := by
  induction h with
  | leaf hn => exact hn
  | node _ _ ihl ihr => rw [Tree.sum, Nat.add_mod, ihl, ihr]
```

`node`の場合には，2つの前提それぞれについて帰納法の仮定`ihl`と`ihr`が加わる．
これまで`cases`で済んでいた補題も，扱う値や述語が再帰的になれば，`induction`に書き換える必要がある．
