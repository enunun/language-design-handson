# Iteration 2 帰納法の一般化と`Option`

Iteration 2で使うLeanの構文とtacticを説明する．
例には，Iteration 1のノートの関係`SumOf`と，リストを扱う小さな関数を使う．

## 帰納法の仮定を一般化する：`generalizing`

`SumOf xs s`の和`s`が1つに決まることを，導出についての帰納法で示したい．
次のように書くと，証明が通らない．

```lean
theorem sumOf_unique_bad {xs : List Nat} {s₁ s₂ : Nat} (h₁ : SumOf xs s₁) (h₂ : SumOf xs s₂) : s₁ = s₂ := by
  induction h₁ with
  | nil => cases h₂; rfl
  | cons _ ih =>
    cases h₂ with
    | cons h₂' => rw [ih h₂']
```

`cons`の場合のゴールは次のとおりである．

```text
case cons
xs : List Nat
s₁ s₂ x✝ : Nat
xs✝ : List Nat
s✝ : Nat
a✝ : SumOf xs✝ s✝
ih : SumOf xs✝ s₂ → s✝ = s₂
h₂ : SumOf (x✝ :: xs✝) s₂
⊢ x✝ + s✝ = s₂
```

帰納法の仮定`ih`は，固定された`s₂`についての主張になっている．
しかし`h₂`を分解して得られるのは，`xs✝`の和が別の値であるという導出である．
そのため，`ih h₂'`は型が合わない．

```text
error: Application type mismatch: The argument
  h₂'
has type
  SumOf xs✝ s✝
but is expected to have type
  SumOf xs✝ (x✝ + s✝)
```

`generalizing s₂`を付けると，帰納法の仮定が「任意の`s₂`について」の主張になる．

```lean
theorem sumOf_unique {xs : List Nat} {s₁ s₂ : Nat} (h₁ : SumOf xs s₁) (h₂ : SumOf xs s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | nil => cases h₂; rfl
  | cons _ ih =>
    cases h₂ with
    | cons h₂' => rw [ih h₂']
```

帰納法の途中で別の値に当てはめたい変数は，`generalizing`で一般化しておく．

## 値がないこともある：`Option`

`Option α`は，`α`の値が1つある(`some a`)か，ない(`none`)かのどちらかを表す型である．
リストの先頭を返す`List.head?`は，空のリストには`none`を返す．

```lean
#eval [3, 1, 2].head?
#eval ([] : List Nat).head?
#eval ([3, 1, 2].head?).map (· + 10)
```

```text
some 3
none
some 13
```

`o.map f`は，`o`が`some a`なら`some (f a)`を，`none`なら`none`を返す．
`(· + 10)`は，引数に`10`を足す関数`fun x => x + 10`の略記である．

## 存在：`∃`と`⟨_, _⟩`

`∃ n, P n`は「`P n`を満たす`n`がある」という命題である．
証明するには，具体的な`n`と，`P n`の証明を組にして示す．
組は`⟨_, _⟩`(`\<`と`\>`)で書く．

```lean
def firstTwo : List Nat → Option Nat
  | x :: y :: _ => some (x + y)
  | _ => none

example : ∃ n, firstTwo [1, 2, 3] = some n := ⟨3, rfl⟩
```

`∧`(かつ)を証明するときも，2つの証明を`⟨_, _⟩`で組にする．

## 仮定を分解する：`obtain`

仮定が`∃`や`∧`の形のとき，`obtain`で中身を取り出す．

```lean
theorem map_some {o : Option Nat} {m : Nat} (h : o.map (· + 10) = some m) : ∃ n, o = some n ∧ m = n + 10 := by
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨n, hn, rfl⟩ := h
  exact ⟨n, hn, rfl⟩
```

- `Option.map_eq_some_iff`は，「`o.map f = some m`は，`o = some n`かつ`f n = m`となる`n`があることと同値」という定理である．`simp only [...] at h`で，`h`をこの形に書き換える．
- `obtain ⟨n, hn, rfl⟩ := h`は，`h`から`n`と`hn : o = some n`を取り出す．最後の`rfl`は，等式`n + 10 = m`を使って`m`を`n + 10`に置き換える．

## `match`の場合分け：`split`と`unfold`

関数の定義に`match`があるとき，`split`でその場合ごとにゴールを分けられる．
`split at h`は，仮定`h`の中の`match`で場合を分ける．

```lean
def classify : List Nat → Option Nat
  | [] => none
  | x :: xs =>
    match x, xs with
    | 0, _ => some 0
    | _, [] => some 1
    | _, _ => some 2

example (x : Nat) (xs : List Nat) (n : Nat) (h : classify (x :: xs) = some n) : n ≤ 2 := by
  simp only [classify] at h
  split at h
  · cases h; decide
  · cases h; decide
  · cases h; decide
```

`simp only [classify] at h`で定義を展開すると，`h`の左辺は`match`になる．
`split at h`で3つの場合に分かれ，各場合の`h`は`some 0 = some n`などになる．
`cases h`で`n`が具体的な値になり，`decide`で不等式を確かめる．

Leanは，`match`を含む関数の定義から，場合ごとの等式を自動で作る．
入れ子の`match`では，等式が具体的な形の引数についてだけ作られ，`simp only [f]`で展開できないことがある．
そのときは`unfold f`を使う．
`unfold f`は，引数の形によらず`f`の定義そのものに置き換える．

## 帰納法の前に式を変数にする：`generalize`

`induction h`は，`h`の型に現れる引数が変数でないと，うまく場合を分けられないことがある．
`generalize hu : 式 = u at h`は，`h`の中の`式`を新しい変数`u`に置き換え，等式`hu : 式 = u`を仮定に加える．
帰納法の各場合で，必要になったところで`hu`を使う．

## 同じtacticを全部の場合に使う：`<;>`と`simp_all`

`t₁ <;> t₂`は，`t₁`で分かれたすべてのゴールに`t₂`を使う．
`cases h <;> simp_all`のように，場合分けの後の処理が同じときに使う．

`simp_all`は，ゴールとすべての仮定を，仮定を使いながらまとめて簡単にする．
