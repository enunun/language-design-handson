# Iteration 4 失敗を返す関数と証明の組み立て

Iteration 4で使うLeanの構文とtacticを説明する．
例には，割り算を安全に行う小さな関数を使う．

## 失敗の理由を返す：`Except`

`Except ε α`は，成功して`α`の値を返す(`.ok a`)か，失敗して`ε`の値を返す(`.error e`)かのどちらかを表す型である．
`Option`と違い，失敗の理由を持てる．

```lean
def safeDiv (a b : Nat) : Except String Nat :=
  if b = 0 then .error "0で割った" else .ok (a / b)

#eval safeDiv 7 2
#eval safeDiv 7 0
```

```text
Except.ok 3
Except.error "0で割った"
```

`Except`には，2つの値が等しいかを判定する`DecidableEq`のインスタンスがない．
そのため，`Except`の値の等式は`decide`で証明できない．

```lean
example : safeDiv 7 0 = .error "0で割った" := by decide
```

```text
error: failed to synthesize
  Decidable (safeDiv 7 0 = Except.error "0で割った")
```

計算すれば両辺が同じになる等式なので，`rfl`で証明する．

```lean
example : safeDiv 7 0 = .error "0で割った" := rfl
```

## または：`∨`

`P ∨ Q`は「`P`または`Q`」である．
証明するには，どちらか一方を示す．
`.inl`で左の`P`を，`.inr`で右の`Q`を示す．

```lean
theorem zero_or_pos (n : Nat) : n = 0 ∨ 0 < n := by
  cases n with
  | zero => exact .inl rfl
  | succ m => exact .inr (Nat.succ_pos m)
```

## `rcases`で`∨`と`∃`を分解する

仮定が`P ∨ Q`のとき，`rcases h with hp | hq`で2つの場合に分ける．
`∃`や`∧`は`⟨…⟩`で分解する．
2つを組み合わせて，`rcases h with rfl | ⟨m, rfl⟩`のように書ける．
`rfl`の位置に来る等式は，その場で変数を置き換えるのに使われる．

```lean
example (n : Nat) (h : n = 0 ∨ ∃ m, n = m + 1) : n + 1 ≠ 0 := by
  rcases h with rfl | ⟨m, rfl⟩
  · decide
  · simp
```

1つ目の場合では`n`が`0`に，2つ目の場合では`n`が`m + 1`に置き換わる．

## 複数のゴールを扱う：`all_goals`と`first`

`all_goals t`は，残っているすべてのゴールに`t`を使う．

```lean
example (n : Nat) : n + 0 = n ∧ 0 + n = n := by
  constructor
  all_goals simp
```

`first | t₁ | t₂`は，`t₁`を試し，失敗したら`t₂`を試す．
`<;>`と組み合わせると，場合によって異なるtacticで閉じるゴールの集まりを，まとめて扱える．

```lean
example (b : Bool) : b = true ∨ b = false := by
  cases b <;> first | exact .inl rfl | exact .inr rfl
```

`b`が`false`の場合は`.inl rfl`が失敗し，`.inr rfl`で閉じる．
`b`が`true`の場合は`.inl rfl`で閉じる．

## 等式を組み合わせる：`symm`と`trans`

`h : a = b`があるとき，`h.symm`は`b = a`の証明である．
`h₁ : a = b`と`h₂ : b = c`があるとき，`h₁.trans h₂`は`a = c`の証明である．

```lean
example (n : Nat) (h : n = 0) : 0 = n := h.symm
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := h₁.trans h₂
```

`f x = some v`と`f x = some w`から`some v = some w`を作り，`cases`で分解すると`v = w`が得られる．
型の一意性や大ステップ意味論の決定性を，完全性から導くときに使う．
