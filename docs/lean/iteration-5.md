# Iteration 5 文字列と燃料

Iteration 5で使うLeanの構文とtacticを説明する．
例には，文字列を扱う関数と，コラッツの操作を繰り返す関数を使う．

## 文字列の比較と`if`

`String`は文字列の型である．
`x = y`は命題だが，`String`の等しさは計算で判定できるので，`if x = y then … else …`と書ける．

```lean
def greet (name : String) : String :=
  if name = "Lean" then "やあ，Lean" else s!"こんにちは，{name}"

#eval greet "Lean"
#eval greet "Mini"
```

```text
"やあ，Lean"
"こんにちは，Mini"
```

`if`を含む式を証明の中で簡単にするには，条件が成り立つかどうかの仮定を`simp`に渡す．

```lean
theorem greet_ne (name : String) (h : name ≠ "Lean") : greet name = s!"こんにちは，{name}" := by
  simp [greet, h]
```

`if x = x then …`のように，条件が明らかに成り立つときは，`simp`だけで簡単になる．

## 場合分け：`by_cases`

`by_cases h : P`は，`P`が成り立つ場合と成り立たない場合にゴールを分ける．
それぞれの場合で，`h : P`か`h : ¬ P`が仮定に加わる．

```lean
example (n : Nat) : (if n = 0 then 0 else n) = n := by
  by_cases h : n = 0
  · simp [h]
  · simp [h]
```

変数の名前が等しいかどうかで場合を分ける証明(置換の性質など)で使う．

## 停止することを示せない関数と燃料

Leanの関数は，必ず停止しなければならない．
引数が構成子を1つずつはがして小さくなっていく再帰(構造的な再帰)なら，Leanは自動で停止を確かめる．
そうでない再帰では，停止を確かめられないとエラーになる．

```lean
def collatz (n : Nat) : Nat :=
  if n ≤ 1 then 0
  else if n % 2 = 0 then collatz (n / 2) + 1
  else collatz (3 * n + 1) + 1
```

```text
error: fail to show termination for
  collatz
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    collatz (n / 2)
```

`3 * n + 1`は`n`より大きいので，引数が小さくなっていかない．
このような関数は，繰り返しの上限(燃料)を引数に足し，燃料についての構造的な再帰として書く．
燃料を使い切ったら，結果がないことを返す．

```lean
def collatzFuel : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, n =>
    if n ≤ 1 then some 0
    else if n % 2 = 0 then (collatzFuel fuel (n / 2)).map (· + 1)
    else (collatzFuel fuel (3 * n + 1)).map (· + 1)

#eval collatzFuel 100 6
#eval collatzFuel 3 6
```

```text
some 8
none
```

燃料つきの関数の性質は，「燃料が十分にあれば結果が出る」「結果が出たならそれは正しい」という形で述べる．
証明は，燃料についての帰納法で行う．

## 既定値を持つ引数

`(times : Nat := 2)`のように引数に既定値を書くと，その引数を省略できる．
省略したときは既定値が使われる．

```lean
def repeatStr (s : String) (times : Nat := 2) : String :=
  String.join (List.replicate times s)

#eval repeatStr "ab"
#eval repeatStr "ab" 3
```

```text
"abab"
"ababab"
```

既定値を持つ引数は，引数の並びの後ろのほうに置く．

## 等式を仮定にした帰納法

Iteration 2では，`generalize hu : 式 = u at h`で式を変数にしてから帰納法を使った．
このとき，帰納法の仮定は等式`hu`を前提として持つ．

型付けの導出のうち，空の文脈の場合だけを示したいときも，同じ方法を使う．
`generalize hΓ : ([] : Ctx) = Γ at h`の後で`induction h`とすると，帰納法の仮定は`[] = Γ → …`の形になる．
帰納法の仮定を使うときは，等式の証明(`rfl`や`hΓ`)を引数に渡す．
引数の順序は，Infoviewで帰納法の仮定の型を見て確かめる．
