# Iteration 3 場合の多い定義と証明

Iteration 3で使うLeanの構文とtacticを説明する．
例には，`Option Nat`を扱う小さな関数を使う．

## 複数の値についての`match`

`match a, b with`は，2つの値の組み合わせで場合を分ける．
上の行から順に試し，最初に当てはまった場合を使う．
`_`はどんな値にも当てはまる．

```lean
def addOpt (a b : Option Nat) : Option Nat :=
  match a, b with
  | some x, some y => some (x + y)
  | _, _ => none

#eval addOpt (some 1) (some 2)
#eval addOpt (some 1) none
```

```text
some 3
none
```

## 真偽値`Bool`と命題`Prop`

`Bool`は，計算できる真偽値`true`と`false`の型である．
`a == b`は，`a`と`b`が等しいかを計算して`Bool`を返す．
`a = b`は，等しいという命題(`Prop`)である．

```lean
#eval (3 == 0, 0 == 0)
#check (3 == 0)
#check (3 = 0)
```

```text
(false, true)
3 == 0 : Bool
3 = 0 : Prop
```

`(0 == 0) = true`は，計算すると両辺が等しくなるので`rfl`で証明できる．

## `rcases`で値の形を場合分けする

`rcases a with _ | x`は，`Option Nat`の値`a`を，`none`の場合と`some x`の場合に分ける．
`|`で区切った1つ1つが，構成子ごとの場合である．
`<;>`でつなぐと，分かれたすべての場合で次のtacticを使う．

```lean
theorem addOpt_comm (a b : Option Nat) : addOpt a b = addOpt b a := by
  simp only [addOpt]
  rcases a with _ | x <;> rcases b with _ | y <;> simp [Nat.add_comm]
```

`a`と`b`のそれぞれで2つの場合に分かれるので，4つの場合になる．
どの場合も，`simp`が`match`を計算し，残った等式を`Nat.add_comm`で示す．

`rcases`は，`a`が変数でなく`eval t₁`のような式でも使える．
その式を新しい変数に置き換えてから場合を分ける．

値の型の構成子が3つ以上あるときは，`_ | _ | _`のように区切りを増やす．
`Option Value`は，`none`，`some (.num n)`，`some (.bool b)`の3つの場合に分けられる．

## 等しくない：`≠`

`a ≠ b`は`¬ (a = b)`の略記で，`\ne`と打つと入力できる．
証明するには，`a = b`を仮定して矛盾を導く．

```lean
example : (1 : Nat) ≠ 2 := by
  intro h
  contradiction
```

`contradiction`は，`1 = 2`のように構成子の異なる値が等しいという仮定を，矛盾として扱う．

## 名前付き引数

関数や構成子の引数は，`(名前 := 値)`の形で，名前を指定して渡せる．
暗黙の引数をLeanが推論できないときに使う．

```lean
def isZero (n : Nat) : Bool := n == 0
example : isZero (n := 0) = true := rfl
```

`Eval.iszero (n := 0) Eval.num`のように書くと，規則の暗黙の引数`n`を`0`に決められる．

## 暗黙の引数に名前を付ける：`@`

`induction h with`や`cases h with`の各場合では，規則の明示的な引数(前提)にだけ名前を付ける．
暗黙の引数にも名前を付けたいときは，構成子の名前の前に`@`を付け，すべての引数を順に並べる．

```lean
inductive Pos : Nat → Prop where
  | one : Pos 1
  | succ {n : Nat} : Pos n → Pos (n + 1)

theorem pos_ne_zero {n : Nat} (h : Pos n) : n ≠ 0 := by
  induction h with
  | one => decide
  | @succ m _ _ => exact Nat.succ_ne_zero m
```

`@succ m _ _`の`m`は暗黙の引数`n`，次の`_`は前提`Pos m`，最後の`_`は帰納法の仮定である．
