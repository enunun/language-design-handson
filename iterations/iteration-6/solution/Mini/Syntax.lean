/-!
# 構文

Miniの型と式の抽象構文と，評価の結果の値を定義する．
-/

namespace Mini

/-- Miniの型．自然数の型`Nat`，真偽値の型`Bool`，`A`を受け取り`B`を返す関数の型`A → B`である． -/
inductive Ty where
  | nat
  | bool
  | arrow (A B : Ty)
  deriving Repr, DecidableEq

/-- Miniの式．`num n`は自然数のリテラル，`add`，`sub`，`mul`はそれぞれ`+`，`-`，`*`である．
`tru`と`fls`は真偽値のリテラル`true`と`false`，`ite c t e`は`if c then t else e`である．
`iszero t`は，`t`の値が`0`かどうかを調べる．
`var x`は変数，`let_ x t u`は`let x = t in u`である．
`lam x A t`は関数`fun (x : A) => t`，`app t u`は関数適用`t u`である． -/
inductive Term where
  | num (n : Nat)
  | add (t₁ t₂ : Term)
  | sub (t₁ t₂ : Term)
  | mul (t₁ t₂ : Term)
  | tru
  | fls
  | ite (c t e : Term)
  | iszero (t : Term)
  | var (x : String)
  | let_ (x : String) (t u : Term)
  | lam (x : String) (A : Ty) (t : Term)
  | app (t u : Term)
  deriving Repr, DecidableEq

/-- 評価の結果の値．自然数，真偽値，関数である． -/
inductive Value where
  | num (n : Nat)
  | bool (b : Bool)
  | lam (x : String) (A : Ty) (t : Term)
  deriving Repr, DecidableEq

/-- 値を，その値を表す式にする． -/
def Value.toTerm : Value → Term
  | .num n => .num n
  | .bool true => .tru
  | .bool false => .fls
  | .lam x A t => .lam x A t

/-- 式が値を表すなら，その値を返す． -/
def Term.toValue? : Term → Option Value
  | .num n => some (.num n)
  | .tru => some (.bool true)
  | .fls => some (.bool false)
  | .lam x A t => some (.lam x A t)
  | _ => none

end Mini
