/-!
# 構文

Miniの式の抽象構文と，評価の結果の値を定義する．
-/

namespace Mini

/-- Miniの式．`num n`は自然数のリテラル，`add`，`sub`，`mul`はそれぞれ`+`，`-`，`*`である．
`tru`と`fls`は真偽値のリテラル`true`と`false`，`ite c t e`は`if c then t else e`である．
`iszero t`は，`t`の値が`0`かどうかを調べる． -/
inductive Term where
  | num (n : Nat)
  | add (t₁ t₂ : Term)
  | sub (t₁ t₂ : Term)
  | mul (t₁ t₂ : Term)
  | tru
  | fls
  | ite (c t e : Term)
  | iszero (t : Term)
  deriving Repr, DecidableEq

/-- 評価の結果の値．自然数か真偽値である． -/
inductive Value where
  | num (n : Nat)
  | bool (b : Bool)
  deriving Repr, DecidableEq

/-- 値を，その値を表す式にする． -/
def Value.toTerm : Value → Term
  | .num n => .num n
  | .bool true => .tru
  | .bool false => .fls

end Mini
