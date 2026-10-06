/-!
# 構文

Miniの式の抽象構文を定義する．
-/

namespace Mini

/-- Miniの式．`num n`は自然数のリテラル，`add`，`sub`，`mul`はそれぞれ`+`，`-`，`*`である． -/
inductive Term where
  | num (n : Nat)
  | add (t₁ t₂ : Term)
  | sub (t₁ t₂ : Term)
  | mul (t₁ t₂ : Term)
  deriving Repr, DecidableEq

end Mini
