import Mini.Syntax

/-!
# 評価器

式を評価して，その値の自然数を返す．
-/

namespace Mini

/-- 式`t`の値．`-`は自然数の引き算で，結果が負になるときは`0`になる． -/
def eval : Term → Nat
  | .num n => n
  | .add t₁ t₂ => eval t₁ + eval t₂
  | .sub t₁ t₂ => eval t₁ - eval t₂
  | .mul t₁ t₂ => eval t₁ * eval t₂

end Mini
