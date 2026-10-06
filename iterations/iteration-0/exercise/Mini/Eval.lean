import Mini.Syntax

/-!
# 評価器

式を評価して，その値の自然数を返す．
-/

namespace Mini

/-- 式`t`の値．仮の実装で，どの式にも`0`を返す． -/
def eval : Term → Nat := fun _ => 0

end Mini
