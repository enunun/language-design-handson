import Mini.BigStep

/-!
# `Mini.BigStep`の単体テスト
-/

namespace MiniTest.BigStepTest

open Mini

/-! ## 導出の例 -/

example : Term.num 3 ⇓ 3 := Eval.num

example : Term.add (.num 1) (.num 2) ⇓ 3 := Eval.add Eval.num Eval.num

/-- `1 + 2 * 3`の導出．規則を組み合わせた木になる． -/
example : Term.add (.num 1) (.mul (.num 2) (.num 3)) ⇓ 7 :=
  Eval.add Eval.num (Eval.mul Eval.num Eval.num)

/-- 引き算の結果が負になるときは`0`になる． -/
example : Term.sub (.num 2) (.num 5) ⇓ 0 := Eval.sub Eval.num Eval.num

/-- `1 + 2`を評価しても`4`にはならない． -/
example : ¬ Term.add (.num 1) (.num 2) ⇓ 4 := by
  have h3 : ∀ n, Term.add (.num 1) (.num 2) ⇓ n → n = 3 := by
    intro n h
    cases h with
    | add h₁ h₂ =>
      cases h₁
      cases h₂
      rfl
  intro h
  have := h3 4 h
  contradiction

end MiniTest.BigStepTest
