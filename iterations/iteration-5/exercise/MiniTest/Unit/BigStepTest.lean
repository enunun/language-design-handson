import Mini.BigStep

/-!
# `Mini.BigStep`の単体テスト
-/

namespace MiniTest.BigStepTest

open Mini

/-! ## 導出の例 -/

example : Term.num 3 ⇓ .num 3 := Eval.num

example : Term.add (.num 1) (.num 2) ⇓ .num 3 := Eval.add Eval.num Eval.num

/-- `1 + 2 * 3`の導出．規則を組み合わせた木になる． -/
example : Term.add (.num 1) (.mul (.num 2) (.num 3)) ⇓ .num 7 :=
  Eval.add Eval.num (Eval.mul Eval.num Eval.num)

/-- 引き算の結果が負になるときは`0`になる． -/
example : Term.sub (.num 2) (.num 5) ⇓ .num 0 := Eval.sub Eval.num Eval.num

/-- `1 + 2`を評価しても`4`にはならない． -/
example : ¬ Term.add (.num 1) (.num 2) ⇓ .num 4 := by
  have h3 : ∀ v, Term.add (.num 1) (.num 2) ⇓ v → v = .num 3 := by
    intro v h
    cases h with
    | add h₁ h₂ =>
      cases h₁
      cases h₂
      rfl
  intro h
  have := h3 _ h
  contradiction

example : Term.ite .tru (.num 1) (.num 2) ⇓ .num 1 := Eval.iteTrue Eval.tru Eval.num

example : Term.ite (.iszero (.num 0)) (.num 1) (.num 2) ⇓ .num 1 :=
  Eval.iteTrue (Eval.iszero Eval.num) Eval.num

example : Term.iszero (.num 5) ⇓ .bool false := Eval.iszero Eval.num

/-- `1 + true`には値がない． -/
example : ¬ ∃ v, Term.add (.num 1) .tru ⇓ v := by
  intro ⟨v, h⟩
  cases h with
  | add _ h₂ => cases h₂

end MiniTest.BigStepTest
