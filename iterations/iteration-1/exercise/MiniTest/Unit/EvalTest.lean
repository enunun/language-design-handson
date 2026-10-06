import Mini.Eval

/-!
# `Mini.Eval`の単体テスト
-/

namespace MiniTest.EvalTest

open Mini

/-! ## 各演算子の評価 -/

example : eval (.num 3) = 3 := by decide

example : eval (.add (.num 1) (.num 2)) = 3 := by decide

example : eval (.sub (.num 5) (.num 2)) = 3 := by decide

/-- 引き算の結果が負になるときは`0`になる． -/
example : eval (.sub (.num 2) (.num 5)) = 0 := by decide

example : eval (.mul (.num 2) (.num 3)) = 6 := by decide

example : eval (.add (.num 1) (.mul (.num 2) (.num 3))) = 7 := by decide

/-! ## 式の等価性 -/

theorem eval_add_comm (t₁ t₂ : Term) : eval (.add t₁ t₂) = eval (.add t₂ t₁) := by
  simp only [eval]
  exact Nat.add_comm _ _

theorem eval_add_assoc (t₁ t₂ t₃ : Term) :
    eval (.add (.add t₁ t₂) t₃) = eval (.add t₁ (.add t₂ t₃)) := by
  simp only [eval]
  exact Nat.add_assoc _ _ _

theorem eval_mul_comm (t₁ t₂ : Term) : eval (.mul t₁ t₂) = eval (.mul t₂ t₁) := by
  simp only [eval]
  exact Nat.mul_comm _ _

theorem eval_mul_assoc (t₁ t₂ t₃ : Term) :
    eval (.mul (.mul t₁ t₂) t₃) = eval (.mul t₁ (.mul t₂ t₃)) := by
  simp only [eval]
  exact Nat.mul_assoc _ _ _

theorem eval_mul_one (t : Term) : eval (.mul t (.num 1)) = eval t := by
  simp only [eval]
  exact Nat.mul_one _

/-- `-`は結合法則を満たさない．`(3 - 2) - 1`は`0`だが，`3 - (2 - 1)`は`2`である． -/
theorem eval_sub_not_assoc :
    ¬ ∀ t₁ t₂ t₃ : Term, eval (.sub (.sub t₁ t₂) t₃) = eval (.sub t₁ (.sub t₂ t₃)) := by
  intro h
  have h' := h (.num 3) (.num 2) (.num 1)
  simp [eval] at h'

end MiniTest.EvalTest
