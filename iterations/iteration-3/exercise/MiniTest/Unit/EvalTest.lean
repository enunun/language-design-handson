import Mini.Eval
import Mini.BigStep
import Mini.SmallStep

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

/-! ## 大ステップ意味論との一致 -/

/-- 健全性：評価器が返す値は，大ステップ意味論でも式の値である． -/
theorem eval_sound {t : Term} {n : Nat} (h : eval t = n) : t ⇓ n := by
  subst h
  induction t with
  | num n => exact Eval.num
  | add t₁ t₂ ih₁ ih₂ => exact Eval.add ih₁ ih₂
  | sub t₁ t₂ ih₁ ih₂ => exact Eval.sub ih₁ ih₂
  | mul t₁ t₂ ih₁ ih₂ => exact Eval.mul ih₁ ih₂

/-- 完全性：大ステップ意味論で式の値が`n`なら，評価器も`n`を返す． -/
theorem eval_complete {t : Term} {n : Nat} (h : t ⇓ n) : eval t = n := by
  induction h with
  | num => rfl
  | add _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | sub _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]

/-- 大ステップ意味論は決定的である．完全性から，どちらの値も`eval t`に等しい． -/
theorem eval_deterministic {t : Term} {n m : Nat} (h₁ : t ⇓ n) (h₂ : t ⇓ m) : n = m := by
  rw [← eval_complete h₁, ← eval_complete h₂]

/-! ## 1ステップの簡約 -/

example : step (.mul (.add (.num 1) (.num 2)) (.add (.num 3) (.num 4)))
    = some (.mul (.num 3) (.add (.num 3) (.num 4))) := by decide

example : step (.mul (.num 3) (.add (.num 3) (.num 4))) = some (.mul (.num 3) (.num 7)) := by decide

example : step (.num 21) = none := by decide

/-- `step`の健全性：`step`が返す式は，小ステップ意味論で1ステップ簡約した式である． -/
theorem step_sound {t t' : Term} (h : step t = some t') : t ⟶ t' := by
  induction t generalizing t' with
  | num n => simp [step] at h
  | add t₁ t₂ ih₁ ih₂ =>
    unfold step at h
    split at h
    · cases h; exact .add
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .addR (ih₂ hu)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .addL (ih₁ hu)
  | sub t₁ t₂ ih₁ ih₂ =>
    unfold step at h
    split at h
    · cases h; exact .sub
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .subR (ih₂ hu)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .subL (ih₁ hu)
  | mul t₁ t₂ ih₁ ih₂ =>
    unfold step at h
    split at h
    · cases h; exact .mul
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .mulR (ih₂ hu)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .mulL (ih₁ hu)

/-- `step`の完全性：小ステップ意味論で1ステップ簡約できるなら，`step`はその式を返す． -/
theorem step_complete {t t' : Term} (h : t ⟶ t') : step t = some t' := by
  induction h with
  | addL s ih => cases s <;> simp_all [step]
  | addR s ih => cases s <;> simp_all [step]
  | add => rfl
  | subL s ih => cases s <;> simp_all [step]
  | subR s ih => cases s <;> simp_all [step]
  | sub => rfl
  | mulL s ih => cases s <;> simp_all [step]
  | mulR s ih => cases s <;> simp_all [step]
  | mul => rfl

end MiniTest.EvalTest
