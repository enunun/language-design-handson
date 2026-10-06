import Mini.Eval
import Mini.BigStep
import Mini.SmallStep

/-!
# `Mini.Eval`の単体テスト
-/

namespace MiniTest.EvalTest

open Mini

/-! ## 各演算子の評価 -/

example : eval (.num 3) = some (.num 3) := by decide

example : eval (.add (.num 1) (.num 2)) = some (.num 3) := by decide

example : eval (.sub (.num 5) (.num 2)) = some (.num 3) := by decide

/-- 引き算の結果が負になるときは`0`になる． -/
example : eval (.sub (.num 2) (.num 5)) = some (.num 0) := by decide

example : eval (.mul (.num 2) (.num 3)) = some (.num 6) := by decide

example : eval (.add (.num 1) (.mul (.num 2) (.num 3))) = some (.num 7) := by decide

example : eval .tru = some (.bool true) := by decide

example : eval (.ite .tru (.num 1) (.num 2)) = some (.num 1) := by decide

example : eval (.ite .fls (.num 1) (.num 2)) = some (.num 2) := by decide

example : eval (.iszero (.sub (.num 2) (.num 2))) = some (.bool true) := by decide

example : eval (.iszero (.num 5)) = some (.bool false) := by decide

/-- 数と真偽値は足せないので，評価が行き詰まる． -/
example : eval (.add (.num 1) .tru) = none := by decide

/-- 条件が真偽値でない`if`は，評価が行き詰まる． -/
example : eval (.ite (.num 1) (.num 2) (.num 3)) = none := by decide

/-- 選ばれない枝は評価しないので，行き詰まる式があってもよい． -/
example : eval (.ite .tru (.num 1) (.add (.num 1) .tru)) = some (.num 1) := by decide

/-! ## 式の等価性 -/

theorem eval_add_comm (t₁ t₂ : Term) : eval (.add t₁ t₂) = eval (.add t₂ t₁) := by
  simp only [eval]
  rcases eval t₁ with _ | _ | _ <;> rcases eval t₂ with _ | _ | _ <;> simp [Nat.add_comm]

theorem eval_add_assoc (t₁ t₂ t₃ : Term) :
    eval (.add (.add t₁ t₂) t₃) = eval (.add t₁ (.add t₂ t₃)) := by
  simp only [eval]
  rcases eval t₁ with _ | _ | _ <;> rcases eval t₂ with _ | _ | _ <;>
    rcases eval t₃ with _ | _ | _ <;> simp [Nat.add_assoc]

theorem eval_mul_comm (t₁ t₂ : Term) : eval (.mul t₁ t₂) = eval (.mul t₂ t₁) := by
  simp only [eval]
  rcases eval t₁ with _ | _ | _ <;> rcases eval t₂ with _ | _ | _ <;> simp [Nat.mul_comm]

theorem eval_mul_assoc (t₁ t₂ t₃ : Term) :
    eval (.mul (.mul t₁ t₂) t₃) = eval (.mul t₁ (.mul t₂ t₃)) := by
  simp only [eval]
  rcases eval t₁ with _ | _ | _ <;> rcases eval t₂ with _ | _ | _ <;>
    rcases eval t₃ with _ | _ | _ <;> simp [Nat.mul_assoc]

/-- `t`の値が数なら，`t * 1`と`t`は等価である． -/
theorem eval_mul_one {t : Term} {n : Nat} (h : eval t = some (.num n)) :
    eval (.mul t (.num 1)) = some (.num n) := by
  simp [eval, h]

/-- 真偽値があるので，`t * 1`と`t`はいつも等価とは限らない．`true * 1`は行き詰まる． -/
theorem eval_mul_one_not_equiv : ¬ ∀ t : Term, eval (.mul t (.num 1)) = eval t := by
  intro h
  have h' := h .tru
  simp [eval] at h'

/-- `-`は結合法則を満たさない．`(3 - 2) - 1`は`0`だが，`3 - (2 - 1)`は`2`である． -/
theorem eval_sub_not_assoc :
    ¬ ∀ t₁ t₂ t₃ : Term, eval (.sub (.sub t₁ t₂) t₃) = eval (.sub t₁ (.sub t₂ t₃)) := by
  intro h
  have h' := h (.num 3) (.num 2) (.num 1)
  simp [eval] at h'

/-! ## 大ステップ意味論との一致 -/

/-- 健全性：評価器が返す値は，大ステップ意味論でも式の値である． -/
theorem eval_sound {t : Term} {v : Value} (h : eval t = some v) : t ⇓ v := by
  induction t generalizing v with
  | num n => cases h; exact Eval.num
  | add t₁ t₂ ih₁ ih₂ =>
    unfold eval at h
    split at h
    · next h₁ h₂ => cases h; exact Eval.add (ih₁ h₁) (ih₂ h₂)
    · contradiction
  | sub t₁ t₂ ih₁ ih₂ =>
    unfold eval at h
    split at h
    · next h₁ h₂ => cases h; exact Eval.sub (ih₁ h₁) (ih₂ h₂)
    · contradiction
  | mul t₁ t₂ ih₁ ih₂ =>
    unfold eval at h
    split at h
    · next h₁ h₂ => cases h; exact Eval.mul (ih₁ h₁) (ih₂ h₂)
    · contradiction
  | tru => cases h; exact Eval.tru
  | fls => cases h; exact Eval.fls
  | ite c t e ihc iht ihe =>
    unfold eval at h
    split at h
    · next hc => exact Eval.iteTrue (ihc hc) (iht h)
    · next hc => exact Eval.iteFalse (ihc hc) (ihe h)
    · contradiction
  | iszero t ih =>
    unfold eval at h
    split at h
    · next ht => cases h; exact Eval.iszero (ih ht)
    · contradiction

/-- 完全性：大ステップ意味論で式の値が`v`なら，評価器も`v`を返す． -/
theorem eval_complete {t : Term} {v : Value} (h : t ⇓ v) : eval t = some v := by
  induction h with
  | num => rfl
  | add _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | sub _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [eval, ih₁, ih₂]
  | tru => rfl
  | fls => rfl
  | iteTrue _ _ ihc iht => simp [eval, ihc, iht]
  | iteFalse _ _ ihc ihe => simp [eval, ihc, ihe]
  | iszero _ ih => simp [eval, ih]

/-- 大ステップ意味論は決定的である．完全性から，どちらの値も`eval t`の値に等しい． -/
theorem eval_deterministic {t : Term} {v w : Value} (h₁ : t ⇓ v) (h₂ : t ⇓ w) : v = w := by
  have := (eval_complete h₁).symm.trans (eval_complete h₂)
  cases this
  rfl

/-! ## 1ステップの簡約 -/

example : step (.mul (.add (.num 1) (.num 2)) (.add (.num 3) (.num 4)))
    = some (.mul (.num 3) (.add (.num 3) (.num 4))) := by decide

example : step (.mul (.num 3) (.add (.num 3) (.num 4))) = some (.mul (.num 3) (.num 7)) := by decide

example : step (.num 21) = none := by decide

example : step (.ite (.iszero (.num 0)) (.num 1) (.num 2)) = some (.ite .tru (.num 1) (.num 2)) := by
  decide

example : step (.ite .tru (.num 1) (.num 2)) = some (.num 1) := by decide

/-- 行き詰まった式は簡約できない． -/
example : step (.add (.num 1) .tru) = none := by decide

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
  | tru => simp [step] at h
  | fls => simp [step] at h
  | ite c t e ihc _ _ =>
    unfold step at h
    split at h
    · cases h; exact .iteTrue
    · cases h; exact .iteFalse
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .ite (ihc hu)
  | iszero t ih =>
    unfold step at h
    split at h
    · cases h; exact .iszeroZero
    · cases h; exact .iszeroSucc
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .iszero (ih hu)

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
  | iteTrue => rfl
  | iteFalse => rfl
  | ite s ih => cases s <;> simp_all [step]
  | iszeroZero => rfl
  | iszeroSucc => rfl
  | iszero s ih => cases s <;> simp_all [step]

end MiniTest.EvalTest
