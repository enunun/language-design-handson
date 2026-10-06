import Mini.SmallStep
import Mini.BigStep

/-!
# `Mini.SmallStep`の単体テスト
-/

namespace MiniTest.SmallStepTest

open Mini

/-! ## 簡約の例 -/

/-- 左の部分式から簡約する． -/
example : Term.mul (.add (.num 1) (.num 2)) (.add (.num 3) (.num 4))
    ⟶ .mul (.num 3) (.add (.num 3) (.num 4)) :=
  Step.mulL Step.add

/-- 左の部分式が数になったら，右の部分式を簡約する． -/
example : Term.mul (.num 3) (.add (.num 3) (.num 4)) ⟶ .mul (.num 3) (.num 7) :=
  Step.mulR Step.add

example : Term.mul (.num 3) (.num 7) ⟶ .num 21 := Step.mul

/-- 左の部分式が数になるまで，右の部分式は簡約しない． -/
example : ¬ Term.add (.add (.num 1) (.num 2)) (.add (.num 3) (.num 4))
    ⟶ .add (.add (.num 1) (.num 2)) (.num 7) := by
  intro h
  cases h

example : Term.mul (.add (.num 1) (.num 2)) (.add (.num 3) (.num 4)) ⟶* .num 21 :=
  .step (.mulL .add) (.step (.mulR .add) (.step .mul .refl))

/-! ## 正規形と決定性 -/

/-- 数はそれ以上簡約できない． -/
theorem num_normal {n : Nat} {t : Term} : ¬ Term.num n ⟶ t := by
  intro h
  cases h

/-- 小ステップ意味論は決定的である．1ステップで簡約した結果は1つに決まる． -/
theorem step_deterministic {t t₁ t₂ : Term} (h₁ : t ⟶ t₁) (h₂ : t ⟶ t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | addL h ih =>
    cases h₂ with
    | addL h' => rw [ih h']
    | addR _ => cases h
    | add => cases h
  | addR h ih =>
    cases h₂ with
    | addL h' => cases h'
    | addR h' => rw [ih h']
    | add => cases h
  | add =>
    cases h₂ with
    | addL h' => cases h'
    | addR h' => cases h'
    | add => rfl
  | subL h ih =>
    cases h₂ with
    | subL h' => rw [ih h']
    | subR _ => cases h
    | sub => cases h
  | subR h ih =>
    cases h₂ with
    | subL h' => cases h'
    | subR h' => rw [ih h']
    | sub => cases h
  | sub =>
    cases h₂ with
    | subL h' => cases h'
    | subR h' => cases h'
    | sub => rfl
  | mulL h ih =>
    cases h₂ with
    | mulL h' => rw [ih h']
    | mulR _ => cases h
    | mul => cases h
  | mulR h ih =>
    cases h₂ with
    | mulL h' => cases h'
    | mulR h' => rw [ih h']
    | mul => cases h
  | mul =>
    cases h₂ with
    | mulL h' => cases h'
    | mulR h' => cases h'
    | mul => rfl

/-! ## 多ステップ簡約の補題 -/

theorem Steps.single {t t' : Term} (h : t ⟶ t') : t ⟶* t' :=
  .step h .refl

theorem Steps.trans {t t' t'' : Term} (h₁ : t ⟶* t') (h₂ : t' ⟶* t'') : t ⟶* t'' := by
  induction h₁ with
  | refl => exact h₂
  | step s _ ih => exact .step s (ih h₂)

theorem Steps.addL {t₁ t₁' t₂ : Term} (h : t₁ ⟶* t₁') : Term.add t₁ t₂ ⟶* .add t₁' t₂ := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.addL s) ih

theorem Steps.addR {n₁ : Nat} {t₂ t₂' : Term} (h : t₂ ⟶* t₂') :
    Term.add (.num n₁) t₂ ⟶* .add (.num n₁) t₂' := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.addR s) ih

theorem Steps.subL {t₁ t₁' t₂ : Term} (h : t₁ ⟶* t₁') : Term.sub t₁ t₂ ⟶* .sub t₁' t₂ := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.subL s) ih

theorem Steps.subR {n₁ : Nat} {t₂ t₂' : Term} (h : t₂ ⟶* t₂') :
    Term.sub (.num n₁) t₂ ⟶* .sub (.num n₁) t₂' := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.subR s) ih

theorem Steps.mulL {t₁ t₁' t₂ : Term} (h : t₁ ⟶* t₁') : Term.mul t₁ t₂ ⟶* .mul t₁' t₂ := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.mulL s) ih

theorem Steps.mulR {n₁ : Nat} {t₂ t₂' : Term} (h : t₂ ⟶* t₂') :
    Term.mul (.num n₁) t₂ ⟶* .mul (.num n₁) t₂' := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.mulR s) ih

/-! ## 大ステップ意味論との一致 -/

/-- 大ステップ意味論で`t`の値が`n`なら，`t`は何ステップかで`n`に簡約される． -/
theorem bigstep_steps {t : Term} {n : Nat} (h : t ⇓ n) : t ⟶* .num n := by
  induction h with
  | num => exact .refl
  | add _ _ ih₁ ih₂ => exact Steps.trans (Steps.addL ih₁) (Steps.trans (Steps.addR ih₂) (Steps.single .add))
  | sub _ _ ih₁ ih₂ => exact Steps.trans (Steps.subL ih₁) (Steps.trans (Steps.subR ih₂) (Steps.single .sub))
  | mul _ _ ih₁ ih₂ => exact Steps.trans (Steps.mulL ih₁) (Steps.trans (Steps.mulR ih₂) (Steps.single .mul))

/-- 1ステップ簡約した式の値は，簡約する前の式の値でもある． -/
theorem step_bigstep {t t' : Term} {n : Nat} (s : t ⟶ t') (h : t' ⇓ n) : t ⇓ n := by
  induction s generalizing n with
  | addL _ ih => cases h with | add h₁ h₂ => exact .add (ih h₁) h₂
  | addR _ ih => cases h with | add h₁ h₂ => exact .add h₁ (ih h₂)
  | add => cases h; exact .add .num .num
  | subL _ ih => cases h with | sub h₁ h₂ => exact .sub (ih h₁) h₂
  | subR _ ih => cases h with | sub h₁ h₂ => exact .sub h₁ (ih h₂)
  | sub => cases h; exact .sub .num .num
  | mulL _ ih => cases h with | mul h₁ h₂ => exact .mul (ih h₁) h₂
  | mulR _ ih => cases h with | mul h₁ h₂ => exact .mul h₁ (ih h₂)
  | mul => cases h; exact .mul .num .num

/-- `t`が何ステップかで`n`に簡約されるなら，大ステップ意味論で`t`の値は`n`である． -/
theorem steps_bigstep {t : Term} {n : Nat} (h : t ⟶* .num n) : t ⇓ n := by
  generalize hu : Term.num n = u at h
  induction h with
  | refl => subst hu; exact .num
  | step s _ ih => exact step_bigstep s (ih hu)

/-- 2つの意味論は一致する． -/
theorem bigstep_iff_steps {t : Term} {n : Nat} : t ⇓ n ↔ t ⟶* .num n :=
  ⟨bigstep_steps, steps_bigstep⟩

end MiniTest.SmallStepTest
