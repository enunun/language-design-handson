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

/-- `if`は，条件を先に簡約する． -/
example : Term.ite (.iszero (.num 0)) (.num 1) (.num 2) ⟶ .ite .tru (.num 1) (.num 2) :=
  Step.ite Step.iszeroZero

example : Term.ite .tru (.num 1) (.num 2) ⟶ .num 1 := Step.iteTrue

example : Term.iszero (.num 5) ⟶ .fls := Step.iszeroSucc

/-- 条件が真偽値になるまで，`if`の枝は簡約しない． -/
example : ¬ Term.ite (.iszero (.num 0)) (.add (.num 1) (.num 2)) (.num 0)
    ⟶ .ite (.iszero (.num 0)) (.num 3) (.num 0) := by
  intro h
  cases h

/-- `1 + true`は行き詰まっている． -/
example : Stuck (.add (.num 1) .tru) := by
  constructor
  · intro t h
    cases h with
    | addL h => cases h
    | addR h => cases h
  · intro v h
    cases v with
    | num n => cases h
    | bool b => cases b <;> cases h

/-! ## 正規形と決定性 -/

/-- 数はそれ以上簡約できない． -/
theorem num_normal {n : Nat} {t : Term} : ¬ Term.num n ⟶ t := by
  intro h
  cases h

/-- 値を表す式は，それ以上簡約できない． -/
theorem value_normal (v : Value) : Normal v.toTerm := by
  intro t h
  cases v with
  | num n => cases h
  | bool b => cases b <;> cases h

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
  | iteTrue =>
    cases h₂ with
    | iteTrue => rfl
    | ite h' => cases h'
  | iteFalse =>
    cases h₂ with
    | iteFalse => rfl
    | ite h' => cases h'
  | ite h ih =>
    cases h₂ with
    | iteTrue => cases h
    | iteFalse => cases h
    | ite h' => rw [ih h']
  | iszeroZero =>
    cases h₂ with
    | iszeroZero => rfl
    | iszero h' => cases h'
  | iszeroSucc =>
    cases h₂ with
    | iszeroSucc => rfl
    | iszero h' => cases h'
  | iszero h ih =>
    cases h₂ with
    | iszeroZero => cases h
    | iszeroSucc => cases h
    | iszero h' => rw [ih h']

/-! ## 評価の順序を変えた意味論

`if`の`then`の枝を，条件より先に簡約してもよいとする規則を足すと，決定性が成り立たなくなる．
-/

/-- `Step`に，`then`の枝を簡約する規則`iteThen`を足した簡約． -/
inductive StepEager : Term → Term → Prop where
  | base {t t' : Term} : t ⟶ t' → StepEager t t'
  | iteThen {c t t' e : Term} : StepEager t t' → StepEager (.ite c t e) (.ite c t' e)

/-- `StepEager`は決定的ではない．`if true then 1 + 2 else 0`は2通りに簡約できる． -/
theorem stepEager_not_deterministic :
    ¬ ∀ t t₁ t₂, StepEager t t₁ → StepEager t t₂ → t₁ = t₂ := by
  intro h
  have := h (.ite .tru (.add (.num 1) (.num 2)) (.num 0)) (.add (.num 1) (.num 2))
    (.ite .tru (.num 3) (.num 0)) (.base .iteTrue) (.iteThen (.base .add))
  cases this

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

theorem Steps.ite {c c' t e : Term} (h : c ⟶* c') : Term.ite c t e ⟶* .ite c' t e := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.ite s) ih

theorem Steps.iszero {t t' : Term} (h : t ⟶* t') : Term.iszero t ⟶* .iszero t' := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.iszero s) ih

/-! ## 大ステップ意味論との一致 -/

/-- 大ステップ意味論で`t`の値が`v`なら，`t`は何ステップかで`v`を表す式に簡約される． -/
theorem bigstep_steps {t : Term} {v : Value} (h : t ⇓ v) : t ⟶* v.toTerm := by
  induction h with
  | num => exact .refl
  | add _ _ ih₁ ih₂ => exact Steps.trans (Steps.addL ih₁) (Steps.trans (Steps.addR ih₂) (Steps.single .add))
  | sub _ _ ih₁ ih₂ => exact Steps.trans (Steps.subL ih₁) (Steps.trans (Steps.subR ih₂) (Steps.single .sub))
  | mul _ _ ih₁ ih₂ => exact Steps.trans (Steps.mulL ih₁) (Steps.trans (Steps.mulR ih₂) (Steps.single .mul))
  | tru => exact .refl
  | fls => exact .refl
  | iteTrue _ _ ihc iht => exact Steps.trans (Steps.ite ihc) (.step .iteTrue iht)
  | iteFalse _ _ ihc ihe => exact Steps.trans (Steps.ite ihc) (.step .iteFalse ihe)
  | @iszero _ n _ ih =>
    cases n with
    | zero => exact Steps.trans (Steps.iszero ih) (Steps.single .iszeroZero)
    | succ n => exact Steps.trans (Steps.iszero ih) (Steps.single .iszeroSucc)

/-- 値を表す式は，その値に評価される． -/
theorem value_bigstep (v : Value) : v.toTerm ⇓ v := by
  cases v with
  | num n => exact .num
  | bool b => cases b with
    | true => exact .tru
    | false => exact .fls

/-- 1ステップ簡約した式の値は，簡約する前の式の値でもある． -/
theorem step_bigstep {t t' : Term} {v : Value} (s : t ⟶ t') (h : t' ⇓ v) : t ⇓ v := by
  induction s generalizing v with
  | addL _ ih => cases h with | add h₁ h₂ => exact .add (ih h₁) h₂
  | addR _ ih => cases h with | add h₁ h₂ => exact .add h₁ (ih h₂)
  | add => cases h; exact .add .num .num
  | subL _ ih => cases h with | sub h₁ h₂ => exact .sub (ih h₁) h₂
  | subR _ ih => cases h with | sub h₁ h₂ => exact .sub h₁ (ih h₂)
  | sub => cases h; exact .sub .num .num
  | mulL _ ih => cases h with | mul h₁ h₂ => exact .mul (ih h₁) h₂
  | mulR _ ih => cases h with | mul h₁ h₂ => exact .mul h₁ (ih h₂)
  | mul => cases h; exact .mul .num .num
  | iteTrue => exact .iteTrue .tru h
  | iteFalse => exact .iteFalse .fls h
  | ite _ ih =>
    cases h with
    | iteTrue hc ht => exact .iteTrue (ih hc) ht
    | iteFalse hc he => exact .iteFalse (ih hc) he
  | iszeroZero => cases h; exact .iszero (n := 0) .num
  | iszeroSucc => cases h; exact .iszero .num
  | iszero _ ih => cases h with | iszero h => exact .iszero (ih h)

/-- `t`が何ステップかで`v`を表す式に簡約されるなら，大ステップ意味論で`t`の値は`v`である． -/
theorem steps_bigstep {t : Term} {v : Value} (h : t ⟶* v.toTerm) : t ⇓ v := by
  generalize hu : v.toTerm = u at h
  induction h with
  | refl => subst hu; exact value_bigstep v
  | step s _ ih => exact step_bigstep s (ih hu)

/-- 2つの意味論は一致する． -/
theorem bigstep_iff_steps {t : Term} {v : Value} : t ⇓ v ↔ t ⟶* v.toTerm :=
  ⟨bigstep_steps, steps_bigstep⟩

end MiniTest.SmallStepTest
