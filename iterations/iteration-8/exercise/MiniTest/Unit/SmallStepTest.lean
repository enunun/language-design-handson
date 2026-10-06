import Mini.SmallStep
import Mini.BigStep
import MiniTest.Unit.BigStepTest

/-!
# `Mini.SmallStep`の単体テスト
-/

namespace MiniTest.SmallStepTest

open Mini
open MiniTest.BigStepTest

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

/-- `let`は，束縛する式を値まで簡約してから，本体の変数を置き換える． -/
example : Term.let_ "x" (.add (.num 1) (.num 2)) (.mul (.var "x") (.var "x"))
    ⟶ .let_ "x" (.num 3) (.mul (.var "x") (.var "x")) :=
  Step.letL Step.add

example : Term.let_ "x" (.num 3) (.mul (.var "x") (.var "x")) ⟶ .mul (.num 3) (.num 3) :=
  Step.letV IsValue.num

/-- 関数適用は，引数を値まで簡約してから，本体の変数を置き換える． -/
example : Term.app (.lam "x" .nat (.add (.var "x") (.num 1))) (.add (.num 1) (.num 1))
    ⟶ .app (.lam "x" .nat (.add (.var "x") (.num 1))) (.num 2) :=
  Step.app2 IsValue.lam Step.add

example : Term.app (.lam "x" .nat (.add (.var "x") (.num 1))) (.num 2) ⟶ .add (.num 2) (.num 1) :=
  Step.beta IsValue.num

/-- 関数でない値の適用は行き詰まる． -/
example : Stuck (.app (.num 1) (.num 2)) := by
  constructor
  · intro t h
    cases h with
    | app1 h => cases h
    | app2 _ h => cases h
  · intro v h
    cases v with
    | num n => cases h
    | bool b => cases b <;> cases h
    | lam x A t => cases h
    | fix f x A B t => cases h

/-- 自由な変数は行き詰まっている． -/
example : Stuck (.var "x") := by
  constructor
  · intro t h
    cases h
  · intro v h
    cases v with
    | num n => cases h
    | bool b => cases b <;> cases h
    | lam x A t => cases h
    | fix f x A B t => cases h

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
    | lam x A t => cases h
    | fix f x A B t => cases h

/-- 再帰関数の適用は，引数の変数と関数の名前の両方を置き換える．`loop 0`は1ステップで自分自身に戻る． -/
example : loopApp ⟶ loopApp := Step.betaFix IsValue.num

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
  | lam x A t => cases h
  | fix f x A B t => cases h

/-! ## 値を表す式の補題 -/

theorem isValue_toTerm (v : Value) : IsValue v.toTerm := by
  cases v with
  | num n => exact .num
  | bool b => cases b <;> constructor
  | lam x A t => exact .lam
  | fix f x A B t => exact .fix

theorem isValue_exists_value {t : Term} (h : IsValue t) : ∃ v : Value, t = v.toTerm := by
  cases h with
  | num => exact ⟨.num _, rfl⟩
  | tru => exact ⟨.bool true, rfl⟩
  | fls => exact ⟨.bool false, rfl⟩
  | lam => exact ⟨.lam _ _ _, rfl⟩
  | fix => exact ⟨.fix _ _ _ _ _, rfl⟩

theorem isValue_normal {t t' : Term} (h : IsValue t) : ¬ t ⟶ t' := by
  obtain ⟨v, rfl⟩ := isValue_exists_value h
  exact value_normal v t'

theorem toValue?_toTerm (v : Value) : v.toTerm.toValue? = some v := by
  cases v with
  | num n => rfl
  | bool b => cases b <;> rfl
  | lam x A t => rfl
  | fix f x A B t => rfl

theorem toValue?_some {t : Term} {v : Value} (h : t.toValue? = some v) : t = v.toTerm := by
  cases t <;> simp [Term.toValue?] at h <;> subst h <;> rfl

theorem toValue?_isValue {t : Term} {v : Value} (h : t.toValue? = some v) : IsValue t := by
  rw [toValue?_some h]
  exact isValue_toTerm v

theorem toValue?_of_step {t t' : Term} (s : t ⟶ t') : t.toValue? = none := by
  cases s <;> rfl

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
  | letL h ih =>
    cases h₂ with
    | letL h' => rw [ih h']
    | letV hv => exact absurd h (isValue_normal hv)
  | letV hv =>
    cases h₂ with
    | letL h' => exact absurd h' (isValue_normal hv)
    | letV _ => rfl
  | app1 h ih =>
    cases h₂ with
    | app1 h' => rw [ih h']
    | app2 hv _ => exact absurd h (isValue_normal hv)
    | beta _ => cases h
    | betaFix _ => cases h
  | app2 hv h ih =>
    cases h₂ with
    | app1 h' => exact absurd h' (isValue_normal hv)
    | app2 _ h' => rw [ih h']
    | beta hv' => exact absurd h (isValue_normal hv')
    | betaFix hv' => exact absurd h (isValue_normal hv')
  | beta hv =>
    cases h₂ with
    | app1 h' => cases h'
    | app2 _ h' => exact absurd h' (isValue_normal hv)
    | beta _ => rfl
  | betaFix hv =>
    cases h₂ with
    | app1 h' => cases h'
    | app2 _ h' => exact absurd h' (isValue_normal hv)
    | betaFix _ => rfl

/-- `loop 0`から簡約して着く式は，`loop 0`だけである．したがって`loop 0`は値に着かない． -/
example {t : Term} (h : loopApp ⟶* t) : t = loopApp := by
  suffices ∀ s, s ⟶* t → s = loopApp → t = loopApp from this _ h rfl
  clear h
  intro s hs
  induction hs with
  | refl => exact id
  | step h₁ _ ih =>
    intro heq
    subst heq
    exact ih (step_deterministic h₁ (Step.betaFix IsValue.num))

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

theorem Steps.letL {x : String} {t t' u : Term} (h : t ⟶* t') : Term.let_ x t u ⟶* .let_ x t' u := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.letL s) ih

theorem Steps.app1 {t₁ t₁' t₂ : Term} (h : t₁ ⟶* t₁') : Term.app t₁ t₂ ⟶* .app t₁' t₂ := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.app1 s) ih

theorem Steps.app2 {v₁ t₂ t₂' : Term} (hv : IsValue v₁) (h : t₂ ⟶* t₂') : Term.app v₁ t₂ ⟶* .app v₁ t₂' := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.app2 hv s) ih

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
  | @let_ x t u v w _ _ ih₁ ih₂ =>
    exact Steps.trans (Steps.letL ih₁) (.step (.letV (isValue_toTerm v)) ih₂)
  | lam => exact .refl
  | @app t₁ t₂ b x A v₂ v _ _ _ ih₁ ih₂ ih₃ =>
    exact Steps.trans (Steps.app1 ih₁)
      (Steps.trans (Steps.app2 .lam ih₂) (.step (.beta (isValue_toTerm v₂)) ih₃))
  | fix => exact .refl
  | @appFix t₁ t₂ b f x A B v₂ v _ _ _ ih₁ ih₂ ih₃ =>
    exact Steps.trans (Steps.app1 ih₁)
      (Steps.trans (Steps.app2 .fix ih₂) (.step (.betaFix (isValue_toTerm v₂)) ih₃))

/-- 値を表す式は，その値に評価される． -/
theorem value_bigstep (v : Value) : v.toTerm ⇓ v := by
  cases v with
  | num n => exact .num
  | bool b => cases b with
    | true => exact .tru
    | false => exact .fls
  | lam x A t => exact .lam
  | fix f x A B t => exact .fix

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
  | letL _ ih => cases h with | let_ h₁ h₂ => exact .let_ (ih h₁) h₂
  | letV hv =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    exact .let_ (value_bigstep v) h
  | app1 _ ih =>
    cases h with
    | app h₁ h₂ h₃ => exact .app (ih h₁) h₂ h₃
    | appFix h₁ h₂ h₃ => exact .appFix (ih h₁) h₂ h₃
  | app2 _ _ ih =>
    cases h with
    | app h₁ h₂ h₃ => exact .app h₁ (ih h₂) h₃
    | appFix h₁ h₂ h₃ => exact .appFix h₁ (ih h₂) h₃
  | beta hv =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    exact .app .lam (value_bigstep v) h
  | betaFix hv =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    exact .appFix .fix (value_bigstep v) h

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
