import Mini.Eval
import Mini.BigStep
import Mini.SmallStep
import MiniTest.Unit.SmallStepTest

/-!
# `Mini.Eval`の単体テスト
-/

namespace MiniTest.EvalTest

open Mini
open MiniTest.BigStepTest
open MiniTest.SmallStepTest

/-! ## 評価の例 -/

example : eval 100 (.num 3) = .ok (.num 3) := rfl

example : eval 100 (.add (.num 1) (.mul (.num 2) (.num 3))) = .ok (.num 7) := rfl

/-- 引き算の結果が負になるときは`0`になる． -/
example : eval 100 (.sub (.num 2) (.num 5)) = .ok (.num 0) := rfl

example : eval 100 (.ite (.iszero (.sub (.num 2) (.num 2))) (.num 1) (.num 2)) = .ok (.num 1) := rfl

example : eval 100 (.let_ "x" (.add (.num 1) (.num 2)) (.mul (.var "x") (.var "x"))) = .ok (.num 9) := rfl

/-- 行き詰まったときは，行き詰まった式を返す． -/
example : eval 100 (.add (.num 1) .tru) = .error (.stuck (.add (.num 1) .tru)) := rfl

example : eval 100 (.let_ "x" (.num 1) (.var "y")) = .error (.stuck (.var "y")) := rfl

/-- `1 + 2`を値にするには，簡約1ステップと値の確認で燃料が2つ要る． -/
example : eval 1 (.add (.num 1) (.num 2)) = .error .outOfFuel := rfl

example : eval 2 (.add (.num 1) (.num 2)) = .ok (.num 3) := rfl

/-- `fact 3`の値は`6`である． -/
example : eval 100 (.app factFn (.num 3)) = .ok (.num 6) := rfl

/-- `loop 0`は，どれだけ燃料を与えても燃料切れになる． -/
example (k : Nat) : eval k loopApp = .error .outOfFuel := by
  induction k with
  | zero => rfl
  | succ k ih => rw [eval]; exact ih

example : eval 100 (.fst (.pair (.add (.num 1) (.num 2)) .tru)) = .ok (.num 3) := rfl

/-- 組の値は，成分の値の組である． -/
example : eval 100 (.pair (.num 1) (.pair .tru (.add (.num 1) (.num 1))))
    = .ok (.pair (.num 1) (.pair (.bool true) (.num 2))) := rfl

example : eval 100 (.fst (.num 1)) = .error (.stuck (.fst (.num 1))) := rfl

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

example : step (.let_ "x" (.num 3) (.mul (.var "x") (.var "x"))) = some (.mul (.num 3) (.num 3)) := by
  decide

example : step (.var "x") = none := by decide

example : step loopApp = some loopApp := by decide

example : step (.pair (.num 1) (.add (.num 1) (.num 2))) = some (.pair (.num 1) (.num 3)) := by decide

/-- 値を表す組は簡約できない． -/
example : step (.pair (.num 1) .tru) = none := by decide

example : step (.snd (.pair (.num 1) .tru)) = some .tru := by decide

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
  | var x => simp [step] at h
  | let_ x t u iht _ =>
    unfold step at h
    split at h
    · next hv => cases h; exact .letV (toValue?_isValue hv)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u', hu, rfl⟩ := h
      exact .letL (iht hu)
  | lam x A t _ => simp [step] at h
  | fix f x A B t _ => simp [step] at h
  | app t₁ t₂ ih₁ ih₂ =>
    unfold step at h
    split at h
    · next _ _ x A b _ hv₁ hv₂ =>
      cases h
      rw [toValue?_some hv₁]
      exact .beta (toValue?_isValue hv₂)
    · next _ _ f x A B b _ hv₁ hv₂ =>
      cases h
      rw [toValue?_some hv₁]
      exact .betaFix (toValue?_isValue hv₂)
    · contradiction
    · next _ _ _ hv₁ _ =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .app2 (toValue?_isValue hv₁) (ih₂ hu)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .app1 (ih₁ hu)
  | pair t u ih₁ ih₂ =>
    unfold step at h
    split at h
    · contradiction
    · next _ _ _ hv _ =>
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨u', hu, rfl⟩ := h
      exact .pairR (toValue?_isValue hv) (ih₂ hu)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      exact .pairL (ih₁ ht)
  | fst t ih =>
    unfold step at h
    split at h
    · next v w hv =>
      cases h
      rw [toValue?_some hv]
      exact .fstPair (isValue_toTerm v) (isValue_toTerm w)
    · contradiction
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .fst (ih hu)
  | snd t ih =>
    unfold step at h
    split at h
    · next v w hv =>
      cases h
      rw [toValue?_some hv]
      exact .sndPair (isValue_toTerm v) (isValue_toTerm w)
    · contradiction
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .snd (ih hu)

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
  | letL s ih => simp [step, toValue?_of_step s, ih]
  | letV hv =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    simp [step, toValue?_toTerm]
  | app1 s ih => simp [step, toValue?_of_step s, ih]
  | app2 hv s ih =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    simp [step, toValue?_toTerm, toValue?_of_step s, ih]
  | beta hv =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    simp [step, Term.toValue?, toValue?_toTerm]
  | betaFix hv =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    simp [step, Term.toValue?, toValue?_toTerm]
  | pairL s ih => simp [step, toValue?_of_step s, ih]
  | pairR hv s ih =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    simp [step, toValue?_toTerm, toValue?_of_step s, ih]
  | fst s ih => simp [step, toValue?_of_step s, ih]
  | fstPair hv hw =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    obtain ⟨w, rfl⟩ := isValue_exists_value hw
    simp [step, Term.toValue?, toValue?_toTerm]
  | snd s ih => simp [step, toValue?_of_step s, ih]
  | sndPair hv hw =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    obtain ⟨w, rfl⟩ := isValue_exists_value hw
    simp [step, Term.toValue?, toValue?_toTerm]

/-! ## 小ステップ意味論との一致 -/

/-- 健全性：評価器が返す値は，大ステップ意味論でも式の値である． -/
theorem eval_sound {k : Nat} {t : Term} {v : Value} (h : eval k t = .ok v) : t ⇓ v := by
  induction k generalizing t with
  | zero => cases h
  | succ k ih =>
    unfold eval at h
    split at h
    · next hv =>
      cases h
      rw [toValue?_some hv]
      exact value_bigstep _
    · split at h
      · next t' hs => exact step_bigstep (step_sound hs) (ih h)
      · contradiction

/-- `t`が何ステップかで`v`を表す式に簡約されるなら，十分な燃料で評価器は`v`を返す． -/
theorem eval_of_steps {t : Term} {v : Value} (h : t ⟶* v.toTerm) : ∃ k, eval k t = .ok v := by
  generalize hu : v.toTerm = u at h
  induction h with
  | refl =>
    subst hu
    exact ⟨1, by simp [eval, toValue?_toTerm]⟩
  | step s _ ih =>
    obtain ⟨k, hk⟩ := ih hu
    exact ⟨k + 1, by simp [eval, toValue?_of_step s, step_complete s, hk]⟩

/-- 完全性：大ステップ意味論で式の値が`v`なら，十分な燃料で評価器は`v`を返す． -/
theorem eval_complete {t : Term} {v : Value} (h : t ⇓ v) : ∃ k, eval k t = .ok v :=
  eval_of_steps (bigstep_steps h)

/-- 評価器が式`t'`で行き詰まったと報告するなら，`t`は`t'`に簡約され，`t'`は行き詰まっている． -/
theorem eval_stuck {k : Nat} {t t' : Term} (h : eval k t = .error (.stuck t')) : t ⟶* t' ∧ Stuck t' := by
  induction k generalizing t with
  | zero => cases h
  | succ k ih =>
    unfold eval at h
    split at h
    · contradiction
    · next hv =>
      split at h
      · next t'' hs =>
        obtain ⟨s, st⟩ := ih h
        exact ⟨.step (step_sound hs) s, st⟩
      · next hs =>
        cases h
        refine ⟨.refl, fun u su => ?_, fun v hv' => ?_⟩
        · simp [step_complete su] at hs
        · simp [hv', toValue?_toTerm] at hv

end MiniTest.EvalTest
