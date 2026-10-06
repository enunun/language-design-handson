import Mini.Typing
import Mini.SmallStep
import Mini.Eval
import MiniTest.Unit.EvalTest

/-!
# `Mini.Typing`の単体テスト
-/

namespace MiniTest.TypingTest

open Mini
open MiniTest.BigStepTest
open MiniTest.SmallStepTest

/-! ## 型付けの例 -/

example : HasType [] (.add (.num 1) (.num 2)) .nat := .add .num .num

example : HasType [] (.ite (.iszero (.num 0)) (.num 1) (.num 2)) .nat := .ite (.iszero .num) .num .num

/-- `let`の本体は，束縛した変数の型を文脈に加えて型を付ける． -/
example : HasType [] (.let_ "x" (.num 1) (.add (.var "x") (.num 2))) .nat :=
  .let_ .num (.add (.var rfl) .num)

/-- 文脈にない変数には型が付かない． -/
example : ¬ ∃ T, HasType [] (.var "x") T := by
  intro ⟨T, h⟩
  cases h with
  | var hx => cases hx

/-- `1 + true`には型が付かない． -/
example : ¬ ∃ T, HasType [] (.add (.num 1) .tru) T := by
  intro ⟨T, h⟩
  cases h with
  | add _ h₂ => cases h₂

/-- 型システムは安全側に倒した近似である．`if true then 0 else false`は値`0`に評価されるが，型が付かない． -/
example : eval 100 (.ite .tru (.num 0) .fls) = .ok (.num 0) ∧ ¬ ∃ T, HasType [] (.ite .tru (.num 0) .fls) T := by
  constructor
  · rfl
  · intro ⟨T, h⟩
    cases h with
    | ite _ ht he =>
      cases ht
      cases he

example : HasType [] (.lam "x" .nat (.iszero (.var "x"))) (.arrow .nat .bool) :=
  .lam (.iszero (.var rfl))

example : HasType [] (.app (.lam "x" .nat (.var "x")) (.num 1)) .nat := .app (.lam (.var rfl)) .num

/-- 引数の型が関数の引数の型と合わない適用には，型が付かない． -/
example : ¬ ∃ T, HasType [] (.app (.lam "x" .nat (.var "x")) .tru) T := by
  intro ⟨T, h⟩
  cases h with
  | app h₁ h₂ =>
    cases h₁
    cases h₂

/-- 再帰関数の本体は，引数の変数と関数自身の型を文脈に加えて型を付ける． -/
example : HasType [] factFn (.arrow .nat .nat) :=
  .fix (.ite (.iszero (.var rfl)) .num (.mul (.var rfl) (.app (.var rfl) (.sub (.var rfl) .num))))

/-- 評価が終わらない`loop 0`にも型が付く．型が付くことは，評価が終わることを意味しない． -/
example : HasType [] loopApp .nat := .app (.fix (.app (.var rfl) (.var rfl))) .num

/-! ## 型検査器 -/

example : typeOf [] (.ite (.iszero (.num 0)) (.num 1) (.num 2)) = .ok .nat := rfl

example : typeOf [] (.add (.num 1) .tru) = .error (.mismatch "+の右辺" .nat .bool) := rfl

example : typeOf [] (.ite (.num 1) (.num 2) (.num 3)) = .error (.mismatch "ifの条件" .bool .nat) := rfl

example : typeOf [] (.ite .tru (.num 1) .fls) = .error (.branches .nat .bool) := rfl

example : typeOf [] (.let_ "x" (.num 1) (.var "y")) = .error (.unbound "y") := rfl

example : typeOf [] (.lam "x" .nat (.iszero (.var "x"))) = .ok (.arrow .nat .bool) := rfl

example : typeOf [] (.app (.lam "x" .nat (.var "x")) .tru) = .error (.mismatch "関数の引数" .nat .bool) := rfl

example : typeOf [] (.app (.num 1) (.num 2)) = .error (.notFunction .nat) := rfl

example : typeOf [] factFn = .ok (.arrow .nat .nat) := rfl

/-- 本体の型が，注釈した結果の型と合わない． -/
example : typeOf [] (.fix "f" "x" .nat .bool (.var "x")) = .error (.mismatch "再帰関数の本体" .bool .nat) := rfl

/-- 内側の束縛が外側の束縛を隠す． -/
example : typeOf [] (.let_ "x" (.num 1) (.let_ "x" .tru (.var "x"))) = .ok .bool := rfl

/-- 型検査器の健全性：型検査器が返す型は，型付け規則でも式の型である． -/
theorem typeOf_sound {Γ : Ctx} {t : Term} {T : Ty} (h : typeOf Γ t = .ok T) : HasType Γ t T := by
  induction t generalizing Γ T with
  | num n => cases h; exact .num
  | add t₁ t₂ ih₁ ih₂ =>
    unfold typeOf at h
    split at h <;> first | contradiction | (next h₁ h₂ => cases h; exact .add (ih₁ h₁) (ih₂ h₂))
  | sub t₁ t₂ ih₁ ih₂ =>
    unfold typeOf at h
    split at h <;> first | contradiction | (next h₁ h₂ => cases h; exact .sub (ih₁ h₁) (ih₂ h₂))
  | mul t₁ t₂ ih₁ ih₂ =>
    unfold typeOf at h
    split at h <;> first | contradiction | (next h₁ h₂ => cases h; exact .mul (ih₁ h₁) (ih₂ h₂))
  | tru => cases h; exact .tru
  | fls => cases h; exact .fls
  | ite c t e ihc iht ihe =>
    unfold typeOf at h
    split at h
    · next hc ht he =>
      split at h
      · next hTE => cases h; subst hTE; exact .ite (ihc hc) (iht ht) (ihe he)
      · contradiction
    all_goals contradiction
  | iszero t ih =>
    unfold typeOf at h
    split at h <;> first | contradiction | (next ht => cases h; exact .iszero (ih ht))
  | var x =>
    unfold typeOf at h
    split at h
    · next hx => cases h; exact .var hx
    · contradiction
  | let_ x t u iht ihu =>
    unfold typeOf at h
    split at h
    · next ht => exact .let_ (iht ht) (ihu h)
    · contradiction
  | lam x A t ih =>
    unfold typeOf at h
    split at h
    · next ht => cases h; exact .lam (ih ht)
    · contradiction
  | app t₁ t₂ ih₁ ih₂ =>
    unfold typeOf at h
    split at h
    · next h₁ h₂ =>
      split at h
      · next hA => cases h; subst hA; exact .app (ih₁ h₁) (ih₂ h₂)
      · contradiction
    all_goals contradiction
  | fix f x A B t ih =>
    unfold typeOf at h
    split at h
    · next ht =>
      split at h
      · next hB => cases h; subst hB; exact .fix (ih ht)
      · contradiction
    · contradiction

/-- 型検査器の完全性：型付け規則で式の型が`T`なら，型検査器も`T`を返す． -/
theorem typeOf_complete {Γ : Ctx} {t : Term} {T : Ty} (h : HasType Γ t T) : typeOf Γ t = .ok T := by
  induction h with
  | num => rfl
  | add _ _ ih₁ ih₂ => simp [typeOf, ih₁, ih₂]
  | sub _ _ ih₁ ih₂ => simp [typeOf, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [typeOf, ih₁, ih₂]
  | tru => rfl
  | fls => rfl
  | ite _ _ _ ihc iht ihe => simp [typeOf, ihc, iht, ihe]
  | iszero _ ih => simp [typeOf, ih]
  | var hx => simp [typeOf, hx]
  | let_ _ _ ih₁ ih₂ => simp [typeOf, ih₁, ih₂]
  | lam _ ih => simp [typeOf, ih]
  | app _ _ ih₁ ih₂ => simp [typeOf, ih₁, ih₂]
  | fix _ ih => simp [typeOf, ih]

/-- 式の型は1つに決まる．完全性から，どちらの型も`typeOf Γ t`の結果に等しい． -/
theorem type_unique {Γ : Ctx} {t : Term} {T U : Ty} (h₁ : HasType Γ t T) (h₂ : HasType Γ t U) : T = U := by
  have := (typeOf_complete h₁).symm.trans (typeOf_complete h₂)
  cases this
  rfl

/-! ## 文脈の弱化と置換補題 -/

/-- 文脈`Γ`の変数がすべて，同じ型で文脈`Δ`にもあること． -/
def Included (Γ Δ : Ctx) : Prop := ∀ x A, Γ.lookup x = some A → Δ.lookup x = some A

theorem Included.cons {Γ Δ : Ctx} {x : String} {T : Ty} (h : Included Γ Δ) :
    Included ((x, T) :: Γ) ((x, T) :: Δ) := by
  intro y A hy
  by_cases hyx : y = x <;> simp_all [Ctx.lookup]
  exact h y A hy

/-- 弱化：文脈を広げても，型付けは保たれる． -/
theorem weaken {Γ Δ : Ctx} {t : Term} {T : Ty} (h : HasType Γ t T) (hΓ : Included Γ Δ) : HasType Δ t T := by
  induction h generalizing Δ with
  | num => exact .num
  | add _ _ ih₁ ih₂ => exact .add (ih₁ hΓ) (ih₂ hΓ)
  | sub _ _ ih₁ ih₂ => exact .sub (ih₁ hΓ) (ih₂ hΓ)
  | mul _ _ ih₁ ih₂ => exact .mul (ih₁ hΓ) (ih₂ hΓ)
  | tru => exact .tru
  | fls => exact .fls
  | ite _ _ _ ihc iht ihe => exact .ite (ihc hΓ) (iht hΓ) (ihe hΓ)
  | iszero _ ih => exact .iszero (ih hΓ)
  | var hx => exact .var (hΓ _ _ hx)
  | let_ _ _ ih₁ ih₂ => exact .let_ (ih₁ hΓ) (ih₂ hΓ.cons)
  | lam _ ih => exact .lam (ih hΓ.cons)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ hΓ) (ih₂ hΓ)
  | fix _ ih => exact .fix (ih hΓ.cons.cons)

/-- 置換補題：`x : A`のもとで型`B`を持つ式の`x`を，型`A`を持つ閉じた式で置き換えても，型は`B`のままである． -/
theorem subst_typing {Γ : Ctx} {x : String} {A B : Ty} {u v : Term}
    (hu : HasType ((x, A) :: Γ) u B) (hv : HasType [] v A) : HasType Γ (subst x v u) B := by
  induction u generalizing Γ B with
  | num n => cases hu; exact .num
  | add t₁ t₂ ih₁ ih₂ => cases hu with | add h₁ h₂ => exact .add (ih₁ h₁) (ih₂ h₂)
  | sub t₁ t₂ ih₁ ih₂ => cases hu with | sub h₁ h₂ => exact .sub (ih₁ h₁) (ih₂ h₂)
  | mul t₁ t₂ ih₁ ih₂ => cases hu with | mul h₁ h₂ => exact .mul (ih₁ h₁) (ih₂ h₂)
  | tru => cases hu; exact .tru
  | fls => cases hu; exact .fls
  | ite c t e ihc iht ihe => cases hu with | ite hc ht he => exact .ite (ihc hc) (iht ht) (ihe he)
  | iszero t ih => cases hu with | iszero h => exact .iszero (ih h)
  | var y =>
    cases hu with
    | var hy =>
      by_cases hyx : y = x
      · subst hyx
        simp [Ctx.lookup] at hy
        subst hy
        simp only [subst, ite_true]
        exact weaken hv (fun _ _ h => by simp [Ctx.lookup] at h)
      · simp only [Ctx.lookup, hyx, ite_false] at hy
        simp only [subst, hyx, ite_false]
        exact .var hy
  | let_ y t u iht ihu =>
    cases hu with
    | let_ ht hu' =>
      by_cases hyx : y = x
      · subst hyx
        simp only [subst, ite_true]
        refine .let_ (iht ht) (weaken hu' ?_)
        intro z C hz
        by_cases hzy : z = y <;> simp_all [Ctx.lookup]
      · simp only [subst, hyx, ite_false]
        refine .let_ (iht ht) (ihu (weaken hu' ?_))
        intro z C hz
        by_cases hzy : z = y <;> by_cases hzx : z = x <;> simp_all [Ctx.lookup]
  | lam y A' b ih =>
    cases hu with
    | lam hb =>
      by_cases hyx : y = x
      · subst hyx
        simp only [subst, ite_true]
        refine .lam (weaken hb ?_)
        intro z C hz
        by_cases hzy : z = y <;> simp_all [Ctx.lookup]
      · simp only [subst, hyx, ite_false]
        refine .lam (ih (weaken hb ?_))
        intro z C hz
        by_cases hzy : z = y <;> by_cases hzx : z = x <;> simp_all [Ctx.lookup]
  | app t₁ t₂ ih₁ ih₂ => cases hu with | app h₁ h₂ => exact .app (ih₁ h₁) (ih₂ h₂)
  | fix g y A' B' b ih =>
    cases hu with
    | fix hb =>
      by_cases hgy : g = x ∨ y = x
      · simp only [subst, hgy, ite_true]
        refine .fix (weaken hb ?_)
        intro z D hz
        rcases hgy with rfl | rfl <;>
          by_cases hzy : z = y <;> by_cases hzg : z = g <;> simp_all [Ctx.lookup]
      · simp only [subst, hgy, ite_false]
        refine .fix (ih (weaken hb ?_))
        intro z D hz
        by_cases hzy : z = y <;> by_cases hzg : z = g <;> by_cases hzx : z = x <;> simp_all [Ctx.lookup]

/-! ## 標準形補題

値を表す式の型から，その値の形がわかる．
-/

theorem canonical_nat {Γ : Ctx} {v : Value} (h : HasType Γ v.toTerm .nat) : ∃ n, v = .num n := by
  cases v with
  | num n => exact ⟨n, rfl⟩
  | bool b => cases b <;> cases h
  | lam x A t => cases h
  | fix f x A B t => cases h

theorem canonical_bool {Γ : Ctx} {v : Value} (h : HasType Γ v.toTerm .bool) : v = .bool true ∨ v = .bool false := by
  cases v with
  | num n => cases h
  | bool b => cases b <;> simp
  | lam x A t => cases h
  | fix f x A B t => cases h

theorem canonical_arrow {Γ : Ctx} {v : Value} {A B : Ty} (h : HasType Γ v.toTerm (.arrow A B)) :
    (∃ x b, v = .lam x A b) ∨ (∃ f x b, v = .fix f x A B b) := by
  cases v with
  | num n => cases h
  | bool b => cases b <;> cases h
  | lam x A' t => cases h; exact .inl ⟨x, t, rfl⟩
  | fix f x A' B' t => cases h; exact .inr ⟨f, x, t, rfl⟩

/-! ## 進行と保存 -/

/-- 進行：空の文脈で型の付く式は，値を表す式であるか，1ステップ簡約できる． -/
theorem progress {t : Term} {T : Ty} (h : HasType [] t T) : (∃ v : Value, t = v.toTerm) ∨ ∃ t', t ⟶ t' := by
  generalize hΓ : ([] : Ctx) = Γ at h
  induction h with
  | num => exact .inl ⟨.num _, rfl⟩
  | @add _ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    subst hΓ
    rcases ih₁ rfl with ⟨v₁, rfl⟩ | ⟨t₁', s₁⟩
    · obtain ⟨n₁, rfl⟩ := canonical_nat h₁
      rcases ih₂ rfl with ⟨v₂, rfl⟩ | ⟨t₂', s₂⟩
      · obtain ⟨n₂, rfl⟩ := canonical_nat h₂
        exact .inr ⟨_, .add⟩
      · exact .inr ⟨_, .addR s₂⟩
    · exact .inr ⟨_, .addL s₁⟩
  | @sub _ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    subst hΓ
    rcases ih₁ rfl with ⟨v₁, rfl⟩ | ⟨t₁', s₁⟩
    · obtain ⟨n₁, rfl⟩ := canonical_nat h₁
      rcases ih₂ rfl with ⟨v₂, rfl⟩ | ⟨t₂', s₂⟩
      · obtain ⟨n₂, rfl⟩ := canonical_nat h₂
        exact .inr ⟨_, .sub⟩
      · exact .inr ⟨_, .subR s₂⟩
    · exact .inr ⟨_, .subL s₁⟩
  | @mul _ t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    subst hΓ
    rcases ih₁ rfl with ⟨v₁, rfl⟩ | ⟨t₁', s₁⟩
    · obtain ⟨n₁, rfl⟩ := canonical_nat h₁
      rcases ih₂ rfl with ⟨v₂, rfl⟩ | ⟨t₂', s₂⟩
      · obtain ⟨n₂, rfl⟩ := canonical_nat h₂
        exact .inr ⟨_, .mul⟩
      · exact .inr ⟨_, .mulR s₂⟩
    · exact .inr ⟨_, .mulL s₁⟩
  | tru => exact .inl ⟨.bool true, rfl⟩
  | fls => exact .inl ⟨.bool false, rfl⟩
  | @ite _ c t e T hc _ _ ihc _ _ =>
    subst hΓ
    rcases ihc rfl with ⟨v, rfl⟩ | ⟨c', s⟩
    · rcases canonical_bool hc with rfl | rfl
      · exact .inr ⟨_, .iteTrue⟩
      · exact .inr ⟨_, .iteFalse⟩
    · exact .inr ⟨_, .ite s⟩
  | @iszero _ t h ih =>
    subst hΓ
    rcases ih rfl with ⟨v, rfl⟩ | ⟨t', s⟩
    · obtain ⟨n, rfl⟩ := canonical_nat h
      cases n with
      | zero => exact .inr ⟨_, .iszeroZero⟩
      | succ n => exact .inr ⟨_, .iszeroSucc⟩
    · exact .inr ⟨_, .iszero s⟩
  | var hx =>
    subst hΓ
    simp [Ctx.lookup] at hx
  | let_ _ _ ih₁ _ =>
    subst hΓ
    rcases ih₁ rfl with ⟨v, rfl⟩ | ⟨t', s⟩
    · exact .inr ⟨_, .letV (isValue_toTerm v)⟩
    · exact .inr ⟨_, .letL s⟩
  | lam _ _ => exact .inl ⟨.lam _ _ _, rfl⟩
  | fix _ _ => exact .inl ⟨.fix _ _ _ _ _, rfl⟩
  | @app _ t₁ t₂ A B h₁ _ ih₁ ih₂ =>
    subst hΓ
    rcases ih₁ rfl with ⟨v₁, rfl⟩ | ⟨t₁', s₁⟩
    · rcases canonical_arrow h₁ with ⟨x, b, rfl⟩ | ⟨f, x, b, rfl⟩
      · rcases ih₂ rfl with ⟨v₂, rfl⟩ | ⟨t₂', s₂⟩
        · exact .inr ⟨_, .beta (isValue_toTerm v₂)⟩
        · exact .inr ⟨_, .app2 .lam s₂⟩
      · rcases ih₂ rfl with ⟨v₂, rfl⟩ | ⟨t₂', s₂⟩
        · exact .inr ⟨_, .betaFix (isValue_toTerm v₂)⟩
        · exact .inr ⟨_, .app2 .fix s₂⟩
    · exact .inr ⟨_, .app1 s₁⟩

/-- 保存：空の文脈で型の付く式を1ステップ簡約しても，型は変わらない． -/
theorem preservation {t t' : Term} {T : Ty} (h : HasType [] t T) (s : t ⟶ t') : HasType [] t' T := by
  generalize hΓ : ([] : Ctx) = Γ at h
  induction h generalizing t' with
  | num => cases s
  | add h₁ h₂ ih₁ ih₂ =>
    cases s with
    | addL s => exact .add (ih₁ s hΓ) h₂
    | addR s => exact .add h₁ (ih₂ s hΓ)
    | add => exact .num
  | sub h₁ h₂ ih₁ ih₂ =>
    cases s with
    | subL s => exact .sub (ih₁ s hΓ) h₂
    | subR s => exact .sub h₁ (ih₂ s hΓ)
    | sub => exact .num
  | mul h₁ h₂ ih₁ ih₂ =>
    cases s with
    | mulL s => exact .mul (ih₁ s hΓ) h₂
    | mulR s => exact .mul h₁ (ih₂ s hΓ)
    | mul => exact .num
  | tru => cases s
  | fls => cases s
  | ite hc ht he ihc _ _ =>
    cases s with
    | iteTrue => exact ht
    | iteFalse => exact he
    | ite s => exact .ite (ihc s hΓ) ht he
  | iszero h ih =>
    cases s with
    | iszeroZero => exact .tru
    | iszeroSucc => exact .fls
    | iszero s => exact .iszero (ih s hΓ)
  | var => cases s
  | let_ h₁ h₂ ih₁ _ =>
    subst hΓ
    cases s with
    | letL s => exact .let_ (ih₁ s rfl) h₂
    | letV _ => exact subst_typing h₂ h₁
  | lam _ _ => cases s
  | app h₁ h₂ ih₁ ih₂ =>
    subst hΓ
    cases s with
    | app1 s => exact .app (ih₁ s rfl) h₂
    | app2 _ s => exact .app h₁ (ih₂ s rfl)
    | beta _ =>
      cases h₁ with
      | lam hb => exact subst_typing hb h₂
    | betaFix _ =>
      have hf := h₁
      cases h₁ with
      | fix hb => exact subst_typing (subst_typing hb h₂) hf
  | fix _ _ => cases s

/-- 型安全性：空の文脈で型の付く式は，何ステップ簡約しても行き詰まらない． -/
theorem type_safety {t t' : Term} {T : Ty} (h : HasType [] t T) (s : t ⟶* t') : ¬ Stuck t' := by
  induction s with
  | refl =>
    intro ⟨hn, hv⟩
    rcases progress h with ⟨v, rfl⟩ | ⟨u, su⟩
    · exact hv v rfl
    · exact hn u su
  | step s₁ _ ih => exact ih (preservation h s₁)

/-! ## 型の付く式の評価 -/

/-- 空の文脈で型の付く式を評価しても，行き詰まらない．燃料を使い切ることはある． -/
theorem eval_not_stuck {k : Nat} {t t' : Term} {T : Ty} (h : HasType [] t T) : eval k t ≠ .error (.stuck t') := by
  intro he
  obtain ⟨s, st⟩ := EvalTest.eval_stuck he
  exact type_safety h s st

end MiniTest.TypingTest
