import Mini.Typing
import Mini.SmallStep
import Mini.Eval

/-!
# `Mini.Typing`の単体テスト
-/

namespace MiniTest.TypingTest

open Mini

/-! ## 型付けの例 -/

example : HasType (.add (.num 1) (.num 2)) .nat := .add .num .num

example : HasType (.ite (.iszero (.num 0)) (.num 1) (.num 2)) .nat := .ite (.iszero .num) .num .num

/-- `1 + true`には型が付かない． -/
example : ¬ ∃ T, HasType (.add (.num 1) .tru) T := by
  intro ⟨T, h⟩
  cases h with
  | add _ h₂ => cases h₂

/-- 型システムは安全側に倒した近似である．`if true then 0 else false`は値`0`に評価されるが，型が付かない． -/
example : eval (.ite .tru (.num 0) .fls) = some (.num 0) ∧ ¬ ∃ T, HasType (.ite .tru (.num 0) .fls) T := by
  constructor
  · decide
  · intro ⟨T, h⟩
    cases h with
    | ite _ ht he =>
      cases ht
      cases he

/-! ## 型検査器 -/

example : typeOf (.ite (.iszero (.num 0)) (.num 1) (.num 2)) = .ok .nat := rfl

example : typeOf (.add (.num 1) .tru) = .error (.mismatch "+の右辺" .nat .bool) := rfl

example : typeOf (.ite (.num 1) (.num 2) (.num 3)) = .error (.mismatch "ifの条件" .bool .nat) := rfl

example : typeOf (.ite .tru (.num 1) .fls) = .error (.branches .nat .bool) := rfl

/-- 型検査器の健全性：型検査器が返す型は，型付け規則でも式の型である． -/
theorem typeOf_sound {t : Term} {T : Ty} (h : typeOf t = .ok T) : HasType t T := by
  induction t generalizing T with
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

/-- 型検査器の完全性：型付け規則で式の型が`T`なら，型検査器も`T`を返す． -/
theorem typeOf_complete {t : Term} {T : Ty} (h : HasType t T) : typeOf t = .ok T := by
  induction h with
  | num => rfl
  | add _ _ ih₁ ih₂ => simp [typeOf, ih₁, ih₂]
  | sub _ _ ih₁ ih₂ => simp [typeOf, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [typeOf, ih₁, ih₂]
  | tru => rfl
  | fls => rfl
  | ite _ _ _ ihc iht ihe => simp [typeOf, ihc, iht, ihe]
  | iszero _ ih => simp [typeOf, ih]

/-- 式の型は1つに決まる．完全性から，どちらの型も`typeOf t`の結果に等しい． -/
theorem type_unique {t : Term} {T U : Ty} (h₁ : HasType t T) (h₂ : HasType t U) : T = U := by
  have := (typeOf_complete h₁).symm.trans (typeOf_complete h₂)
  cases this
  rfl

/-! ## 標準形補題

値を表す式の型から，その値の形がわかる．
-/

theorem canonical_nat {v : Value} (h : HasType v.toTerm .nat) : ∃ n, v = .num n := by
  cases v with
  | num n => exact ⟨n, rfl⟩
  | bool b => cases b <;> cases h

theorem canonical_bool {v : Value} (h : HasType v.toTerm .bool) : v = .bool true ∨ v = .bool false := by
  cases v with
  | num n => cases h
  | bool b => cases b <;> simp

/-! ## 進行と保存 -/

/-- 進行：型の付く式は，値を表す式であるか，1ステップ簡約できる． -/
theorem progress {t : Term} {T : Ty} (h : HasType t T) : (∃ v : Value, t = v.toTerm) ∨ ∃ t', t ⟶ t' := by
  induction h with
  | num => exact .inl ⟨.num _, rfl⟩
  | @add t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨v₁, rfl⟩ | ⟨t₁', s₁⟩
    · obtain ⟨n₁, rfl⟩ := canonical_nat h₁
      rcases ih₂ with ⟨v₂, rfl⟩ | ⟨t₂', s₂⟩
      · obtain ⟨n₂, rfl⟩ := canonical_nat h₂
        exact .inr ⟨_, .add⟩
      · exact .inr ⟨_, .addR s₂⟩
    · exact .inr ⟨_, .addL s₁⟩
  | @sub t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨v₁, rfl⟩ | ⟨t₁', s₁⟩
    · obtain ⟨n₁, rfl⟩ := canonical_nat h₁
      rcases ih₂ with ⟨v₂, rfl⟩ | ⟨t₂', s₂⟩
      · obtain ⟨n₂, rfl⟩ := canonical_nat h₂
        exact .inr ⟨_, .sub⟩
      · exact .inr ⟨_, .subR s₂⟩
    · exact .inr ⟨_, .subL s₁⟩
  | @mul t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨v₁, rfl⟩ | ⟨t₁', s₁⟩
    · obtain ⟨n₁, rfl⟩ := canonical_nat h₁
      rcases ih₂ with ⟨v₂, rfl⟩ | ⟨t₂', s₂⟩
      · obtain ⟨n₂, rfl⟩ := canonical_nat h₂
        exact .inr ⟨_, .mul⟩
      · exact .inr ⟨_, .mulR s₂⟩
    · exact .inr ⟨_, .mulL s₁⟩
  | tru => exact .inl ⟨.bool true, rfl⟩
  | fls => exact .inl ⟨.bool false, rfl⟩
  | @ite c t e T hc _ _ ihc _ _ =>
    rcases ihc with ⟨v, rfl⟩ | ⟨c', s⟩
    · rcases canonical_bool hc with rfl | rfl
      · exact .inr ⟨_, .iteTrue⟩
      · exact .inr ⟨_, .iteFalse⟩
    · exact .inr ⟨_, .ite s⟩
  | @iszero t h ih =>
    rcases ih with ⟨v, rfl⟩ | ⟨t', s⟩
    · obtain ⟨n, rfl⟩ := canonical_nat h
      cases n with
      | zero => exact .inr ⟨_, .iszeroZero⟩
      | succ n => exact .inr ⟨_, .iszeroSucc⟩
    · exact .inr ⟨_, .iszero s⟩

/-- 保存：型の付く式を1ステップ簡約しても，型は変わらない． -/
theorem preservation {t t' : Term} {T : Ty} (h : HasType t T) (s : t ⟶ t') : HasType t' T := by
  induction h generalizing t' with
  | num => cases s
  | add h₁ h₂ ih₁ ih₂ =>
    cases s with
    | addL s => exact .add (ih₁ s) h₂
    | addR s => exact .add h₁ (ih₂ s)
    | add => exact .num
  | sub h₁ h₂ ih₁ ih₂ =>
    cases s with
    | subL s => exact .sub (ih₁ s) h₂
    | subR s => exact .sub h₁ (ih₂ s)
    | sub => exact .num
  | mul h₁ h₂ ih₁ ih₂ =>
    cases s with
    | mulL s => exact .mul (ih₁ s) h₂
    | mulR s => exact .mul h₁ (ih₂ s)
    | mul => exact .num
  | tru => cases s
  | fls => cases s
  | ite hc ht he ihc _ _ =>
    cases s with
    | iteTrue => exact ht
    | iteFalse => exact he
    | ite s => exact .ite (ihc s) ht he
  | iszero h ih =>
    cases s with
    | iszeroZero => exact .tru
    | iszeroSucc => exact .fls
    | iszero s => exact .iszero (ih s)

/-- 型安全性：型の付く式は，何ステップ簡約しても行き詰まらない． -/
theorem type_safety {t t' : Term} {T : Ty} (h : HasType t T) (s : t ⟶* t') : ¬ Stuck t' := by
  induction s with
  | refl =>
    intro ⟨hn, hv⟩
    rcases progress h with ⟨v, rfl⟩ | ⟨u, su⟩
    · exact hv v rfl
    · exact hn u su
  | step s₁ _ ih => exact ih (preservation h s₁)

/-! ## 型の付く式の評価 -/

/-- 型の付く式は必ず値に評価され，その値の型は式の型と同じである． -/
theorem eval_of_hasType {t : Term} {T : Ty} (h : HasType t T) : ∃ v, eval t = some v ∧ v.ty = T := by
  induction h with
  | @num n => exact ⟨.num n, rfl, rfl⟩
  | add _ _ ih₁ ih₂ =>
    obtain ⟨v₁, e₁, t₁⟩ := ih₁
    obtain ⟨v₂, e₂, t₂⟩ := ih₂
    cases v₁ <;> cases v₂ <;> simp_all [Value.ty, eval]
  | sub _ _ ih₁ ih₂ =>
    obtain ⟨v₁, e₁, t₁⟩ := ih₁
    obtain ⟨v₂, e₂, t₂⟩ := ih₂
    cases v₁ <;> cases v₂ <;> simp_all [Value.ty, eval]
  | mul _ _ ih₁ ih₂ =>
    obtain ⟨v₁, e₁, t₁⟩ := ih₁
    obtain ⟨v₂, e₂, t₂⟩ := ih₂
    cases v₁ <;> cases v₂ <;> simp_all [Value.ty, eval]
  | tru => exact ⟨.bool true, rfl, rfl⟩
  | fls => exact ⟨.bool false, rfl, rfl⟩
  | ite _ _ _ ihc iht ihe =>
    obtain ⟨vc, ec, tc⟩ := ihc
    obtain ⟨vt, et, tt⟩ := iht
    obtain ⟨ve, ee, te⟩ := ihe
    cases vc with
    | num n => simp [Value.ty] at tc
    | bool b => cases b <;> simp_all [eval]
  | iszero _ ih =>
    obtain ⟨v, e, tv⟩ := ih
    cases v with
    | num n => exact ⟨.bool (n == 0), by simp [eval, e], rfl⟩
    | bool b => simp [Value.ty] at tv

end MiniTest.TypingTest
