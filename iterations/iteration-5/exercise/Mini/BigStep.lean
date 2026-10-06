import Mini.Syntax

/-!
# 大ステップ意味論

式の意味を，評価器とは別に，推論規則で定める．
-/

namespace Mini

/-- 大ステップ意味論．`t ⇓ v`は「式`t`を評価すると値`v`になる」と読む． -/
inductive Eval : Term → Value → Prop where
  | num {n : Nat} : Eval (.num n) (.num n)
  | add {t₁ t₂ : Term} {n₁ n₂ : Nat} :
      Eval t₁ (.num n₁) → Eval t₂ (.num n₂) → Eval (.add t₁ t₂) (.num (n₁ + n₂))
  | sub {t₁ t₂ : Term} {n₁ n₂ : Nat} :
      Eval t₁ (.num n₁) → Eval t₂ (.num n₂) → Eval (.sub t₁ t₂) (.num (n₁ - n₂))
  | mul {t₁ t₂ : Term} {n₁ n₂ : Nat} :
      Eval t₁ (.num n₁) → Eval t₂ (.num n₂) → Eval (.mul t₁ t₂) (.num (n₁ * n₂))
  | tru : Eval .tru (.bool true)
  | fls : Eval .fls (.bool false)
  | iteTrue {c t e : Term} {v : Value} : Eval c (.bool true) → Eval t v → Eval (.ite c t e) v
  | iteFalse {c t e : Term} {v : Value} : Eval c (.bool false) → Eval e v → Eval (.ite c t e) v
  | iszero {t : Term} {n : Nat} : Eval t (.num n) → Eval (.iszero t) (.bool (n == 0))

@[inherit_doc] infix:50 " ⇓ " => Eval

end Mini
