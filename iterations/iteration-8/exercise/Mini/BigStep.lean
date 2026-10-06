import Mini.Syntax
import Mini.Subst

/-!
# 大ステップ意味論

式の意味を，評価器とは別に，推論規則で定める．
-/

namespace Mini

/-- 大ステップ意味論．`t ⇓ v`は「式`t`を評価すると値`v`になる」と読む．
変数を評価する規則はないので，自由な変数を含む式には値がない． -/
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
  | let_ {x : String} {t u : Term} {v w : Value} :
      Eval t v → Eval (subst x v.toTerm u) w → Eval (.let_ x t u) w
  | lam {x : String} {A : Ty} {t : Term} : Eval (.lam x A t) (.lam x A t)
  | app {t₁ t₂ b : Term} {x : String} {A : Ty} {v₂ v : Value} :
      Eval t₁ (.lam x A b) → Eval t₂ v₂ → Eval (subst x v₂.toTerm b) v → Eval (.app t₁ t₂) v
  | fix {f x : String} {A B : Ty} {t : Term} : Eval (.fix f x A B t) (.fix f x A B t)
  | appFix {t₁ t₂ b : Term} {f x : String} {A B : Ty} {v₂ v : Value} :
      Eval t₁ (.fix f x A B b) → Eval t₂ v₂ →
      Eval (subst f (.fix f x A B b) (subst x v₂.toTerm b)) v → Eval (.app t₁ t₂) v

@[inherit_doc] infix:50 " ⇓ " => Eval

end Mini
