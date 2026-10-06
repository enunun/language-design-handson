import Mini.Syntax

/-!
# 小ステップ意味論

式を1ステップずつ簡約する規則で，式の意味を定める．
-/

namespace Mini

/-- 小ステップ意味論．`t ⟶ t'`は「式`t`は1ステップで`t'`に簡約される」と読む．
演算子の左の部分式を先に，数になるまで簡約する． -/
inductive Step : Term → Term → Prop where
  | addL {t₁ t₁' t₂ : Term} : Step t₁ t₁' → Step (.add t₁ t₂) (.add t₁' t₂)
  | addR {n₁ : Nat} {t₂ t₂' : Term} : Step t₂ t₂' → Step (.add (.num n₁) t₂) (.add (.num n₁) t₂')
  | add {n₁ n₂ : Nat} : Step (.add (.num n₁) (.num n₂)) (.num (n₁ + n₂))
  | subL {t₁ t₁' t₂ : Term} : Step t₁ t₁' → Step (.sub t₁ t₂) (.sub t₁' t₂)
  | subR {n₁ : Nat} {t₂ t₂' : Term} : Step t₂ t₂' → Step (.sub (.num n₁) t₂) (.sub (.num n₁) t₂')
  | sub {n₁ n₂ : Nat} : Step (.sub (.num n₁) (.num n₂)) (.num (n₁ - n₂))
  | mulL {t₁ t₁' t₂ : Term} : Step t₁ t₁' → Step (.mul t₁ t₂) (.mul t₁' t₂)
  | mulR {n₁ : Nat} {t₂ t₂' : Term} : Step t₂ t₂' → Step (.mul (.num n₁) t₂) (.mul (.num n₁) t₂')
  | mul {n₁ n₂ : Nat} : Step (.mul (.num n₁) (.num n₂)) (.num (n₁ * n₂))

@[inherit_doc] infix:50 " ⟶ " => Step

/-- 0ステップ以上の簡約．`t ⟶* t'`は「式`t`は何ステップかで`t'`に簡約される」と読む． -/
inductive Steps : Term → Term → Prop where
  | refl {t : Term} : Steps t t
  | step {t t' t'' : Term} : Step t t' → Steps t' t'' → Steps t t''

@[inherit_doc] infix:50 " ⟶* " => Steps

end Mini
