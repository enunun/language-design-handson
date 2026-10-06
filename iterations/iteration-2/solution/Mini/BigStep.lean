import Mini.Syntax

/-!
# 大ステップ意味論

式の意味を，評価器とは別に，推論規則で定める．
-/

namespace Mini

/-- 大ステップ意味論．`t ⇓ n`は「式`t`を評価すると自然数`n`になる」と読む． -/
inductive Eval : Term → Nat → Prop where
  | num {n : Nat} : Eval (.num n) n
  | add {t₁ t₂ : Term} {n₁ n₂ : Nat} : Eval t₁ n₁ → Eval t₂ n₂ → Eval (.add t₁ t₂) (n₁ + n₂)
  | sub {t₁ t₂ : Term} {n₁ n₂ : Nat} : Eval t₁ n₁ → Eval t₂ n₂ → Eval (.sub t₁ t₂) (n₁ - n₂)
  | mul {t₁ t₂ : Term} {n₁ n₂ : Nat} : Eval t₁ n₁ → Eval t₂ n₂ → Eval (.mul t₁ t₂) (n₁ * n₂)

@[inherit_doc] infix:50 " ⇓ " => Eval

end Mini
