import Mini.Syntax
import Mini.Subst

/-!
# 小ステップ意味論

式を1ステップずつ簡約する規則で，式の意味を定める．
-/

namespace Mini

/-- 値を表す式．数と真偽値のリテラルと，関数である． -/
inductive IsValue : Term → Prop where
  | num {n : Nat} : IsValue (.num n)
  | tru : IsValue .tru
  | fls : IsValue .fls
  | lam {x : String} {A : Ty} {t : Term} : IsValue (.lam x A t)

/-- 小ステップ意味論．`t ⟶ t'`は「式`t`は1ステップで`t'`に簡約される」と読む．
演算子の左の部分式を先に，数になるまで簡約する．
`if`は条件だけを先に簡約し，条件が真偽値になってから枝を選ぶ．
`let`は束縛する式を値まで簡約してから，本体の変数をその値で置き換える．
関数適用は，関数と引数を左から順に値まで簡約してから，関数の本体の変数を引数の値で置き換える(値呼び)． -/
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
  | iteTrue {t e : Term} : Step (.ite .tru t e) t
  | iteFalse {t e : Term} : Step (.ite .fls t e) e
  | ite {c c' t e : Term} : Step c c' → Step (.ite c t e) (.ite c' t e)
  | iszeroZero : Step (.iszero (.num 0)) .tru
  | iszeroSucc {n : Nat} : Step (.iszero (.num (n + 1))) .fls
  | iszero {t t' : Term} : Step t t' → Step (.iszero t) (.iszero t')
  | letL {x : String} {t t' u : Term} : Step t t' → Step (.let_ x t u) (.let_ x t' u)
  | letV {x : String} {v u : Term} : IsValue v → Step (.let_ x v u) (subst x v u)
  | app1 {t₁ t₁' t₂ : Term} : Step t₁ t₁' → Step (.app t₁ t₂) (.app t₁' t₂)
  | app2 {v₁ t₂ t₂' : Term} : IsValue v₁ → Step t₂ t₂' → Step (.app v₁ t₂) (.app v₁ t₂')
  | beta {x : String} {A : Ty} {b v : Term} : IsValue v → Step (.app (.lam x A b) v) (subst x v b)

@[inherit_doc] infix:50 " ⟶ " => Step

/-- 0ステップ以上の簡約．`t ⟶* t'`は「式`t`は何ステップかで`t'`に簡約される」と読む． -/
inductive Steps : Term → Term → Prop where
  | refl {t : Term} : Steps t t
  | step {t t' t'' : Term} : Step t t' → Steps t' t'' → Steps t t''

@[inherit_doc] infix:50 " ⟶* " => Steps

/-- 正規形．どの規則でも簡約できない式． -/
def Normal (t : Term) : Prop := ∀ t', ¬ t ⟶ t'

/-- 行き詰まった式．正規形だが，値を表す式ではない． -/
def Stuck (t : Term) : Prop := Normal t ∧ ∀ v : Value, t ≠ v.toTerm

end Mini
