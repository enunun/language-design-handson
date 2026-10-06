import Mini.Syntax

/-!
# 評価器

式を評価して，その値の自然数を返す．
式を1ステップだけ簡約する関数もここに置く．
-/

namespace Mini

/-- 式`t`の値．`-`は自然数の引き算で，結果が負になるときは`0`になる． -/
def eval : Term → Nat
  | .num n => n
  | .add t₁ t₂ => eval t₁ + eval t₂
  | .sub t₁ t₂ => eval t₁ - eval t₂
  | .mul t₁ t₂ => eval t₁ * eval t₂

/-- 式`t`を1ステップ簡約した式．`t`が数でそれ以上簡約できないときは`none`を返す． -/
def step : Term → Option Term
  | .num _ => none
  | .add t₁ t₂ =>
    match t₁, t₂ with
    | .num n₁, .num n₂ => some (.num (n₁ + n₂))
    | .num n₁, t₂ => (step t₂).map (.add (.num n₁))
    | t₁, t₂ => (step t₁).map (.add · t₂)
  | .sub t₁ t₂ =>
    match t₁, t₂ with
    | .num n₁, .num n₂ => some (.num (n₁ - n₂))
    | .num n₁, t₂ => (step t₂).map (.sub (.num n₁))
    | t₁, t₂ => (step t₁).map (.sub · t₂)
  | .mul t₁ t₂ =>
    match t₁, t₂ with
    | .num n₁, .num n₂ => some (.num (n₁ * n₂))
    | .num n₁, t₂ => (step t₂).map (.mul (.num n₁))
    | t₁, t₂ => (step t₁).map (.mul · t₂)

end Mini
