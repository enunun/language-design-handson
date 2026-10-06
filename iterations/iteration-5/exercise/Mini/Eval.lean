import Mini.Syntax

/-!
# 評価器

式を評価して，その値を返す．
式を1ステップだけ簡約する関数もここに置く．
-/

namespace Mini

/-- 式`t`の値．評価が行き詰まったとき(`1 + true`など)は`none`を返す． -/
def eval : Term → Option Value
  | .num n => some (.num n)
  | .add t₁ t₂ =>
    match eval t₁, eval t₂ with
    | some (.num n₁), some (.num n₂) => some (.num (n₁ + n₂))
    | _, _ => none
  | .sub t₁ t₂ =>
    match eval t₁, eval t₂ with
    | some (.num n₁), some (.num n₂) => some (.num (n₁ - n₂))
    | _, _ => none
  | .mul t₁ t₂ =>
    match eval t₁, eval t₂ with
    | some (.num n₁), some (.num n₂) => some (.num (n₁ * n₂))
    | _, _ => none
  | .tru => some (.bool true)
  | .fls => some (.bool false)
  | .ite c t e =>
    match eval c with
    | some (.bool true) => eval t
    | some (.bool false) => eval e
    | _ => none
  | .iszero t =>
    match eval t with
    | some (.num n) => some (.bool (n == 0))
    | _ => none

/-- 式`t`を1ステップ簡約した式．`t`がそれ以上簡約できないときは`none`を返す． -/
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
  | .tru => none
  | .fls => none
  | .ite c t e =>
    match c with
    | .tru => some t
    | .fls => some e
    | c => (step c).map (.ite · t e)
  | .iszero t =>
    match t with
    | .num 0 => some .tru
    | .num (_ + 1) => some .fls
    | t => (step t).map .iszero

end Mini
