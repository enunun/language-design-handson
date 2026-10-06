import Mini.Syntax
import Mini.Subst

/-!
# 評価器

式を1ステップだけ簡約する関数と，それを繰り返して式を評価する関数を定義する．
-/

namespace Mini

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
  | .var _ => none
  | .let_ x t u =>
    match t.toValue? with
    | some _ => some (subst x t u)
    | none => (step t).map (.let_ x · u)
  | .lam _ _ _ => none
  | .app t₁ t₂ =>
    match t₁.toValue?, t₂.toValue? with
    | some (.lam x _ b), some _ => some (subst x t₂ b)
    | some _, some _ => none
    | some _, none => (step t₂).map (.app t₁)
    | none, _ => (step t₁).map (.app · t₂)

/-- 評価が値に着かなかった理由． -/
inductive EvalError where
  /-- 式`t`で行き詰まった． -/
  | stuck (t : Term)
  /-- 燃料を使い切った． -/
  | outOfFuel
  deriving Repr, DecidableEq

/-- 式`t`を，値になるまで`step`で簡約する．`fuel`は簡約するステップ数の上限である． -/
def eval : Nat → Term → Except EvalError Value
  | 0, _ => .error .outOfFuel
  | fuel + 1, t =>
    match t.toValue? with
    | some v => .ok v
    | none =>
      match step t with
      | some t' => eval fuel t'
      | none => .error (.stuck t)

end Mini
