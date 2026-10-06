import Mini.Syntax

/-!
# 型付け

式の型を，型付け規則と型検査器で定める．
-/

namespace Mini

/-- 型付け規則．`HasType t T`は「式`t`は型`T`を持つ」と読む． -/
inductive HasType : Term → Ty → Prop where
  | num {n : Nat} : HasType (.num n) .nat
  | add {t₁ t₂ : Term} : HasType t₁ .nat → HasType t₂ .nat → HasType (.add t₁ t₂) .nat
  | sub {t₁ t₂ : Term} : HasType t₁ .nat → HasType t₂ .nat → HasType (.sub t₁ t₂) .nat
  | mul {t₁ t₂ : Term} : HasType t₁ .nat → HasType t₂ .nat → HasType (.mul t₁ t₂) .nat
  | tru : HasType .tru .bool
  | fls : HasType .fls .bool
  | ite {c t e : Term} {T : Ty} :
      HasType c .bool → HasType t T → HasType e T → HasType (.ite c t e) T
  | iszero {t : Term} : HasType t .nat → HasType (.iszero t) .bool

/-- 型エラー． -/
inductive TypeError where
  /-- `what`の型が，期待した型`expected`ではなく`actual`だった． -/
  | mismatch (what : String) (expected actual : Ty)
  /-- `if`の2つの枝の型が，`thenTy`と`elseTy`で異なる． -/
  | branches (thenTy elseTy : Ty)
  deriving Repr, DecidableEq

/-- 型検査器．式`t`の型を求める．型が付かないときは，その理由を返す． -/
def typeOf : Term → Except TypeError Ty
  | .num _ => .ok .nat
  | .add t₁ t₂ =>
    match typeOf t₁, typeOf t₂ with
    | .ok .nat, .ok .nat => .ok .nat
    | .ok .nat, .ok T₂ => .error (.mismatch "+の右辺" .nat T₂)
    | .ok T₁, .ok _ => .error (.mismatch "+の左辺" .nat T₁)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .sub t₁ t₂ =>
    match typeOf t₁, typeOf t₂ with
    | .ok .nat, .ok .nat => .ok .nat
    | .ok .nat, .ok T₂ => .error (.mismatch "-の右辺" .nat T₂)
    | .ok T₁, .ok _ => .error (.mismatch "-の左辺" .nat T₁)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .mul t₁ t₂ =>
    match typeOf t₁, typeOf t₂ with
    | .ok .nat, .ok .nat => .ok .nat
    | .ok .nat, .ok T₂ => .error (.mismatch "*の右辺" .nat T₂)
    | .ok T₁, .ok _ => .error (.mismatch "*の左辺" .nat T₁)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .tru => .ok .bool
  | .fls => .ok .bool
  | .ite c t e =>
    match typeOf c, typeOf t, typeOf e with
    | .ok .bool, .ok T, .ok E => if T = E then .ok T else .error (.branches T E)
    | .ok C, .ok _, .ok _ => .error (.mismatch "ifの条件" .bool C)
    | .error err, _, _ => .error err
    | _, .error err, _ => .error err
    | _, _, .error err => .error err
  | .iszero t =>
    match typeOf t with
    | .ok .nat => .ok .bool
    | .ok T => .error (.mismatch "iszeroの引数" .nat T)
    | .error err => .error err

/-- 値の型． -/
def Value.ty : Value → Ty
  | .num _ => .nat
  | .bool _ => .bool

end Mini
