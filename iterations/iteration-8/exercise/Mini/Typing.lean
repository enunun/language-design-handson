import Mini.Syntax

/-!
# 型付け

式の型を，型付け規則と型検査器で定める．
-/

namespace Mini

/-- 型付け文脈．変数とその型の組の列で，先頭ほど内側で束縛された変数である． -/
abbrev Ctx := List (String × Ty)

/-- 文脈`Γ`での変数`x`の型．同じ名前の変数が複数あるときは，先頭に近いもの(内側の束縛)を使う． -/
def Ctx.lookup : Ctx → String → Option Ty
  | [], _ => none
  | (y, T) :: Γ, x => if x = y then some T else Ctx.lookup Γ x

/-- 型付け規則．`HasType Γ t T`は「文脈`Γ`のもとで，式`t`は型`T`を持つ」と読む． -/
inductive HasType : Ctx → Term → Ty → Prop where
  | num {Γ : Ctx} {n : Nat} : HasType Γ (.num n) .nat
  | add {Γ : Ctx} {t₁ t₂ : Term} : HasType Γ t₁ .nat → HasType Γ t₂ .nat → HasType Γ (.add t₁ t₂) .nat
  | sub {Γ : Ctx} {t₁ t₂ : Term} : HasType Γ t₁ .nat → HasType Γ t₂ .nat → HasType Γ (.sub t₁ t₂) .nat
  | mul {Γ : Ctx} {t₁ t₂ : Term} : HasType Γ t₁ .nat → HasType Γ t₂ .nat → HasType Γ (.mul t₁ t₂) .nat
  | tru {Γ : Ctx} : HasType Γ .tru .bool
  | fls {Γ : Ctx} : HasType Γ .fls .bool
  | ite {Γ : Ctx} {c t e : Term} {T : Ty} :
      HasType Γ c .bool → HasType Γ t T → HasType Γ e T → HasType Γ (.ite c t e) T
  | iszero {Γ : Ctx} {t : Term} : HasType Γ t .nat → HasType Γ (.iszero t) .bool
  | var {Γ : Ctx} {x : String} {T : Ty} : Γ.lookup x = some T → HasType Γ (.var x) T
  | let_ {Γ : Ctx} {x : String} {t u : Term} {T U : Ty} :
      HasType Γ t T → HasType ((x, T) :: Γ) u U → HasType Γ (.let_ x t u) U
  | lam {Γ : Ctx} {x : String} {A B : Ty} {t : Term} :
      HasType ((x, A) :: Γ) t B → HasType Γ (.lam x A t) (.arrow A B)
  | app {Γ : Ctx} {t₁ t₂ : Term} {A B : Ty} :
      HasType Γ t₁ (.arrow A B) → HasType Γ t₂ A → HasType Γ (.app t₁ t₂) B
  | fix {Γ : Ctx} {f x : String} {A B : Ty} {t : Term} :
      HasType ((x, A) :: (f, .arrow A B) :: Γ) t B → HasType Γ (.fix f x A B t) (.arrow A B)

/-- 型エラー． -/
inductive TypeError where
  /-- `what`の型が，期待した型`expected`ではなく`actual`だった． -/
  | mismatch (what : String) (expected actual : Ty)
  /-- `if`の2つの枝の型が，`thenTy`と`elseTy`で異なる． -/
  | branches (thenTy elseTy : Ty)
  /-- 変数`x`が文脈にない． -/
  | unbound (x : String)
  /-- 関数でない型`actual`の式を，関数として適用した． -/
  | notFunction (actual : Ty)
  deriving Repr, DecidableEq

/-- 型検査器．文脈`Γ`のもとで式`t`の型を求める．型が付かないときは，その理由を返す． -/
def typeOf (Γ : Ctx) : Term → Except TypeError Ty
  | .num _ => .ok .nat
  | .add t₁ t₂ =>
    match typeOf Γ t₁, typeOf Γ t₂ with
    | .ok .nat, .ok .nat => .ok .nat
    | .ok .nat, .ok T₂ => .error (.mismatch "+の右辺" .nat T₂)
    | .ok T₁, .ok _ => .error (.mismatch "+の左辺" .nat T₁)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .sub t₁ t₂ =>
    match typeOf Γ t₁, typeOf Γ t₂ with
    | .ok .nat, .ok .nat => .ok .nat
    | .ok .nat, .ok T₂ => .error (.mismatch "-の右辺" .nat T₂)
    | .ok T₁, .ok _ => .error (.mismatch "-の左辺" .nat T₁)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .mul t₁ t₂ =>
    match typeOf Γ t₁, typeOf Γ t₂ with
    | .ok .nat, .ok .nat => .ok .nat
    | .ok .nat, .ok T₂ => .error (.mismatch "*の右辺" .nat T₂)
    | .ok T₁, .ok _ => .error (.mismatch "*の左辺" .nat T₁)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .tru => .ok .bool
  | .fls => .ok .bool
  | .ite c t e =>
    match typeOf Γ c, typeOf Γ t, typeOf Γ e with
    | .ok .bool, .ok T, .ok E => if T = E then .ok T else .error (.branches T E)
    | .ok C, .ok _, .ok _ => .error (.mismatch "ifの条件" .bool C)
    | .error err, _, _ => .error err
    | _, .error err, _ => .error err
    | _, _, .error err => .error err
  | .iszero t =>
    match typeOf Γ t with
    | .ok .nat => .ok .bool
    | .ok T => .error (.mismatch "iszeroの引数" .nat T)
    | .error err => .error err
  | .var x =>
    match Γ.lookup x with
    | some T => .ok T
    | none => .error (.unbound x)
  | .let_ x t u =>
    match typeOf Γ t with
    | .ok T => typeOf ((x, T) :: Γ) u
    | .error err => .error err
  | .lam x A t =>
    match typeOf ((x, A) :: Γ) t with
    | .ok B => .ok (.arrow A B)
    | .error err => .error err
  | .app t₁ t₂ =>
    match typeOf Γ t₁, typeOf Γ t₂ with
    | .ok (.arrow A B), .ok A' => if A' = A then .ok B else .error (.mismatch "関数の引数" A A')
    | .ok T, .ok _ => .error (.notFunction T)
    | .error err, _ => .error err
    | _, .error err => .error err
  | .fix f x A B t =>
    match typeOf ((x, A) :: (f, .arrow A B) :: Γ) t with
    | .ok B' => if B' = B then .ok (.arrow A B) else .error (.mismatch "再帰関数の本体" B B')
    | .error err => .error err

end Mini
