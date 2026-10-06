import Mini.Syntax

/-!
# 式と値と型の表示

式と値と型を，具体構文の文字列にする．
-/

namespace Mini

/-- `b`が真なら，`s`をかっこで囲む． -/
def parenIf (b : Bool) (s : String) : String :=
  if b then s!"({s})" else s

/-- 結合の強さ`p`の位置に置く型を文字列にする．`→`の強さは`0`で，右に結合する． -/
def Ty.prettyPrec : Nat → Ty → String
  | _, .nat => "Nat"
  | _, .bool => "Bool"
  | p, .arrow A B => parenIf (p > 0) s!"{prettyPrec 1 A} → {prettyPrec 0 B}"

/-- 型を文字列にする． -/
def Ty.pretty (T : Ty) : String :=
  T.prettyPrec 0

/-- 結合の強さ`p`の位置に置く式`t`を文字列にする．
`if`と`let`と`fun`と`fix`の強さは`0`，`+`と`-`は`1`，`*`は`2`，関数適用と`iszero`は`3`，数などの最小の式は`4`である．
左結合なので，二項演算子と関数適用の右の部分式は1つ強い位置に置く． -/
def Term.prettyPrec : Nat → Term → String
  | _, .num n => toString n
  | p, .add t₁ t₂ => parenIf (p > 1) s!"{prettyPrec 1 t₁} + {prettyPrec 2 t₂}"
  | p, .sub t₁ t₂ => parenIf (p > 1) s!"{prettyPrec 1 t₁} - {prettyPrec 2 t₂}"
  | p, .mul t₁ t₂ => parenIf (p > 2) s!"{prettyPrec 2 t₁} * {prettyPrec 3 t₂}"
  | _, .tru => "true"
  | _, .fls => "false"
  | p, .ite c t e =>
    parenIf (p > 0) s!"if {prettyPrec 0 c} then {prettyPrec 0 t} else {prettyPrec 0 e}"
  | p, .iszero t => parenIf (p > 3) s!"iszero {prettyPrec 4 t}"
  | _, .var x => x
  | p, .let_ x t u => parenIf (p > 0) s!"let {x} = {prettyPrec 0 t} in {prettyPrec 0 u}"
  | p, .lam x A t => parenIf (p > 0) s!"fun ({x} : {A.pretty}) => {prettyPrec 0 t}"
  | p, .app t₁ t₂ => parenIf (p > 3) s!"{prettyPrec 3 t₁} {prettyPrec 4 t₂}"
  | p, .fix f x A B t => parenIf (p > 0) s!"fix {f} ({x} : {A.pretty}) : {B.pretty} => {prettyPrec 0 t}"

/-- 式`t`を，必要なところだけかっこを付けた具体構文の文字列にする． -/
def Term.pretty (t : Term) : String :=
  t.prettyPrec 0

/-- 値を文字列にする． -/
def Value.pretty : Value → String
  | .num n => toString n
  | .bool true => "true"
  | .bool false => "false"
  | .lam x A t => (Term.lam x A t).pretty
  | .fix f x A B t => (Term.fix f x A B t).pretty

end Mini
