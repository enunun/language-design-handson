import Mini.Syntax

/-!
# 式と値と型の表示

式と値と型を，具体構文の文字列にする．
-/

namespace Mini

/-- `b`が真なら，`s`をかっこで囲む． -/
def parenIf (b : Bool) (s : String) : String :=
  if b then s!"({s})" else s

/-- 結合の強さ`p`の位置に置く式`t`を文字列にする．
`if`と`let`の強さは`0`，`+`と`-`は`1`，`*`は`2`，`iszero`は`3`，数などの最小の式は`4`である．
左結合なので，二項演算子の右の部分式は1つ強い位置に置く． -/
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

/-- 式`t`を，必要なところだけかっこを付けた具体構文の文字列にする． -/
def Term.pretty (t : Term) : String :=
  t.prettyPrec 0

/-- 値を文字列にする． -/
def Value.pretty : Value → String
  | .num n => toString n
  | .bool true => "true"
  | .bool false => "false"

/-- 型を文字列にする． -/
def Ty.pretty : Ty → String
  | .nat => "Nat"
  | .bool => "Bool"

end Mini
