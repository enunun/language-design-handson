import Mini.Syntax

/-!
# 式の表示

式を具体構文の文字列にする．
-/

namespace Mini

/-- `b`が真なら，`s`をかっこで囲む． -/
def parenIf (b : Bool) (s : String) : String :=
  if b then s!"({s})" else s

/-- 結合の強さ`p`の位置に置く式`t`を文字列にする．
`+`と`-`の強さは`1`，`*`の強さは`2`である．
左結合なので，右の部分式は1つ強い位置に置く． -/
def Term.prettyPrec : Nat → Term → String
  | _, .num n => toString n
  | p, .add t₁ t₂ => parenIf (p > 1) s!"{prettyPrec 1 t₁} + {prettyPrec 2 t₂}"
  | p, .sub t₁ t₂ => parenIf (p > 1) s!"{prettyPrec 1 t₁} - {prettyPrec 2 t₂}"
  | p, .mul t₁ t₂ => parenIf (p > 2) s!"{prettyPrec 2 t₁} * {prettyPrec 3 t₂}"

/-- 式`t`を，必要なところだけかっこを付けた具体構文の文字列にする． -/
def Term.pretty (t : Term) : String :=
  t.prettyPrec 0

end Mini
