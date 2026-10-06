import Mini.Subst

/-!
# `Mini.Subst`の単体テスト
-/

namespace MiniTest.SubstTest

open Mini

/-- 自由な変数`x`を置き換え，ほかの変数は残す． -/
example : subst "x" (.num 3) (.add (.var "x") (.var "y")) = .add (.num 3) (.var "y") := by decide

/-- 束縛する式の中は置き換えるが，同じ名前で束縛された本体の中は置き換えない． -/
example : subst "x" (.num 3) (.let_ "x" (.var "x") (.var "x")) = .let_ "x" (.num 3) (.var "x") := by
  decide

/-- 別の名前を束縛する`let`の本体の中は置き換える． -/
example : subst "x" (.num 3) (.let_ "y" (.var "x") (.var "x")) = .let_ "y" (.num 3) (.num 3) := by
  decide

end MiniTest.SubstTest
