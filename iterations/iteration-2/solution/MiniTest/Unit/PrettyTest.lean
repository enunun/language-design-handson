import Mini.Pretty

/-!
# `Mini.Pretty`の単体テスト
-/

namespace MiniTest.PrettyTest

open Mini

example : (Term.num 21).pretty = "21" := by decide +kernel

example : (Term.add (.num 1) (.mul (.num 2) (.num 3))).pretty = "1 + 2 * 3" := by decide +kernel

/-- 強く結合する演算子の中に弱い演算子があるときは，かっこを付ける． -/
example : (Term.mul (.add (.num 1) (.num 2)) (.add (.num 3) (.num 4))).pretty
    = "(1 + 2) * (3 + 4)" := by decide +kernel

/-- 左結合なので，左の部分式にはかっこを付けない． -/
example : (Term.sub (.sub (.num 10) (.num 2)) (.num 3)).pretty = "10 - 2 - 3" := by decide +kernel

/-- 右の部分式に同じ強さの演算子があるときは，かっこを付ける． -/
example : (Term.sub (.num 10) (.sub (.num 2) (.num 3))).pretty = "10 - (2 - 3)" := by decide +kernel

end MiniTest.PrettyTest
