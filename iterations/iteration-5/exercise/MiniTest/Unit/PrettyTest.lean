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

example : (Term.ite (.iszero (.sub (.num 2) (.num 2))) (.num 10) (.num 20)).pretty
    = "if iszero (2 - 2) then 10 else 20" := by decide +kernel

/-- `if`を演算子の左に置くときは，かっこを付ける． -/
example : (Term.add (.ite .tru (.num 1) (.num 2)) (.num 3)).pretty
    = "(if true then 1 else 2) + 3" := by decide +kernel

/-- `iszero`は`*`より強く結合する． -/
example : (Term.mul (.iszero (.num 0)) (.num 2)).pretty = "iszero 0 * 2" := by decide +kernel

example : (Value.num 3).pretty = "3" := by decide +kernel

example : (Value.bool false).pretty = "false" := by decide +kernel

example : Ty.nat.pretty = "Nat" := by decide +kernel

example : Ty.bool.pretty = "Bool" := by decide +kernel

end MiniTest.PrettyTest
