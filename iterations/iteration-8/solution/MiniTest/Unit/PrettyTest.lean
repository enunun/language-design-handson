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

example : (Term.let_ "x" (.add (.num 1) (.num 2)) (.mul (.var "x") (.var "x"))).pretty
    = "let x = 1 + 2 in x * x" := by decide +kernel

/-- `let`を演算子の左に置くときは，かっこを付ける． -/
example : (Term.add (.let_ "x" (.num 1) (.var "x")) (.num 2)).pretty = "(let x = 1 in x) + 2" := by
  decide +kernel

example : (Term.lam "x" .nat (.add (.var "x") (.var "x"))).pretty = "fun (x : Nat) => x + x" := by
  decide +kernel

/-- 関数適用の関数が`fun`なら，かっこを付ける． -/
example : (Term.app (.lam "x" .nat (.var "x")) (.num 2)).pretty = "(fun (x : Nat) => x) 2" := by
  decide +kernel

/-- 関数適用は左に結合する．引数が関数適用なら，かっこを付ける． -/
example : (Term.app (.app (.var "f") (.var "x")) (.app (.var "g") (.var "y"))).pretty = "f x (g y)" := by
  decide +kernel

/-- 関数適用は`*`より強く結合する． -/
example : (Term.mul (.var "n") (.app (.var "f") (.sub (.var "n") (.num 1)))).pretty = "n * f (n - 1)" := by
  decide +kernel

example : (Term.fix "f" "x" .nat .nat (.app (.var "f") (.var "x"))).pretty = "fix f (x : Nat) : Nat => f x" := by
  decide +kernel

/-- 関数適用の関数が`fix`なら，かっこを付ける． -/
example : (Term.app (.fix "f" "x" .nat .nat (.var "x")) (.num 0)).pretty = "(fix f (x : Nat) : Nat => x) 0" := by
  decide +kernel

/-- 組はいつもかっこで囲む．成分にはかっこを付けない． -/
example : (Term.pair (.num 1) (.add (.num 1) (.num 2))).pretty = "(1, 1 + 2)" := by decide +kernel

/-- `fst`と`snd`は関数適用と同じ強さで結合する． -/
example : (Term.add (.fst (.var "p")) (.snd (.app (.var "f") (.var "x")))).pretty = "fst p + snd (f x)" := by
  decide +kernel

example : (Value.pair (.num 1) (.pair (.bool true) (.num 2))).pretty = "(1, (true, 2))" := by decide +kernel

example : Ty.nat.pretty = "Nat" := by decide +kernel

/-- `→`は右に結合する．左の型が関数型なら，かっこを付ける． -/
example : (Ty.arrow (.arrow .nat .nat) (.arrow .nat .bool)).pretty = "(Nat → Nat) → Nat → Bool" := by
  decide +kernel

example : Ty.bool.pretty = "Bool" := by decide +kernel

/-- `×`は`→`より強く結合する． -/
example : (Ty.arrow (.prod .nat .bool) .nat).pretty = "Nat × Bool → Nat" := by decide +kernel

example : (Ty.prod (.arrow .nat .nat) .nat).pretty = "(Nat → Nat) × Nat" := by decide +kernel

/-- `×`は右に結合する．左の型が組の型なら，かっこを付ける． -/
example : (Ty.prod (.prod .nat .bool) (.prod .nat .bool)).pretty = "(Nat × Bool) × Nat × Bool" := by
  decide +kernel

end MiniTest.PrettyTest
