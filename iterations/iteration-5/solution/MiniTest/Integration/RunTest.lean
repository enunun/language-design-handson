import Mini.Run
import MiniTest.Unit.TypingTest

/-!
# `Mini.Run`の統合テスト

文字列を入力にした具体例は，`decide +kernel`で証明する．
-/

namespace MiniTest.RunTest

open Mini

/-! ## 具体例 -/

/-- `*`は`+`より強く結合する． -/
example : run "1 + 2 * 3" = "7" := by decide +kernel

example : run "(1 + 2) * 3" = "9" := by decide +kernel

/-- `-`は左から結合する． -/
example : run "10 - 2 - 3" = "5" := by decide +kernel

example : run "2 - 5" = "0" := by decide +kernel

example : run "1 +" = "構文エラー：式が途中で終わっている" := by decide +kernel

example : run "if iszero (2 - 2) then 10 else 20" = "10" := by decide +kernel

example : run "iszero 3" = "false" := by decide +kernel

/-- 型が付かない式は評価しない． -/
example : run "1 + true" = "型エラー：+の右辺の型が合わない(期待：Nat，実際：Bool)" := by decide +kernel

example : run "(1 + 2) * iszero 0" = "型エラー：*の右辺の型が合わない(期待：Nat，実際：Bool)" := by
  decide +kernel

example : run "if 1 then 2 else 3" = "型エラー：ifの条件の型が合わない(期待：Bool，実際：Nat)" := by
  decide +kernel

/-- 評価すれば値になる式でも，型が付かなければ評価しない． -/
example : run "if true then 0 else false" = "型エラー：ifの2つの枝の型が合わない(then：Nat，else：Bool)" := by
  decide +kernel

example : run "1 + x" = "型エラー：変数xが定義されていない" := by decide +kernel

example : run "let x = 1 + 2 in x * x" = "9" := by decide +kernel

/-- 内側の`let`が外側の`x`を隠す． -/
example : run "let x = 1 in let x = x + 1 in x * 10" = "20" := by decide +kernel

example : run "let x = 1 in y" = "型エラー：変数yが定義されていない" := by decide +kernel

/-- 燃料を使い切ると，評価が終わらなかったことを表示する． -/
example : run "1 + 2 + 3" 2 = "燃料切れ：2ステップで評価が終わらなかった" := by decide +kernel

example : run "1 + 2 + 3" 3 = "6" := by decide +kernel

/-! ## 一般の性質 -/

/-- 構文解析と型検査と評価に成功した文字列を`run`すると，その値が表示される． -/
theorem run_of_eval {s : String} {fuel : Nat} {t : Term} {T : Ty} {v : Value}
    (hp : parse s = .ok t) (ht : typeOf [] t = .ok T) (he : eval fuel t = .ok v) :
    run s fuel = v.pretty := by
  simp [run, hp, ht, he]

/-- 型検査を通った文字列を`run`すると，値が表示されるか，燃料切れになる．実行時エラーにはならない． -/
theorem run_well_typed {s : String} {fuel : Nat} {t : Term} {T : Ty}
    (hp : parse s = .ok t) (ht : typeOf [] t = .ok T) :
    (∃ v : Value, run s fuel = v.pretty) ∨ run s fuel = EvalError.outOfFuel.message fuel := by
  cases he : eval fuel t with
  | ok v => exact .inl ⟨v, run_of_eval hp ht he⟩
  | error err =>
    cases err with
    | stuck t' => exact absurd he (TypingTest.eval_not_stuck (TypingTest.typeOf_sound ht))
    | outOfFuel => exact .inr (by simp [run, hp, ht, he])

/-! ## 型の表示 -/

example : runCheck "if iszero 0 then 1 else 2" = "Nat" := by decide +kernel

example : runCheck "iszero (1 + 2)" = "Bool" := by decide +kernel

example : runCheck "1 + true" = "型エラー：+の右辺の型が合わない(期待：Nat，実際：Bool)" := by decide +kernel

example : runCheck "1 +" = "構文エラー：式が途中で終わっている" := by decide +kernel

example : runCheck "let b = iszero 0 in if b then 1 else 2" = "Nat" := by decide +kernel

/-! ## 簡約列の表示 -/

example : runSteps "(1 + 2) * (3 + 4)" = "(1 + 2) * (3 + 4)\n⟶ 3 * (3 + 4)\n⟶ 3 * 7\n⟶ 21" := by
  decide +kernel

/-- `-`は左から結合するので，左の引き算から簡約する． -/
example : runSteps "10 - 2 - 3" = "10 - 2 - 3\n⟶ 8 - 3\n⟶ 5" := by decide +kernel

/-- 数は簡約できないので，1行だけ表示する． -/
example : runSteps "7" = "7" := by decide +kernel

example : runSteps "1 +" = "構文エラー：式が途中で終わっている" := by decide +kernel

example : runSteps "if iszero (2 - 2) then 10 else 20"
    = "if iszero (2 - 2) then 10 else 20\n⟶ if iszero 0 then 10 else 20\n⟶ if true then 10 else 20\n⟶ 10" := by
  decide +kernel

example : runSteps "let x = 1 + 2 in x * x" = "let x = 1 + 2 in x * x\n⟶ let x = 3 in x * x\n⟶ 3 * 3\n⟶ 9" := by
  decide +kernel

/-- 表示するステップ数の上限を指定できる． -/
example : runSteps "1 + 2 + 3" 1 = "1 + 2 + 3\n⟶ 3 + 3" := by decide +kernel

/-- 行き詰まった式は，それ以上簡約列を伸ばさない． -/
example : runSteps "1 + true" = "1 + true" := by decide +kernel

end MiniTest.RunTest
