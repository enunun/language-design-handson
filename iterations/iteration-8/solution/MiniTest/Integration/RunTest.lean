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

example : run "let double = fun (x : Nat) => x + x in double 21" = "42" := by decide +kernel

/-- 関数を引数として受け取る関数． -/
example : run "(fun (f : Nat -> Nat) => f (f 3)) (fun (x : Nat) => x * x)" = "81" := by decide +kernel

/-- 関数も値である． -/
example : run "fun (x : Nat) => x" = "fun (x : Nat) => x" := by decide +kernel

example : run "(fun (x : Nat) => x) true" = "型エラー：関数の引数の型が合わない(期待：Nat，実際：Bool)" := by
  decide +kernel

example : run "1 2" = "型エラー：関数でない式を適用している(型：Nat)" := by decide +kernel

example : run "(fix fact (n : Nat) : Nat => if iszero n then 1 else n * fact (n - 1)) 5" = "120" := by
  decide +kernel

/-- 評価が終わらない式は，燃料切れになる． -/
example : run "(fix loop (n : Nat) : Nat => loop n) 0" 1000 = "燃料切れ：1000ステップで評価が終わらなかった" := by
  decide +kernel

example : run "fix f (x : Nat) : Bool => x" = "型エラー：再帰関数の本体の型が合わない(期待：Bool，実際：Nat)" := by
  decide +kernel

example : run "fst (1 + 2, true)" = "3" := by decide +kernel

/-- 組の値は，成分の値の組として表示する． -/
example : run "(1, (iszero 0, 1 + 1))" = "(1, (true, 2))" := by decide +kernel

/-- 組を受け取って組を返す関数． -/
example : run "let swap = fun (p : Nat × Bool) => (snd p, fst p) in swap (1, true)" = "(true, 1)" := by
  decide +kernel

example : run "fst 1" = "型エラー：組でない式から成分を取り出している(型：Nat)" := by decide +kernel

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

example : runCheck "fun (x : Nat) => iszero x" = "Nat → Bool" := by decide +kernel

example : runCheck "fun (f : Nat → Nat) => fun (x : Nat) => f (f x)" = "(Nat → Nat) → Nat → Nat" := by
  decide +kernel

example : runCheck "fix fact (n : Nat) : Nat => if iszero n then 1 else n * fact (n - 1)" = "Nat → Nat" := by
  decide +kernel

example : runCheck "fun (p : Nat × Bool) => if snd p then fst p else 0" = "Nat × Bool → Nat" := by
  decide +kernel

/-- 組の型の`×`は`*`とも書ける． -/
example : runCheck "fun (p : Nat * Bool) => (snd p, fst p)" = "Nat × Bool → Bool × Nat" := by
  decide +kernel

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

example : runSteps "(fun (x : Nat) => x + 1) 2" = "(fun (x : Nat) => x + 1) 2\n⟶ 2 + 1\n⟶ 3" := by
  decide +kernel

/-- `loop 0`は1ステップで自分自身に戻る． -/
example : runSteps "(fix loop (n : Nat) : Nat => loop n) 0" 2
    = "(fix loop (n : Nat) : Nat => loop n) 0\n⟶ (fix loop (n : Nat) : Nat => loop n) 0\n⟶ (fix loop (n : Nat) : Nat => loop n) 0" := by
  decide +kernel

/-- 組の成分を左から値まで簡約してから，成分を取り出す． -/
example : runSteps "fst (1 + 2, iszero 0)" = "fst (1 + 2, iszero 0)\n⟶ fst (3, iszero 0)\n⟶ fst (3, true)\n⟶ 3" := by
  decide +kernel

/-- 表示するステップ数の上限を指定できる． -/
example : runSteps "1 + 2 + 3" 1 = "1 + 2 + 3\n⟶ 3 + 3" := by decide +kernel

/-- 行き詰まった式は，それ以上簡約列を伸ばさない． -/
example : runSteps "1 + true" = "1 + true" := by decide +kernel

end MiniTest.RunTest
