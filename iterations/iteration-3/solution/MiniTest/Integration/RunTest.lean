import Mini.Run

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

/-- 数と真偽値は足せないので，評価が行き詰まる．行き詰まった式を表示する． -/
example : run "1 + true" = "実行時エラー：評価が行き詰まった(1 + true)" := by decide +kernel

/-- 行き詰まるまで簡約してから，その式を表示する． -/
example : run "(1 + 2) * iszero 0" = "実行時エラー：評価が行き詰まった(3 * true)" := by decide +kernel

/-- 条件が真偽値でない`if`は行き詰まる． -/
example : run "if 1 then 2 else 3" = "実行時エラー：評価が行き詰まった(if 1 then 2 else 3)" := by
  decide +kernel

example : run "1 + x" = "構文エラー：知らない単語がある(x)" := by decide +kernel

/-! ## 一般の性質 -/

/-- 構文解析と評価に成功した文字列を`run`すると，その値が表示される． -/
theorem run_of_eval {s : String} {t : Term} {v : Value} (hp : parse s = .ok t) (he : eval t = some v) :
    run s = v.pretty := by
  simp [run, hp, he]

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

/-- 行き詰まった式は，それ以上簡約列を伸ばさない． -/
example : runSteps "1 + true" = "1 + true" := by decide +kernel

end MiniTest.RunTest
