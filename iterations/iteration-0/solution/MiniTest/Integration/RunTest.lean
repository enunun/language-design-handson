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

/-! ## 一般の性質 -/

/-- 構文解析に成功した文字列を`run`すると，その式の値が表示される． -/
theorem run_of_parse {s : String} {t : Term} (h : parse s = .ok t) :
    run s = toString (eval t) := by
  simp [run, h]

end MiniTest.RunTest
