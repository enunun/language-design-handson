import Mini.Eval
import Mini.Parser

/-!
# 実行

構文解析と評価をつなぎ，コマンド`mini`が表示する文字列を作る．
-/

namespace Mini

/-- 文字列`s`を構文解析して評価し，表示する文字列を返す． -/
def run (s : String) : String :=
  match parse s with
  | .ok t => toString (eval t)
  | .error e => s!"構文エラー：{e}"

end Mini
