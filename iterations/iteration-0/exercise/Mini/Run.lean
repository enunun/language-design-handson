import Mini.Eval
import Mini.Parser

/-!
# 実行

構文解析と評価をつなぎ，コマンド`mini`が表示する文字列を作る．
-/

namespace Mini

/-- 文字列`s`を構文解析して評価し，表示する文字列を返す．仮の実装で，空の文字列を返す． -/
def run : String → String := fun _ => ""

end Mini
