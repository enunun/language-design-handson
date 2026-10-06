# モジュール依存図

ライブラリ`Mini`の各モジュールとコマンド`Main`が，どのモジュールをimportしているかを示す．
矢印`A --> B`は，`A`が`B`をimportしていることを表す．

```mermaid
flowchart LR
  Main["Main"] --> Run["Mini.Run"]
  Run --> Eval["Mini.Eval"]
  Run --> Parser["Mini.Parser"]
  Run --> Pretty["Mini.Pretty"]
  Eval --> Syntax["Mini.Syntax"]
  Parser --> Syntax
  Pretty --> Syntax
  BigStep["Mini.BigStep"] --> Syntax
  SmallStep["Mini.SmallStep"] --> Syntax
```

- `Mini.Syntax`：式の抽象構文`Term`．
- `Mini.BigStep`：大ステップ意味論`Eval`(記法`t ⇓ n`)．
- `Mini.SmallStep`：小ステップ意味論`Step`(記法`t ⟶ t'`)と多ステップ簡約`Steps`(記法`t ⟶* t'`)．
- `Mini.Eval`：評価器`eval`と，1ステップ簡約する関数`step`．
- `Mini.Pretty`：式を具体構文の文字列にする`Term.pretty`．
- `Mini.Parser`：配布された構文解析器`parse`．
- `Mini.Run`：構文解析と評価をつなぎ，表示する文字列を作る`run`と，簡約列を表示する文字列を作る`runSteps`．
- `Main`：コマンド`mini eval <式>`と`mini steps <式>`．
- `Mini.Eval`と`Mini.Parser`はどちらも`Mini.Syntax`だけに依存し，互いには依存しない．
- `Mini.BigStep`と`Mini.SmallStep`は仕様であり，実装のどのモジュールからも使われない．実装との関係は，テストの定理で結び付ける．
