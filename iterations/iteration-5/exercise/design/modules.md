# モジュール依存図

ライブラリ`Mini`の各モジュールとコマンド`Main`が，どのモジュールをimportしているかを示す．
矢印`A --> B`は，`A`が`B`をimportしていることを表す．

```mermaid
flowchart LR
  Main["Main"] --> Run["Mini.Run"]
  Run --> Eval["Mini.Eval"]
  Run --> Parser["Mini.Parser"]
  Run --> Pretty["Mini.Pretty"]
  Run --> Typing["Mini.Typing"]
  Eval --> Syntax["Mini.Syntax"]
  Parser --> Syntax
  Pretty --> Syntax
  Typing --> Syntax
  BigStep["Mini.BigStep"] --> Syntax
  SmallStep["Mini.SmallStep"] --> Syntax
```

- `Mini.Syntax`：型`Ty`，式の抽象構文`Term`，評価の結果の値`Value`．
- `Mini.Typing`：型付け規則`HasType`，型エラー`TypeError`，型検査器`typeOf`，値の型`Value.ty`．
- `Mini.BigStep`：大ステップ意味論`Eval`(記法`t ⇓ v`)．
- `Mini.SmallStep`：小ステップ意味論`Step`(記法`t ⟶ t'`)，多ステップ簡約`Steps`(記法`t ⟶* t'`)，正規形`Normal`と行き詰まった式`Stuck`．
- `Mini.Eval`：評価器`eval`と，1ステップ簡約する関数`step`．
- `Mini.Pretty`：式と値と型を文字列にする`Term.pretty`，`Value.pretty`，`Ty.pretty`．
- `Mini.Parser`：配布された構文解析器`parse`．
- `Mini.Run`：構文解析と型検査と評価をつなぐ`run`，型を表示する`runCheck`，簡約列を表示する`runSteps`．型エラーを文字列にする`TypeError.message`もここに置く．
- `Main`：コマンド`mini eval <式>`，`mini steps <式>`，`mini check <式>`．
- `Mini.Eval`と`Mini.Parser`はどちらも`Mini.Syntax`だけに依存し，互いには依存しない．
- `Mini.BigStep`と`Mini.SmallStep`は仕様であり，実装のどのモジュールからも使われない．実装との関係は，テストの定理で結び付ける．
