# Iteration 2 演習：簡約列の表示

式を1ステップずつ簡約する小ステップ意味論を定め，コマンド`mini steps`で簡約の過程を表示する．
小ステップ意味論の決定性と，大ステップ意味論との一致を証明する．

```text
$ lake exe mini steps "(1 + 2) * (3 + 4)"
(1 + 2) * (3 + 4)
⟶ 3 * (3 + 4)
⟶ 3 * 7
⟶ 21
```

## 進め方

手順は[docs/iteration-2.md](docs/iteration-2.md)にある．
テストリスト → 設計書 → テストファーストの実装 → 設計レビューの順に進める．
模範解答は[../solution/](../solution/)にある．

## ディレクトリ構成

```text
Mini/
  Syntax.lean                    式の抽象構文Term
  BigStep.lean                   大ステップ意味論Eval
  Parser.lean                    構文解析器parse(配布物)
  Eval.lean                      評価器eval
  Run.lean                       構文解析と評価をつなぐrun
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/                   単体テスト(BigStepTest，EvalTest)
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
design/                          設計書
TESTLIST.md                      テストリスト(このIterationで書く)
docs/iteration-2.md              演習の手順
lakefile.toml                    パッケージの設定
```
