# Iteration 1 演習：大ステップ意味論と評価器の正しさ

Miniの式の意味を大ステップ意味論の推論規則で定め，評価器`eval`がその意味に従うことを証明する．
利用者から見える`mini`の振る舞いは，Iteration 0と同じである．

## 進め方

手順は[docs/iteration-1.md](docs/iteration-1.md)にある．
テストリスト → 設計書 → テストファーストの実装 → 設計レビューの順に進める．
模範解答は[../solution/](../solution/)にある．

## ディレクトリ構成

```text
Mini/
  Syntax.lean                    式の抽象構文Term
  Parser.lean                    構文解析器parse(配布物)
  Eval.lean                      評価器eval
  Run.lean                       構文解析と評価をつなぐrun
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/EvalTest.lean      Mini.Evalの単体テスト
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
design/                          設計書
TESTLIST.md                      テストリスト(このIterationで書く)
docs/iteration-1.md              演習の手順
lakefile.toml                    パッケージの設定
```
