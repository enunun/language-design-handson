# Iteration 1 解答：大ステップ意味論と評価器の正しさ

Iteration 1の演習を完成させたものと，その模範解答である．
大ステップ意味論`Eval`を推論規則で定め，評価器`eval`の健全性と完全性，意味論の決定性を証明している．

## 内容

- [TESTLIST.md](TESTLIST.md)：模範解答のテストリスト．
- [design/spec.md](design/spec.md)，[design/modules.md](design/modules.md)：模範解答の設計書．
- [docs/iteration-1.md](docs/iteration-1.md)：演習の各手順の解説．

## ディレクトリ構成

```text
Mini/
  Syntax.lean                    式の抽象構文Term
  BigStep.lean                   大ステップ意味論Eval
  Parser.lean                    構文解析器parse
  Eval.lean                      評価器eval
  Run.lean                       構文解析と評価をつなぐrun
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/BigStepTest.lean   Mini.BigStepの単体テスト
MiniTest/Unit/EvalTest.lean      Mini.Evalの単体テスト
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
design/                          設計書
TESTLIST.md                      テストリスト
docs/iteration-1.md              解説
lakefile.toml                    パッケージの設定
```
