# Iteration 2 解答：簡約列の表示

Iteration 2の演習を完成させたものと，その模範解答である．
小ステップ意味論`Step`と多ステップ簡約`Steps`を定め，1ステップ簡約する関数`step`，式を表示する`Term.pretty`，簡約列を表示する`mini steps`を実装している．

## 内容

- [TESTLIST.md](TESTLIST.md)：模範解答のテストリスト．
- [design/spec.md](design/spec.md)，[design/modules.md](design/modules.md)：模範解答の設計書．
- [docs/iteration-2.md](docs/iteration-2.md)：演習の各手順の解説．

## ディレクトリ構成

```text
Mini/
  Syntax.lean                    式の抽象構文Term
  BigStep.lean                   大ステップ意味論Eval
  SmallStep.lean                 小ステップ意味論Stepと多ステップ簡約Steps
  Parser.lean                    構文解析器parse
  Eval.lean                      評価器evalと1ステップの簡約step
  Pretty.lean                    式の表示Term.pretty
  Run.lean                       runとrunSteps
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/                   単体テスト(BigStepTest，SmallStepTest，EvalTest，PrettyTest)
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
design/                          設計書
TESTLIST.md                      テストリスト
docs/iteration-2.md              解説
lakefile.toml                    パッケージの設定
```
