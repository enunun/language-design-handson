# Iteration 3 解答：真偽値と条件分岐

Iteration 3の演習を完成させたものと，その模範解答である．
真偽値，`if`，`iszero`を足し，評価の結果を値`Value`(自然数か真偽値)にしている．
行き詰まった式を定義し，`then`の枝を先に簡約する意味論が決定的でないことを証明している．

## 内容

- [TESTLIST.md](TESTLIST.md)：模範解答のテストリスト．
- [design/spec.md](design/spec.md)，[design/modules.md](design/modules.md)：模範解答の設計書．
- [docs/iteration-3.md](docs/iteration-3.md)：演習の各手順の解説．

## ディレクトリ構成

```text
Mini/
  Syntax.lean                    式の抽象構文Termと値Value
  BigStep.lean                   大ステップ意味論Eval
  SmallStep.lean                 小ステップ意味論Step，Steps，NormalとStuck
  Parser.lean                    構文解析器parse
  Eval.lean                      評価器evalと1ステップの簡約step
  Pretty.lean                    式と値の表示
  Run.lean                       runとrunSteps
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/                   単体テスト(BigStepTest，SmallStepTest，EvalTest，PrettyTest)
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
design/                          設計書
TESTLIST.md                      テストリスト
docs/iteration-3.md              解説
lakefile.toml                    パッケージの設定
```
