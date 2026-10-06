# Iteration 4 解答：型と型検査器

Iteration 4の演習を完成させたものと，その模範解答である．
型付け規則`HasType`と型検査器`typeOf`を定め，型検査器の健全性と完全性，進行，保存，型安全性を証明している．
`mini check`で式の型を表示し，`mini eval`は型を検査してから評価する．

## 内容

- [TESTLIST.md](TESTLIST.md)：模範解答のテストリスト．
- [design/spec.md](design/spec.md)，[design/modules.md](design/modules.md)：模範解答の設計書．
- [docs/iteration-4.md](docs/iteration-4.md)：演習の各手順の解説．

## ディレクトリ構成

```text
Mini/
  Syntax.lean                    型Ty，式の抽象構文Term，値Value
  BigStep.lean                   大ステップ意味論Eval
  SmallStep.lean                 小ステップ意味論Step，Steps，NormalとStuck
  Typing.lean                    型付け規則HasTypeと型検査器typeOf
  Parser.lean                    構文解析器parse
  Eval.lean                      評価器evalと1ステップの簡約step
  Pretty.lean                    式と値と型の表示
  Run.lean                       run，runCheck，runSteps
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/                   単体テスト(BigStepTest，SmallStepTest，TypingTest，EvalTest，PrettyTest)
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
design/                          設計書
TESTLIST.md                      テストリスト
docs/iteration-4.md              解説
lakefile.toml                    パッケージの設定
```
