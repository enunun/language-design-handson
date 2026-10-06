# Iteration 8 解答：組

Iteration 8の演習を完成させたものと，その模範解答である．
組`(t, u)`，射影`fst t`と`snd t`，組の型`A × B`を足している．
組の成分を左から順に値まで評価する設計(先行評価)を選び，その規則のもとで決定性，2つの意味論の一致，評価器の正しさ，型安全性を証明している．

## 内容

- [TESTLIST.md](TESTLIST.md)：模範解答のテストリスト．
- [design/spec.md](design/spec.md)，[design/modules.md](design/modules.md)：模範解答の設計書．
- [docs/iteration-8.md](docs/iteration-8.md)：演習の各手順の解説．

## ディレクトリ構成

```text
Mini/
  Syntax.lean                    型Ty，式の抽象構文Term，値Value
  Subst.lean                     置換subst
  BigStep.lean                   大ステップ意味論Eval
  SmallStep.lean                 IsValue，Step，Steps，NormalとStuck
  Typing.lean                    文脈Ctx，型付け規則HasType，型検査器typeOf
  Parser.lean                    構文解析器parse
  Eval.lean                      1ステップの簡約stepと燃料つきの評価器eval
  Pretty.lean                    式と値と型の表示
  Run.lean                       run，runCheck，runSteps
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/                   単体テスト(SubstTest，BigStepTest，SmallStepTest，TypingTest，EvalTest，PrettyTest)
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
design/                          設計書
TESTLIST.md                      テストリスト
docs/iteration-8.md              解説
lakefile.toml                    パッケージの設定
```
