# Iteration 7 解答：再帰

Iteration 7の演習を完成させたものと，その模範解答である．
再帰関数`fix f (x : A) : B => t`を足し，評価が終わらない式`loop 0`に値がないことを証明している．
一般再帰を足しても，型安全性が保たれることを証明している．

## 内容

- [TESTLIST.md](TESTLIST.md)：模範解答のテストリスト．
- [design/spec.md](design/spec.md)，[design/modules.md](design/modules.md)：模範解答の設計書．
- [docs/iteration-7.md](docs/iteration-7.md)：演習の各手順の解説．

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
docs/iteration-7.md              解説
lakefile.toml                    パッケージの設定
```
