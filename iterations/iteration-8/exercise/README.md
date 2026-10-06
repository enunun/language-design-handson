# Iteration 8 演習：組

Miniに組`(t, u)`，射影`fst t`と`snd t`，組の型`A × B`を足す．
評価と型付けの推論規則を自分で設計し，その規則のもとでこれまでの性質が成り立つことを証明する．

```text
$ lake exe mini check "fun (p : Nat × Bool) => if snd p then fst p else 0"
Nat × Bool → Nat
$ lake exe mini eval "fst (1 + 2, true)"
3
```

## 進め方

手順は[docs/iteration-8.md](docs/iteration-8.md)にある．
テストリスト → 設計書 → テストファーストの実装 → 設計レビューの順に進める．
模範解答は[../solution/](../solution/)にある．

## ディレクトリ構成

```text
Mini/                            ライブラリ(Syntax，Subst，BigStep，SmallStep，Typing，Eval，Pretty，Parser，Run)
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/                   単体テスト(SubstTest，BigStepTest，SmallStepTest，TypingTest，EvalTest，PrettyTest)
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
handout/Parser.lean              組と射影と組の型に対応した構文解析器(配布物)
design/                          設計書
TESTLIST.md                      テストリスト(このIterationで書く)
docs/iteration-8.md              演習の手順
lakefile.toml                    パッケージの設定
```
