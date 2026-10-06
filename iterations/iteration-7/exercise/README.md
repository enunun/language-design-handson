# Iteration 7 演習：再帰

Miniに再帰関数`fix f (x : A) : B => t`を足す．
評価が終わらない式を書けるようになるが，型安全性は保たれることを証明する．

```text
$ lake exe mini eval "(fix fact (n : Nat) : Nat => if iszero n then 1 else n * fact (n - 1)) 5"
120
$ lake exe mini eval --fuel 1000 "(fix loop (n : Nat) : Nat => loop n) 0"
燃料切れ：1000ステップで評価が終わらなかった
```

## 進め方

手順は[docs/iteration-7.md](docs/iteration-7.md)にある．
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
handout/Parser.lean              再帰関数に対応した構文解析器(配布物)
design/                          設計書
TESTLIST.md                      テストリスト(このIterationで書く)
docs/iteration-7.md              演習の手順
lakefile.toml                    パッケージの設定
```
