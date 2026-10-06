# Iteration 6 演習：関数と関数適用

Miniに関数`fun (x : T) => t`と関数適用`t u`，関数型`T → U`を足す．
Miniは単純型付きラムダ計算になり，その型安全性を証明する．

```text
$ lake exe mini eval "let double = fun (x : Nat) => x + x in double 21"
42
$ lake exe mini check "fun (x : Nat) => iszero x"
Nat → Bool
```

## 進め方

手順は[docs/iteration-6.md](docs/iteration-6.md)にある．
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
handout/Parser.lean              関数と関数適用に対応した構文解析器(配布物)
design/                          設計書
TESTLIST.md                      テストリスト(このIterationで書く)
docs/iteration-6.md              演習の手順
lakefile.toml                    パッケージの設定
```
