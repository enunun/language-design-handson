# Iteration 5 演習：変数と`let`

Miniに変数と`let x = t in u`を足す．
置換が型を保つこと(置換補題)を証明し，評価器を燃料つきの形に作り直す．

```text
$ lake exe mini eval "let x = 1 + 2 in x * x"
9
$ lake exe mini check "let x = 1 in y"
型エラー：変数yが定義されていない
```

## 進め方

手順は[docs/iteration-5.md](docs/iteration-5.md)にある．
テストリスト → 設計書 → テストファーストの実装 → 設計レビューの順に進める．
模範解答は[../solution/](../solution/)にある．

## ディレクトリ構成

```text
Mini/                            ライブラリ(Syntax，BigStep，SmallStep，Typing，Eval，Pretty，Parser，Run)
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/                   単体テスト(BigStepTest，SmallStepTest，TypingTest，EvalTest，PrettyTest)
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
handout/Parser.lean              変数とletに対応した構文解析器(配布物)
design/                          設計書
TESTLIST.md                      テストリスト(このIterationで書く)
docs/iteration-5.md              演習の手順
lakefile.toml                    パッケージの設定
```
