# Iteration 3 演習：真偽値と条件分岐

Miniに真偽値`true`と`false`，条件式`if c then t else e`，`iszero t`を足す．
評価の結果を自然数か真偽値にし，`1 + true`のように行き詰まる式を実行時エラーとして表示する．

```text
$ lake exe mini eval "if iszero (2 - 2) then 10 else 20"
10
$ lake exe mini eval "1 + true"
実行時エラー：評価が行き詰まった(1 + true)
```

## 進め方

手順は[docs/iteration-3.md](docs/iteration-3.md)にある．
テストリスト → 設計書 → テストファーストの実装 → 設計レビューの順に進める．
模範解答は[../solution/](../solution/)にある．

## ディレクトリ構成

```text
Mini/                            ライブラリ(Syntax，BigStep，SmallStep，Eval，Pretty，Parser，Run)
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/                   単体テスト(BigStepTest，SmallStepTest，EvalTest，PrettyTest)
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
handout/Parser.lean              このIterationの構文に対応した構文解析器(配布物)
design/                          設計書
TESTLIST.md                      テストリスト(このIterationで書く)
docs/iteration-3.md              演習の手順
lakefile.toml                    パッケージの設定
```
