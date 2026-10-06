# Iteration 4 演習：型と型検査器

Miniに型`Nat`と`Bool`を導入し，式の型を評価の前に検査する．
型の付く式は決して行き詰まらないこと(型安全性)を証明する．

```text
$ lake exe mini check "if iszero 0 then 1 else 2"
Nat
$ lake exe mini eval "1 + true"
型エラー：+の右辺の型が合わない(期待：Nat，実際：Bool)
```

## 進め方

手順は[docs/iteration-4.md](docs/iteration-4.md)にある．
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
design/                          設計書
TESTLIST.md                      テストリスト(このIterationで書く)
docs/iteration-4.md              演習の手順
lakefile.toml                    パッケージの設定
```
