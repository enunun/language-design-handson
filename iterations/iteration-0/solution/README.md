# Iteration 0 解答：自然数の四則と評価器

Iteration 0の演習を完成させたものと，その模範解答である．
自然数と`+`，`-`，`*`，かっこからなる式を評価する．

```text
$ lake exe mini eval "1 + 2 * 3"
7
$ lake exe mini eval "1 +"
構文エラー：式が途中で終わっている
```

## 内容

- [TESTLIST.md](TESTLIST.md)：模範解答のテストリスト．
- [design/spec.md](design/spec.md)，[design/modules.md](design/modules.md)：模範解答の設計書．
- [docs/iteration-0.md](docs/iteration-0.md)：演習の各手順の解説．

## ディレクトリ構成

```text
Mini/
  Syntax.lean                    式の抽象構文Term
  Parser.lean                    構文解析器parse
  Eval.lean                      評価器eval
  Run.lean                       構文解析と評価をつなぐrun
Mini.lean                        ライブラリMiniの入口
Main.lean                        コマンドmini
MiniTest/Unit/EvalTest.lean      Mini.Evalの単体テスト
MiniTest/Integration/RunTest.lean
                                 Mini.Runの統合テスト
design/                          設計書
TESTLIST.md                      テストリスト
docs/iteration-0.md              解説
lakefile.toml                    パッケージの設定
```
