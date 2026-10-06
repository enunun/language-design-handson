# Iteration 0 演習：自然数の四則と評価器

自然数と`+`，`-`，`*`，かっこからなる式を評価する処理系を作る．
評価器`eval`と，構文解析から評価までをつなぐ`run`を実装し，その振る舞いと性質をLeanの定理として証明する．

```text
$ lake exe mini eval "1 + 2 * 3"
7
```

## 進め方

手順は[docs/iteration-0.md](docs/iteration-0.md)にある．
テストリスト → 設計書 → テストファーストの実装 → 設計レビューの順に進める．
模範解答は[../solution/](../solution/)にある．

## ディレクトリ構成

```text
Mini/
  Syntax.lean          式の抽象構文Term
  Parser.lean          構文解析器parse(配布物)
  Eval.lean            評価器eval(仮の実装)
  Run.lean             構文解析と評価をつなぐrun(仮の実装)
Mini.lean              ライブラリMiniの入口
Main.lean              コマンドmini
MiniTest.lean          テストの入口
MiniTest/Unit.lean     単体テストの入口
MiniTest/Integration.lean
                       統合テストの入口
design/spec.md         言語仕様書
design/modules.md      モジュール依存図
TESTLIST.md            テストリスト
docs/iteration-0.md    演習の手順
lakefile.toml          パッケージの設定
```
