# 定理によるテスト駆動開発

このハンズオンでは，テストをLeanの定理として書き，テスト駆動開発で処理系を育てる．
このガイドでは，テストの書き方と進め方を説明する．
例には，図形の面積を求める小さなパッケージを使う．

## テストは定理である

一般のテストは，いくつかの入力で関数を実行し，結果を期待値と比べる．
Leanのテストは定理である．定理には2種類ある．

- 具体例：`example : area (.rect 2 3) = 6 := by decide`のように，特定の入力についての等式を，計算して証明する．
- 一般の性質：`theorem area_rect_comm (w h : Nat) : area (.rect w h) = area (.rect h w)`のように，すべての入力について成り立つことを証明する．

一般の性質は，入力を1つずつ試すテストでは確かめきれない主張を，すべての入力について保証する．
言語の性質(決定性や型安全性など)は，この形で書く．

テストは`lake test`でまとめて検査する．
すべての定理の証明が通れば成功である．

## Red → Green → Refactor

テストリストの項目を1つずつ，次の3段階で進める．

### Red

まずテストを書き，失敗することを確かめる．
具体例のテストは，実装がまだなければ`decide`が失敗する．

```lean
example : area (.rect 2 3) = 6 := by decide
```

```text
$ lake test
✖ [3/5] Building ShapeTest.Unit.AreaTest (350ms)
error: ShapeTest/Unit/AreaTest.lean:3:37: Tactic `decide` proved that the proposition
  area (Shape.rect 2 3) = 6
is false
Some required targets logged failures:
- ShapeTest.Unit.AreaTest
error: build failed
```

一般の性質のテストは，主張を書いて証明を`sorry`にする．
パッケージは警告をエラーとして扱うので，`sorry`が残っている間は`lake test`が失敗する．

```lean
theorem area_rect_comm (w h : Nat) : area (.rect w h) = area (.rect h w) := by
  sorry
```

```text
$ lake test
✖ [3/5] Building ShapeTest.Unit.AreaTest (352ms)
error: ShapeTest/Unit/AreaTest.lean:5:8: declaration uses `sorry`
Some required targets logged failures:
- ShapeTest.Unit.AreaTest
error: build failed
```

主張を書いた時点で，主張に型が付くこと(定理として意味を持つこと)をLeanが確かめる．
主張に型が付かないときは，`sorry`の警告より先に，型のエラーが表示される．

### Green

テストを通す最小限の実装を書き，証明を完成させる．
最初は，そのテストだけを通す仮の実装でもよい．
次の`area`は，長方形の場合だけを正しく実装し，円の場合は`0`を返す．

```lean
def area : Shape → Nat
  | .circle _ => 0
  | .rect w h => w * h
```

円の面積を確かめるテストを次の項目で足せば，この仮の実装は失敗し，正しい実装が必要になる．
このように，テストを1つ足すたびに実装を一般にしていく．

一般の性質のテストでは，`sorry`を証明に置き換える．
実装が正しくても証明が書けない場合は，主張か実装のどちらかを見直す．
証明できないことが，誤りの手がかりになる．

### Refactor

テストがすべて通ったら，定理の主張を変えずに，定義と証明を読みやすく整理する．
整理した後も`lake test`が成功することを確かめる．

## テストリスト

各Iterationの最初に，要件と使用例から，確かめるべきことを`TESTLIST.md`に書き出す．

```markdown
## 単体テスト

### `Shape.Area`(`ShapeTest/Unit/AreaTest.lean`)

- [ ] 幅2，高さ3の長方形の面積は6である．
- [ ] 半径1の円の面積は3である．
- [ ] `area_rect_comm`：長方形の幅と高さを入れ替えても，面積は変わらない．
```

- 1つの項目には，1つの振る舞いか性質を書く．
- 一般の性質には，定理の名前を付ける．名前は言語仕様書の「性質」の名前と一致させる．
- 具体例から始め，一般の性質を後に置く．具体例を書くと，実装に必要な場合分けが見えてくる．
- 簡単な場合から始め，組み合わせた場合を後に置く．
- 既存のテストの期待値が変わるときは，「〜の期待値を〜に変える」という項目を足す．
- 項目を実装し終えたら，`- [x]`にする．

進めるうちに確かめたいことを思い付いたら，その場でリストに足す．

## 単体テストと統合テスト

テストは単体テストと統合テストに分ける．

| 種類 | 確かめること | 置き場所 |
| --- | --- | --- |
| 単体テスト | 1つのモジュールの定義の性質．評価器が意味論に従うこと，簡約の決定性など | `MiniTest/Unit/<モジュール名>Test.lean` |
| 統合テスト | 構文解析・型検査・評価をつないだ`Mini.Run`の関数の性質．文字列を入力にした具体例など | `MiniTest/Integration/RunTest.lean` |

テストファイルはモジュールごとに1つ作り，モジュールがある限り使い続ける．
機能を変えたIterationでは，同じファイルにテストを足すか，期待値を書き換える．

新しいテストファイルは，入口のファイルにimportを足して登録する．
単体テストは`MiniTest/Unit.lean`に，統合テストは`MiniTest/Integration.lean`に登録する．

```lean
import MiniTest.Unit.AreaTest
```

文字列を入力にした具体例は，`decide`ではなく`decide +kernel`で証明する．
構文解析の計算が長いため，`decide`ではメモリを使い果たすことがある．

## テストの実行

パッケージのディレクトリで，次のコマンドを実行する．

| 操作 | コマンド |
| --- | --- |
| すべてのテスト | `lake test` |
| 単体テストだけ | `lake build MiniTest.Unit` |
| 統合テストだけ | `lake build MiniTest.Integration` |
| 1つのテストファイルだけ | `lake build MiniTest.Unit.EvalTest` |

エディタでテストファイルを開いている間は，保存するたびにLeanがそのファイルを検査し，失敗をInfoviewに表示する．
