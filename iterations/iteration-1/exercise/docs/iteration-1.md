# Iteration 1 大ステップ意味論と評価器の正しさ

このIterationでは，Miniの式の意味を，評価器とは別に推論規則で定める．
そして，Iteration 0で作った評価器`eval`が，その意味に従うことを証明する．
利用者から見える`mini`の振る舞いは変わらない．

## 1-1 準備

このパッケージは，Iteration 0の解答と同じ状態から始まる．
ディレクトリを移り，ビルドしてテストを実行する．
Iteration 0のテストがすべて通ることを確かめる．

``` sh
cd iterations/iteration-1/exercise
lake build
lake test
```

```text
✔ [8/10] Built MiniTest.Integration.RunTest (811ms)
✔ [9/10] Built MiniTest.Integration (458ms)
✔ [10/10] Built MiniTest (326ms)
```

`lake exe mini eval "(1 + 2) * 3"`を実行し，`9`が表示されることも確かめる．

## 1-2 構文と概念

次の2つのノートを読む．

- [帰納的述語と帰納法](../../../docs/lean/iteration-1.md)
- [推論規則と大ステップ意味論](../../../docs/semantics/iteration-1.md)

読み終えたら，`Scratch.lean`で次の課題を試す．

1. ノートの`SumOf`と`total`を書き写し，`SumOf [1, 2, 3] 6`を構成子の組み合わせで証明する．
2. `total_sound`と`total_complete`を書き写し，Infoviewで各場合のゴールと帰納法の仮定を確かめる．
3. `¬ SumOf [] 1`を証明する．

## 1-3 テストリスト

### 要件

- 言語の意味を，評価器とは別に，大ステップ意味論の推論規則で定める．
- 評価器が大ステップ意味論に従うことを示す．
- 利用者から見える振る舞いは変わらない．

### 使用例

Iteration 0と同じ結果になる．

```text
$ lake exe mini eval "(1 + 2) * 3"
9
```

### 作るもの

| モジュール | 定義 | 内容 |
| --- | --- | --- |
| `Mini.BigStep`(新規) | `inductive Eval : Term → Nat → Prop`と記法`t ⇓ n` | 大ステップ意味論．構成子`num`，`add`，`sub`，`mul`は，`Term`の構成子と同じ名前にする |

### 課題

確かめるべきことを`TESTLIST.md`に書き出す．

- `Eval`の単体テストとして，いくつかの式の導出の例を考える．導出できない例も考える．
- `eval`と`Eval`の関係を表す性質を考える．評価器が返す値は意味論のうえでも正しいか．意味論で定まる値を評価器は返すか．
- 大ステップ意味論で，1つの式の値が1つに決まることも性質として挙げる．
- それぞれの性質のテストを，どのテストファイルに置くかを考える．
- 既存のテストの期待値で変わるものがあるかを確かめる．

## 1-4 設計書

- `design/spec.md`
  - `## 意味`：`eval`の等式を，大ステップ意味論`Eval`の推論規則に置き換える．見出しは`### 大ステップ意味論\`Eval\``の形にし，規則名を構成子の名前と一致させる．
  - `eval`が意味論とどう関係するかを，`## 意味`か`## 性質`に書く．
  - `## 性質`：テストリストの性質を足す．
- `design/modules.md`：新しいモジュール`Mini.BigStep`がどのモジュールをimportするかを考えて，図に足す．

書いたら`mise run lint`で数式と図の構文を確かめる．

## 1-5 テストファーストの実装

### `Mini.BigStep`

1. `Mini/BigStep.lean`を作り，`Mini.lean`に`import Mini.BigStep`を足して，モジュールをライブラリに登録する．
2. まず`Eval`を構成子なしで宣言し，`lake build Mini.BigStep`でこのモジュールだけをビルドできることを確かめる．
3. `MiniTest/Unit/BigStepTest.lean`を作って登録し，導出の例を1つずつ足しながら，`Eval`に規則を足していく．

次のヒントを参考にする．

- 規則`add`は，前提に部分式の導出を2つとり，結論の値を`n₁ + n₂`とする．
- 導出の例は，`Eval.add Eval.num Eval.num`のように構成子を組み合わせて書ける．
- 導出できない例では，結論の値を変数にした補題を`have`で示してから使う(ノートの`¬ SumOf [1] 2`を参照)．

### `Mini.Eval`の性質

`MiniTest/Unit/EvalTest.lean`に，`eval`と`Eval`の関係を表す定理を足す．
テストファイルの先頭に`import Mini.BigStep`が要る．

次のヒントを参考にする．

- 健全性は，`subst`で`n`を`eval t`に置き換えてから，`t`についての帰納法で証明する．
- 完全性は，導出`h`についての帰納法で証明する．各場合で`simp`に`eval`と帰納法の仮定を渡す．
- 決定性は，完全性を2回使うと短く証明できる．

## 1-6 振り返り

1. 自分の`TESTLIST.md`を，`solution/TESTLIST.md`と比べる．
2. 健全性だけを示し，完全性を示さなかったとする．評価器にどんな誤りがあっても見逃されるか．
3. 決定性を完全性から導いた．評価器がない言語では，決定性をどう証明すればよいか．
4. 設計書と実装を見比べ，`mise run check-design`で`一致`になるまで設計書を直す．

## 1-7 発展課題

式を簡単にする関数`simplify : Term → Term`を作る．
式の中のすべての`t * 1`を`t`に，`t + 0`を`t`に書き換える．
そのうえで，`simplify`が式の意味を変えないこと($t \Downarrow n$と$\mathit{simplify}(t) \Downarrow n$が同値であること)を証明する．

これも，テストリスト，設計書，実装の順に進める．
