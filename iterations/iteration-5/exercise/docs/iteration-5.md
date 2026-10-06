# Iteration 5 変数と`let`

このIterationでは，Miniに変数と`let x = t in u`を足す．
`t`を値まで評価してから，`u`の中の`x`をその値で置き換える．
置換が型を保つこと(置換補題)を証明し，評価器を燃料つきの形に作り直す．

## 5-1 準備

このパッケージは，Iteration 4の解答と同じ状態から始まる．

``` sh
cd iterations/iteration-5/exercise
lake build
lake test
```

Iteration 4までのテストがすべて通ることを確かめる．
`handout/Parser.lean`は，変数と`let`に対応した構文解析器である．

## 5-2 構文と概念

次の2つのノートを読む．

- [文字列と燃料](../../../docs/lean/iteration-5.md)
- [変数と置換](../../../docs/semantics/iteration-5.md)

読み終えたら，`Scratch.lean`で次の課題を試す．

1. ノートの`collatz`を書き写し，停止を示せないというエラーを確かめる．`collatzFuel`に直し，`#eval collatzFuel 100 27`を実行する．
2. `by_cases`を使って，`(if n = 5 then n else 5) = 5`を証明する．
3. 紙の上で，$(\mathsf{let}\ x = x + 1\ \mathsf{in}\ x * y)[x := 3]$を計算する．

## 5-3 テストリスト

### 要件

- 変数と`let x = t in u`を足す．`t`を値まで評価してから，`u`の中の`x`をその値で置き換える．
- 束縛されていない変数を含む式は型エラーにする．
- 評価のステップ数に上限(燃料)を設け，`--fuel`で変えられるようにする．

### 使用例

```text
$ lake exe mini eval "let x = 1 + 2 in x * x"
9
$ lake exe mini check "let x = 1 in y"
型エラー：変数yが定義されていない
$ lake exe mini eval --fuel 2 "1 + 2 + 3"
燃料切れ：2ステップで評価が終わらなかった
```

### 作るもの

| モジュール | 定義 | 内容 |
| --- | --- | --- |
| `Mini.Syntax` | `Term`の構成子`var (x : String)`，`let_ (x : String) (t u : Term)` | 新しい構文 |
| | `def Term.toValue? : Term → Option Value` | 式が値を表すなら，その値を返す |
| `Mini.Subst`(新規) | `def subst (x : String) (v t : Term) : Term` | 置換$t[x := v]$ |
| `Mini.SmallStep` | `inductive IsValue : Term → Prop`(構成子`num`，`tru`，`fls`) | 値を表す式 |
| `Mini.Typing` | `abbrev Ctx := List (String × Ty)`と`def Ctx.lookup` | 型付け文脈 |
| | `HasType : Ctx → Term → Ty → Prop`，`typeOf : Ctx → Term → Except TypeError Ty` | 文脈つきの型付け |
| | `TypeError`の構成子`unbound (x : String)` | 定義されていない変数 |
| `Mini.Eval` | `inductive EvalError`(構成子`stuck (t : Term)`，`outOfFuel`) | 評価が値に着かなかった理由 |
| | `eval : Nat → Term → Except EvalError Value` | 燃料の回数まで`step`を繰り返す評価器 |
| `Mini.Run` | `run (s : String) (fuel : Nat := 1000)`，`runSteps`も同じ | 燃料の引数を足す |
| `Main` | オプション`--fuel <数>` | `eval`と`steps`に燃料を渡す |

### リファクタリング

`let`の本体に値を置換した式は，元の式の部分式ではない．
そのため，`eval`を式の構造についての再帰では定義できなくなる．
`eval`を，`step`を燃料の回数まで繰り返す関数として定義し直す．

### 課題

確かめるべきことを`TESTLIST.md`に書き出す．

- 置換の具体例を考える．`let`が同じ名前を束縛している場合と，別の名前を束縛している場合を分ける．
- `let`の評価，簡約，型付けの具体例を考える．内側の`let`が外側の束縛を隠す例も入れる．
- 燃料が足りない場合と足りる場合の具体例を考える．
- `eval`を作り直すと，既存のテストのどれが成り立たなくなるか，どう述べ直すかを考える．
  - Iteration 0の等価性の定理は，`eval`の等式のままで成り立つか．
  - 大ステップ意味論の決定性は，何から導けばよいか．
  - 「型の付く式は必ず値になる」は，燃料のある評価器について述べられるか．
- 型安全性の証明で，`let`の簡約の場合に何が必要になるかを考える．

## 5-4 設計書

- `design/spec.md`
  - `## 構文`：変数と`let`を足し，束縛と自由な変数の説明を書く．
  - 値を表す式`IsValue`の規則を書く．
  - `## 意味`：置換の定義を等式で書く．大ステップ意味論と小ステップ意味論に`let`の規則を足す．燃料つきの評価器の振る舞いを書く．
  - `## 型`：型付け文脈を説明し，型付け規則を文脈つきに書き直して，変数と`let`の規則を足す．
  - `## 性質`：述べ直した性質と，新しい性質(置換補題など)を書く．
- `design/modules.md`：新しいモジュール`Mini.Subst`を足す．どのモジュールが置換を使うかを考える．

## 5-5 テストファーストの実装

### 構文と構文解析器と置換

1. `Term`に構成子`var`と`let_`を足し，`handout/Parser.lean`で`Mini/Parser.lean`を置き換える．
2. `Mini/Subst.lean`を作ってライブラリに登録し，`MiniTest/Unit/SubstTest.lean`に具体例を書いてから`subst`を実装する．

次のヒントを参考にする．

- `let_ y t u`の場合，束縛する式`t`はいつも置き換え，本体`u`は`y`が`x`と異なるときだけ置き換える．

### 意味論

`Eval`，`Step`，`IsValue`に規則を足し，`BigStepTest`と`SmallStepTest`のテストを足す．

次のヒントを参考にする．

- `Step`の`let`の規則は，値を表す式であることを前提`IsValue v`にとる．前提を`Value`の値にすると，`cases`で導出を分解しにくくなる．
- `IsValue`，`Value.toTerm`，`Term.toValue?`の関係を補題にしておくと，後の証明で繰り返し使える．
- 大ステップ意味論の決定性は，導出についての帰納法を，もう一方の値を一般化して行う．

### 評価器

1. `EvalError`を定義し，`eval`を燃料つきの形に作り直す．
2. 既存のテストを，テストリストのとおりに述べ直す．
3. `eval`の健全性，完全性と，行き詰まりについての補題を証明する．

次のヒントを参考にする．

- `eval`の具体例は`rfl`で証明する．
- 健全性は，燃料についての帰納法で証明する．`step`の健全性と，Iteration 2の補題(1ステップ簡約した式の値は，簡約前の式の値でもある)を使う．
- 完全性は，大ステップ意味論から小ステップの簡約列を作り，その簡約列についての帰納法で示す．

### 型付け

`TypingTest`を文脈つきに書き直し，置換補題と型安全性を証明する．

次のヒントを参考にする．

- 弱化は，「文脈`Γ`の変数がすべて同じ型で文脈`Δ`にもある」という条件を仮定にとって，型付けの導出についての帰納法で証明する．
- 置換補題は，`u`についての帰納法を，文脈と型を一般化して行う．変数と`let`の場合は，`by_cases`で名前が等しいかどうかを分ける．
- 進行と保存は空の文脈の式について述べる．帰納法の前に`generalize`で空の文脈を変数にする．

### `run`と`--fuel`

統合テストを足して書き換えてから，`run`，`runSteps`，`Main.lean`を直す．
`run_well_typed`は，「値が表示されるか，燃料切れになる」と述べ直す．

最後に，使用例のとおりに表示されることを確かめる．
燃料を指定するときは`lake exe mini eval --fuel 2 "1 + 2 + 3"`のように，式の前にオプションを置く．

## 5-6 振り返り

1. 自分の`TESTLIST.md`を，`solution/TESTLIST.md`と比べる．述べ直した既存のテストの扱いはどう違ったか．
2. 置換する式を閉じた式に限った．どの定理の証明で，この制限が役立ったか．
3. 型の付く式の評価について，Iteration 4の`eval_of_hasType`より弱い主張にした．燃料のある評価器で，より強い主張を述べるには何が必要か．
4. 設計書と実装を見比べ，`mise run check-design`で`一致`になるまで設計書を直す．

## 5-7 発展課題

式の中に自由な変数`x`があるかを調べる関数`Term.hasFree : String → Term → Bool`を作る．
そのうえで，自由な`x`のない式に置換しても式が変わらないこと(`t.hasFree x = false → subst x v t = t`)を証明する．

これも，テストリスト，設計書，実装の順に進める．
