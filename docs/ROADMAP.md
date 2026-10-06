# ロードマップ

このハンズオンでは，小さな関数型言語Miniの処理系をLean 4で育てる．
Iterationごとに言語へ機能を足し，その意味を推論規則で定め，評価器と型検査器を実装する．
そして，実装が意味論に従うことと，言語が満たすべき性質を，Leanの定理として証明する．

## 完成したプログラム

``` text
$ lake exe mini eval "let double = fun (x : Nat) => x + x in double 21"
42
$ lake exe mini eval "(fix fact (n : Nat) : Nat => if iszero n then 1 else n * fact (n - 1)) 5"
120
$ lake exe mini check "fun (p : Nat × Bool) => if snd p then fst p else 0"
Nat × Bool → Nat
$ lake exe mini check "(fun (x : Nat) => x) true"
型エラー：関数の引数の型が合わない(期待：Nat，実際：Bool)
$ lake exe mini steps "(fun (x : Nat) => x + 1) 2"
(fun (x : Nat) => x + 1) 2
⟶ 2 + 1
⟶ 3
$ lake exe mini eval --fuel 1000 "(fix loop (n : Nat) : Nat => loop n) 0"
燃料切れ：1000ステップで評価が終わらなかった
```

## Iterationの進め方

各Iterationは`iterations/iteration-N/`にあり，受講者は`exercise/`で作業する．
`exercise/`は前のIterationの`solution/`と同じ状態から始まる．
`solution/`は完成した演習と模範解答である．

どのIterationも，次の順に進める．

1. テストリスト：要件と使用例から，証明すべき性質と確かめる具体例を`TESTLIST.md`に書き出す．
2. 設計書：言語仕様書(構文と推論規則)とモジュール依存図を更新する．
3. テストファーストの実装：テストリストの項目を1つずつ，Red → Green → Refactorで進める．
4. 設計レビュー：設計書と実装を見比べ，食い違いを直す．

このハンズオンのテストは，すべてLeanの定理である．
定理の主張を書いて証明を`sorry`にした状態がRedで，`lake test`は失敗する．
定義を実装して証明を書き終えた状態がGreenである．
Refactorでは，定理の主張を変えずに定義や証明を整理する．

## テストの分け方

- 単体テスト：1つのモジュールの定義についての性質．評価器`eval`が大ステップ意味論に従うこと，簡約の決定性，型検査器`typeOf`が型付け規則に従うことなど．具体例も`example`として書く．`MiniTest/Unit/<モジュール名>Test.lean`に置く．
- 統合テスト：構文解析・型検査・評価をつないだ関数`run`の性質．`run "1 + 2"`の結果の具体例と，「型検査を通ったプログラムの評価は行き詰まらない」のような一般の性質を書く．`MiniTest/Integration/RunTest.lean`に置く．

## Iterationの一覧

| Iteration | 作る機能 | 学ぶこと |
| --- | --- | --- |
| 0 | 自然数の四則(`+`，`-`，`*`)と評価器 | Leanの帰納型・関数・定理，評価器が与える意味，プログラムの等価性 |
| 1 | 大ステップ意味論と評価器の正しさ | 推論規則，帰納的述語，構造帰納法，評価器の健全性と完全性 |
| 2 | 簡約列の表示(`steps`) | 小ステップ意味論，決定性，2つの意味論の一致 |
| 3 | 真偽値，`if`，`iszero` | 値の種類，行き詰まった項，評価戦略の設計判断 |
| 4 | 型と型検査器(`check`) | 型付け規則，進行と保存，型安全性，型検査器の健全性と完全性 |
| 5 | 変数と`let` | 自由変数と置換，型付け文脈，置換補題，燃料つき評価器 |
| 6 | 関数と関数適用 | 単純型付きラムダ計算，値呼び，関数型 |
| 7 | 再帰(`fix`) | 停止しない評価，燃料切れ，型安全性と停止性の違い |
| 8 | 組(`(t, u)`，`fst`，`snd`) | 推論規則を自分で設計し，既存の性質が保たれることを確かめる |

## Iteration 0 自然数の四則と評価器

### 要件

- 自然数，`+`，`-`，`*`，かっこからなる式を評価し，結果の自然数を表示する．
- `-`は自然数の引き算で，結果が負になるときは`0`とする．
- `*`は`+`と`-`より強く結合し，同じ強さの演算子は左から結合する．

### 使用例

``` text
$ lake exe mini eval "1 + 2 * 3"
7
$ lake exe mini eval "(1 + 2) * 3"
9
$ lake exe mini eval "2 - 5"
0
$ lake exe mini eval "1 +"
構文エラー：式が途中で終わっている
```

### モジュール

- `Mini/Syntax.lean`：`inductive Term`(構成子`num (n : Nat)`，`add`，`sub`，`mul`)．
- `Mini/Eval.lean`：評価器`def eval : Term → Nat`．
- `Mini/Parser.lean`(配布)：`def parse : String → Except String Term`．
- `Mini/Run.lean`：`def run : String → String`．構文解析して評価し，表示する文字列を返す．
- `Main.lean`：コマンド`mini eval <式>`．

### 設計書の更新

- 言語仕様書：最初の版を書く．構文(BNF)と，各演算子の意味を表す等式(`eval (t₁ + t₂) = eval t₁ + eval t₂`など)，成り立つべき性質の一覧．
- モジュール依存図：最初の版を書く．`Syntax`，`Eval`，`Parser`，`Run`，`Main`の依存．

### 学ぶこと

- Lean：`inductive`，パターンマッチによる`def`，`#eval`，`theorem`と`example`，`by`による証明，`rfl`，`decide`，`rw`，`simp`，`Nat`の補題(`Nat.add_comm`など)の探し方，`¬`と反例．
- 意味論：抽象構文と具体構文，BNF，評価器が与える意味，プログラムの等価性．
- 性質：評価の具体例．`+`と`*`の交換法則と結合法則．`t * 1`と`t`の等価性．`-`は結合法則を満たさないこと(反例の証明)．

### 既存のテストへの影響

最初のIterationなので，既存のテストはない．

### 受講者が行うツールの操作

- `lake build`，`lake test`，`lake exe mini eval "<式>"`を実行する．
- 新しいテストファイルを作り，`MiniTest/Unit.lean`または`MiniTest/Integration.lean`にimportを足す．
- 設計書の検査`mise run check-design`を実行する．

## Iteration 1 大ステップ意味論と評価器の正しさ

### 要件

- 言語の意味を，評価器とは別に，大ステップ意味論の推論規則で定める．
- 評価器が大ステップ意味論に従うことを示す．
- 利用者から見える振る舞いは変わらない．

### 使用例

Iteration 0と同じ結果になる．

``` text
$ lake exe mini eval "(1 + 2) * 3"
9
```

### モジュール

- `Mini/BigStep.lean`(新規)：大ステップ意味論`inductive Eval : Term → Nat → Prop`(記法`t ⇓ n`)．

### 設計書の更新

- 言語仕様書：大ステップ意味論の推論規則を足し，等式で書いた意味をそれに置き換える．評価器の健全性と完全性，決定性を性質の一覧に足す．
- モジュール依存図：`BigStep`を足す．

### 学ぶこと

- Lean：帰納的述語(`inductive … : Prop`)，`intro`，`exact`，`constructor`，`cases`．
  項の構造帰納法(`induction t`)と，導出に関する帰納法(`induction h`)．
- 意味論：推論規則と導出木，大ステップ意味論，仕様(関係)と実装(関数)の区別．
- 性質：評価器の健全性(`eval t = n → t ⇓ n`)，完全性(`t ⇓ n → eval t = n`)，大ステップ意味論の決定性．

### 既存のテストへの影響

既存のテストの主張は変わらない．

### 受講者が行うツールの操作

- `Mini/BigStep.lean`を作り，`Mini.lean`にimportを足す．
- 1つのモジュールだけをビルドする(`lake build Mini.BigStep`)．

## Iteration 2 簡約列の表示

### 要件

- 式を1ステップずつ簡約し，最初の式から結果までの列を表示する．
- 簡約は左の部分式から順に行う．

### 使用例

``` text
$ lake exe mini steps "(1 + 2) * (3 + 4)"
(1 + 2) * (3 + 4)
⟶ 3 * (3 + 4)
⟶ 3 * 7
⟶ 21
```

### モジュール

- `Mini/SmallStep.lean`(新規)：小ステップ意味論とその反射推移閉包．
  `inductive Step : Term → Term → Prop`(記法`t ⟶ t'`)と`Steps`(記法`t ⟶* t'`)．
- `Mini/Eval.lean`：1ステップ簡約する関数`def step : Term → Option Term`を足す．
- `Mini/Pretty.lean`(新規)：項を具体構文の文字列にする`def Term.pretty : Term → String`．
- `Mini/Run.lean`：`def runSteps : String → String`を足す．
- `Main.lean`：コマンド`mini steps <式>`を足す．

### 設計書の更新

- 言語仕様書：小ステップ意味論の推論規則と，その性質(決定性，2つの意味論の一致)を足す．
- モジュール依存図：`SmallStep`と`Pretty`を足す．

### 学ぶこと

- Lean：帰納法での`generalizing`と`generalize`，`Option`と`Option.map`，存在量化と`⟨_, _⟩`，`obtain`，`split`と`unfold`，`<;>`と`simp_all`．
- 意味論：小ステップ意味論，正規形，反射推移閉包．
- 性質：小ステップの決定性，`step`の健全性と完全性(`step t = some t' ↔ t ⟶ t'`)，`t ⇓ n ↔ t ⟶* num n`．

### 既存のテストへの影響

既存のテストの主張は変わらない．

### 受講者が行うツールの操作

- `Mini/SmallStep.lean`と`Mini/Pretty.lean`を作り，ライブラリに登録する．
- 作ったモジュールだけをビルドして，型が付くことを確かめる．

## Iteration 3 真偽値と条件分岐

### 要件

- 真偽値`true`と`false`，条件式`if c then t else e`，自然数が`0`かを調べる`iszero t`を足す．
- 評価結果は自然数か真偽値になる．
- `1 + true`のように演算できない式を評価すると，評価が行き詰まったことを表示する．

### 使用例

``` text
$ lake exe mini eval "if iszero (2 - 2) then 10 else 20"
10
$ lake exe mini eval "1 + true"
実行時エラー：評価が行き詰まった(1 + true)
```

### モジュール

- `Mini/Syntax.lean`：構成子`tru`，`fls`，`ite`，`iszero`を足す．値を表す`inductive Value`(`num`，`bool`)を足す．
- `Mini/BigStep.lean`：`Eval : Term → Value → Prop`に変える．
- `Mini/Eval.lean`：`eval : Term → Option Value`に変える．

### リファクタリング

評価結果を`Nat`から`Value`に変える．`eval`は行き詰まると`none`を返す．

### 設計書の更新

- 言語仕様書：構文，値，推論規則を足す．行き詰まった項の定義を足す．
- モジュール依存図：依存関係は変わらない．`Value`の置き場所を書き足す．

### 学ぶこと

- Lean：複数の値についての`match`，`Bool`と`==`，`rcases`のパターン，`≠`，名前付き引数．
- 意味論：値，行き詰まった項，評価戦略．
- 性質：`if`の枝を先に簡約する規則を足すと決定性が崩れること(反例の証明)．

### 既存のテストへの影響

- `eval`の具体例の期待値を`n`から`some (.num n)`に変える．
- 健全性，完全性，2つの意味論の一致の主張を，`Value`を使う形に変える．

### 受講者が行うツールの操作

- 配布された新しい`Parser.lean`で，`Mini/Parser.lean`を置き換える．

## Iteration 4 型と型検査器

### 要件

- 型`Nat`と`Bool`を導入し，式の型を検査して表示する．
- `eval`は評価の前に型を検査し，型の付かない式は評価しない．

### 使用例

``` text
$ lake exe mini check "if iszero 0 then 1 else 2"
Nat
$ lake exe mini check "1 + true"
型エラー：+の右辺の型が合わない(期待：Nat，実際：Bool)
$ lake exe mini eval "1 + true"
型エラー：+の右辺の型が合わない(期待：Nat，実際：Bool)
```

### モジュール

- `Mini/Syntax.lean`：`inductive Ty`(`nat`，`bool`)を足す．
- `Mini/Typing.lean`(新規)：型付け規則と型検査器．
  `inductive HasType : Term → Ty → Prop`と`def typeOf : Term → Except TypeError Ty`．
- `Mini/Run.lean`：`run`で型検査してから評価する．`def runCheck : String → String`を足す．
- `Main.lean`：コマンド`mini check <式>`を足す．

### 設計書の更新

- 言語仕様書：型の構文と型付け規則，型安全性の定理を足す．
- モジュール依存図：`Typing`を足し，`Run`から`Typing`への依存を足す．

### 学ぶこと

- Lean：`Except`と`rfl`による具体例，`Or`と`.inl`・`.inr`，`rcases`による`Or`と`∃`の分解，`first`と`all_goals`，等式の`symm`と`trans`．
- 意味論：型付け規則，標準形補題，進行と保存．
- 性質：`typeOf`の健全性と完全性，型の一意性，進行，保存，型安全性(型の付く項は行き詰まらない)．統合テストとして「型検査を通ったプログラムを`run`しても実行時エラーにならない」．

### 既存のテストへの影響

- `run "1 + true"`の期待値を，実行時エラーから型エラーに変える．

### 受講者が行うツールの操作

- 単体テストだけ，統合テストだけを実行する．

## Iteration 5 変数と`let`

### 要件

- 変数と`let x = t in u`を足す．`t`を値まで評価してから，`u`の中の`x`をその値で置き換える．
- 束縛されていない変数を含む式は型エラーにする．
- 評価のステップ数に上限(燃料)を設け，`--fuel`で変えられるようにする．

### 使用例

``` text
$ lake exe mini eval "let x = 1 + 2 in x * x"
9
$ lake exe mini check "let x = 1 in y"
型エラー：変数yが定義されていない
$ lake exe mini eval --fuel 2 "1 + 2 + 3"
燃料切れ：2ステップで評価が終わらなかった
```

### モジュール

- `Mini/Syntax.lean`：構成子`var (x : String)`と`let_ (x : String) (t u : Term)`を足す．式が値を表すならその値を返す`Term.toValue?`を足す．
- `Mini/Subst.lean`(新規)：置換$t[x := v]$．
  `def subst (x : String) (v t : Term) : Term`．
- `Mini/SmallStep.lean`：値を表す式`IsValue`と，`let`の規則を足す．
- `Mini/Typing.lean`：型付け文脈`Ctx`を足し，`HasType : Ctx → Term → Ty → Prop`と`typeOf : Ctx → Term → Except TypeError Ty`に変える．
- `Mini/Eval.lean`：`eval : Nat → Term → Except EvalError Value`に変える．第1引数は燃料である．
- `Mini/Run.lean`：`run`と`runSteps`に，燃料の引数(既定値`1000`)を足す．
- `Main.lean`：オプション`--fuel <数>`を足す．

### リファクタリング

置換した項は元の項より小さいとは限らないので，`eval`は項についての構造的な再帰で定義できなくなる．
`eval`を，`step`を燃料の回数まで繰り返す関数として定義し直す．
これに伴い，式の等価性の定理は大ステップ意味論で述べ直し，大ステップ意味論の決定性は導出についての帰納法で直接証明する．

### 設計書の更新

- 言語仕様書：変数，`let`，置換の定義，文脈つきの型付け規則，置換補題を足す．
- モジュール依存図：`Subst`を足す．

### 学ぶこと

- Lean：`String`の比較と`if`，`by_cases`，構造的な再帰で書けない関数と燃料，既定値を持つ引数，`generalize`した等式を使う帰納法．
- 意味論：自由変数，閉じた項，置換，型付け文脈，弱化と置換補題．
- 性質：置換補題，燃料つき評価器の健全性と完全性．
  健全性は`eval k t = .ok v → t ⇓ v`，完全性は`t ⇓ v → ∃ k, eval k t = .ok v`である．

### 既存のテストへの影響

- 型付けの定理を，文脈を引数にとる形か，空の文脈`[]`を使う形に変える．
- `eval`の具体例と性質に燃料の引数を足し，結果の型を`Except EvalError Value`に変える．
- 式の等価性の定理を，`eval`の等式から大ステップ意味論の同値に変え，`BigStepTest`に移す．
- `eval_deterministic`を，大ステップ意味論について直接証明する`bigstep_deterministic`に変える．
- `eval_of_hasType`(型の付く式は必ず値になる)を，燃料のある評価器について述べ直した`eval_not_stuck`(型の付く式の評価は行き詰まらない)に変える．
- `run "1 + x"`の期待値を，構文エラーから型エラーに変える．`x`が変数として読まれるからである．

### 受講者が行うツールの操作

- 配布された新しい`Parser.lean`で置き換える．
- `lake exe mini`にオプション`--fuel`を渡す．

## Iteration 6 関数と関数適用

### 要件

- 関数`fun (x : T) => t`と関数適用`t u`，関数型`T → U`を足す．
- 引数は値まで評価してから関数に渡す(値呼び)．

### 使用例

``` text
$ lake exe mini eval "let double = fun (x : Nat) => x + x in double 21"
42
$ lake exe mini check "fun (x : Nat) => iszero x"
Nat → Bool
$ lake exe mini steps "(fun (x : Nat) => x + 1) 2"
(fun (x : Nat) => x + 1) 2
⟶ 2 + 1
⟶ 3
```

### モジュール

- `Mini/Syntax.lean`：構成子`lam (x : String) (A : Ty) (t : Term)`と`app`，型`arrow`を足す．値に関数を足す．
- そのほかのモジュールに，関数と関数適用の場合を足す．

### 設計書の更新

- 言語仕様書：関数の構文と推論規則を足す．値呼びを選んだ理由を書く．
- モジュール依存図：依存関係は変わらない．

### 学ぶこと

- Lean：`split`が加えた名前のない仮定に`next`で名前を付ける，`trace_state`で証明の途中の状態を表示する．
- 意味論：単純型付きラムダ計算，β簡約，値呼びと名前呼び．
- 性質：関数を足しても，決定性，型安全性，評価器の健全性と完全性が保たれること．

### 既存のテストへの影響

- 型の表示の期待値に関数型が加わる．既存の定理の主張は変わらず，証明に関数の場合が加わる．

### 受講者が行うツールの操作

- 配布された新しい`Parser.lean`で置き換える．

## Iteration 7 再帰

### 要件

- 再帰関数`fix f (x : A) : B => t`を足す．`t`の中で`f`を自分自身として呼べる．
- 燃料を使い切ったら，評価が終わらなかったことを表示する．

### 使用例

``` text
$ lake exe mini eval "(fix fact (n : Nat) : Nat => if iszero n then 1 else n * fact (n - 1)) 5"
120
$ lake exe mini eval --fuel 1000 "(fix loop (n : Nat) : Nat => loop n) 0"
燃料切れ：1000ステップで評価が終わらなかった
```

### モジュール

- `Mini/Syntax.lean`：構成子`fix`を足す．
- そのほかのモジュールに，`fix`の場合を足す．

### 設計書の更新

- 言語仕様書：`fix`の構文と推論規則を足す．
- モジュール依存図：依存関係は変わらない．

### 学ぶこと

- Lean：`refine`と`?_`で導出を根から順に組み立てる，帰納法の前に`suffices`で主張を一般化する，`clear`．
- 意味論：一般再帰，停止しない評価，型安全性と停止性の違い．
- 性質：型安全性が保たれること．`loop`が値に評価されないこと(`¬ ∃ v, t ⇓ v`)．

### 既存のテストへの影響

- 関数型の標準形補題`canonical_arrow`の主張が，「関数型を持つ値は関数か再帰関数である」に変わる．
- そのほかの既存の定理の主張は変わらず，証明に`fix`の場合が加わる．

### 受講者が行うツールの操作

- 配布された新しい`Parser.lean`で置き換える．

## Iteration 8 組

### 要件

- 組`(t, u)`，射影`fst t`と`snd t`，型`A × B`を足す．
- 評価と型付けの推論規則は，受講者が自分で設計する．

### 使用例

``` text
$ lake exe mini check "fun (p : Nat × Bool) => if snd p then fst p else 0"
Nat × Bool → Nat
$ lake exe mini eval "fst (1 + 2, true)"
3
```

### モジュール

- `Mini/Syntax.lean`：構成子`pair`，`fst`，`snd`と型`prod`を足す．値に組を足す．
- そのほかのモジュールに，組の場合を足す．

### 設計書の更新

- 言語仕様書：組の構文と推論規則を，受講者が設計して足す．組の成分をいつ評価するかの判断と理由を書く．
- モジュール依存図：依存関係は変わらない．

### 学ぶこと

- 意味論：推論規則の設計，設計の選択が性質に与える影響．
- 性質：自分で設計した規則のもとで，決定性，型安全性，評価器の健全性と完全性が成り立つこと．

### 既存のテストへの影響

既存の定理の主張は変わらず，証明に組の場合が加わる．

### 受講者が行うツールの操作

- 配布された新しい`Parser.lean`で置き換える．
