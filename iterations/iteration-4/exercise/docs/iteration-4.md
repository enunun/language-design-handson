# Iteration 4 型と型検査器

このIterationでは，Miniに型`Nat`と`Bool`を導入し，式の型を評価の前に検査する．
型の付く式は決して行き詰まらないこと(型安全性)を証明する．

## 4-1 準備

このパッケージは，Iteration 3の解答と同じ状態から始まる．

``` sh
cd iterations/iteration-4/exercise
lake build
lake test
```

Iteration 3までのテストがすべて通ることを確かめる．
このIterationでは構文が変わらないので，構文解析器はそのまま使う．

## 4-2 構文と概念

次の2つのノートを読む．

- [失敗を返す関数と証明の組み立て](../../../docs/lean/iteration-4.md)
- [型システムと型安全性](../../../docs/semantics/iteration-4.md)

読み終えたら，`Scratch.lean`で次の課題を試す．

1. ノートの`safeDiv`を書き写し，`safeDiv 7 0 = .error "0で割った"`を`decide`と`rfl`で証明してみる．`decide`のエラーを確かめる．
2. `n = 0 ∨ n = 1`を仮定して`n < 2`を証明する．`rcases`で2つの場合に分ける．

## 4-3 テストリスト

### 要件

- 型`Nat`と`Bool`を導入し，式の型を検査して表示する．
- `eval`は評価の前に型を検査し，型の付かない式は評価しない．

### 使用例

```text
$ lake exe mini check "if iszero 0 then 1 else 2"
Nat
$ lake exe mini check "1 + true"
型エラー：+の右辺の型が合わない(期待：Nat，実際：Bool)
$ lake exe mini eval "1 + true"
型エラー：+の右辺の型が合わない(期待：Nat，実際：Bool)
```

### 作るもの

| モジュール | 定義 | 内容 |
| --- | --- | --- |
| `Mini.Syntax` | `inductive Ty`(構成子`nat`，`bool`) | 型 |
| `Mini.Typing`(新規) | `inductive HasType : Term → Ty → Prop` | 型付け規則．構成子の名前は`Term`の構成子と同じにする |
| | `inductive TypeError` | 型エラー．型が合わない位置と，期待した型と実際の型を持つ |
| | `def typeOf : Term → Except TypeError Ty` | 型検査器 |
| `Mini.Pretty` | `def Ty.pretty : Ty → String` | 型の表示(`Nat`，`Bool`) |
| `Mini.Run` | `run`，`def runCheck : String → String` | `run`は型を検査してから評価する．`runCheck`は型を表示する |
| `Main` | コマンド`mini check <式>` | `runCheck`の結果を表示する |

型エラーの表示は，`+の右辺の型が合わない(期待：Nat，実際：Bool)`の形にする．
`if`の2つの枝の型が異なるときは，`ifの2つの枝の型が合わない(then：Nat，else：Bool)`の形にする．

### 課題

確かめるべきことを`TESTLIST.md`に書き出す．

- 型付けの具体例と，型の付かない例を考える．評価すれば値になるのに型の付かない式はあるか．
- 型検査器の具体例を，型エラーの種類ごとに考える．
- 型検査器と型付け規則の関係を，評価器と大ステップ意味論の関係にならって考える．
- 型の付く式が行き詰まらないことを，小ステップ意味論で述べる．そのために必要な補題(進行と保存)も挙げる．
- 型の付く式を`eval`で評価すると，どうなるかを考える．
- 既存のテストのうち，期待値が変わるものを探す．

## 4-4 設計書

- `design/spec.md`
  - `## 型`を新しく立て，型のBNFと，型付け規則`### 型付け規則\`HasType\``を書く．`## 型`の下の規則名も`mise run check-design`で照合される．
  - 型検査器と型エラーについて，`## 型`に書く．
  - `## 性質`：テストリストの性質を足す．
- `design/modules.md`：新しいモジュール`Mini.Typing`を足す．どのモジュールが型検査器を使うかを考える．

## 4-5 テストファーストの実装

### 型付け規則と型検査器

1. `Ty`を`Mini/Syntax.lean`に足し，`Mini/Typing.lean`を作ってライブラリに登録する．
2. `MiniTest/Unit/TypingTest.lean`を作ってテストに登録し，具体例を足しながら`HasType`と`typeOf`を実装する．

次のヒントを参考にする．

- `typeOf`の`add`の場合は，`match typeOf t₁, typeOf t₂ with`で，両方が`.ok .nat`なら`.ok .nat`を返す．どちらかの型が違えば型エラーを，どちらかが型エラーならそのエラーを返す．
- `typeOf`の具体例は，`decide`ではなく`rfl`で証明する．
- 健全性は，`unfold typeOf at h`と`split at h`で場合を分ける．型エラーを返す場合は`contradiction`で閉じる．多くの場合が同じ形なので，`split at h <;> first | contradiction | …`とまとめられる．
- 型の一意性は，完全性を使うと短く証明できる．

### 型安全性

`TypingTest.lean`に，標準形補題，進行，保存，型安全性を足して証明する．

次のヒントを参考にする．

- 進行は，型付けの導出についての帰納法で証明する．部分式が値を表す式のときは，標準形補題で値の形を決める．
- 進行の主張の「値を表す式である」は，`∃ v : Value, t = v.toTerm`と書ける．`rcases ih with ⟨v, rfl⟩ | ⟨t', s⟩`で分解すると，`t`が`v.toTerm`に置き換わる．
- 保存は，型付けの導出についての帰納法を`t'`を一般化して行い，各場合で簡約の導出を`cases`で分解する．
- 型安全性は，簡約列についての帰納法で，進行と保存を組み合わせる．

### 型の付く式の評価

型の付く式を`eval`で評価すると必ず値になり，その値の型が式の型と同じであることを証明する．
値の型を返す関数`Value.ty`を`Mini.Typing`に足す．

### `run`と`mini check`

統合テストを書き換え，足してから，`run`，`runCheck`，`Main.lean`を実装する．
型エラーを文字列にする関数は`Mini.Run`に置く．

最後に，使用例のとおりに表示されることを確かめる．
単体テストだけを実行するときは`lake build MiniTest.Unit`，統合テストだけを実行するときは`lake build MiniTest.Integration`とする．

## 4-6 振り返り

1. 自分の`TESTLIST.md`を，`solution/TESTLIST.md`と比べる．
2. Iteration 3で実行時エラーになった式は，このIterationでどうなったか．実行時エラーは，もう起こりえないと言えるか．その根拠になる定理はどれか．
3. 型安全性を，大ステップ意味論ではなく小ステップ意味論で述べた．大ステップ意味論で「行き詰まらない」を述べようとすると，何が難しいか．
4. 設計書と実装を見比べ，`mise run check-design`で`一致`になるまで設計書を直す．

## 4-7 発展課題

`if`の型付け規則を緩め，`else`の枝の型を検査しない規則にしたとする．

```math
\frac{c : \mathsf{Bool} \quad t : T}{\mathsf{if}\ c\ \mathsf{then}\ t\ \mathsf{else}\ e : T}
```

この規則を持つ型付け規則をテストファイルの中で定義し，型安全性が成り立たないことを，反例を示して証明する．

これも，テストリスト，設計書，実装の順に進める．
