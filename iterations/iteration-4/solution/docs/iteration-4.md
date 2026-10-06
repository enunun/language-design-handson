# Iteration 4 解説

演習の各手順の解説である．
見出しの番号は，演習の`docs/iteration-4.md`の手順に対応する．

## 4-1 準備

演習のパッケージはIteration 3の解答と同じなので，テストはすべて通る．

## 4-2 構文と概念

課題1では，`decide`は`Decidable`のインスタンスが見つからないというエラーになり，`rfl`は通る．
課題2は，`rcases h with rfl | rfl`の後，それぞれ`decide`で閉じる．

## 4-3 テストリスト

模範解答は`TESTLIST.md`にある．

- 型付けの具体例とともに，$1 + \mathsf{true}$と$\mathsf{if}\ \mathsf{true}\ \mathsf{then}\ 0\ \mathsf{else}\ \mathsf{false}$に型が付かないことを挙げた．後者は評価すれば値になる．
- 型検査器の具体例は，型エラーの3種類(演算子の引数，`if`の条件，`if`の枝)について挙げた．
- 型検査器の健全性と完全性，型の一意性を挙げた．
- 型安全性と，その証明に使う進行と保存を挙げた．
- 型の付く式の評価が必ず値になることを`eval_of_hasType`とし，統合テストの`run_well_typed`で使った．
- 既存のテストでは，Iteration 3で実行時エラーになった`run`の具体例の期待値が，型エラーに変わる．

## 4-4 設計書

### 言語仕様書

- `## 型`を新しく立て，型のBNFと`### 型付け規則\`HasType\``の8つの規則を書いた．規則名は`Term`の構成子と同じにした．
- 型検査器が型エラーで返す情報と，型を評価の前に検査することを書いた．
- `## 性質`：型検査器の健全性と完全性，型の一意性，進行，保存，型安全性，`eval_of_hasType`，`run_well_typed`を足し，`run_of_eval`の主張を直した．

### モジュール依存図

`Mini.Typing`は`Mini.Syntax`だけに依存する．
`Mini.Run`が型検査器を使うので，`Mini.Run`から`Mini.Typing`への矢印を足した．
`Ty`は`Mini.Syntax`に置いた．Iteration 6で，関数の構文が引数の型を持つからである．

## 4-5 テストファーストの実装

### 型付け規則と型検査器

`HasType`の規則は，`Term`の構成子ごとに1つである．

```lean
  | ite {c t e : Term} {T : Ty} :
      HasType c .bool → HasType t T → HasType e T → HasType (.ite c t e) T
```

`typeOf`は，部分式の型検査の結果で場合分けする．
`match`は上の行から試すので，2行目は「左が`Nat`で右が`Nat`でない」，3行目は「左が`Nat`でない」場合になる．

```lean
  | .add t₁ t₂ =>
    match typeOf t₁, typeOf t₂ with
    | .ok .nat, .ok .nat => .ok .nat
    | .ok .nat, .ok T₂ => .error (.mismatch "+の右辺" .nat T₂)
    | .ok T₁, .ok _ => .error (.mismatch "+の左辺" .nat T₁)
    | .error err, _ => .error err
    | _, .error err => .error err
```

健全性の証明では，型エラーを返す場合が多いので，`first`でまとめた．

```lean
  | add t₁ t₂ ih₁ ih₂ =>
    unfold typeOf at h
    split at h <;> first | contradiction | (next h₁ h₂ => cases h; exact .add (ih₁ h₁) (ih₂ h₂))
```

### 型安全性

#### 進行

主張を書き，`sorry`で失敗を確かめた．

```text
error: MiniTest/Unit/TypingTest.lean:107:8: declaration uses `sorry`
```

進行は，型付けの導出についての帰納法で証明した．
`add`の場合，左の部分式が値なら，標準形補題で数`n₁`に決まる．
右の部分式も値なら規則`add`で，そうでなければ`addR`で簡約できる．

```lean
  | @add t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨v₁, rfl⟩ | ⟨t₁', s₁⟩
    · obtain ⟨n₁, rfl⟩ := canonical_nat h₁
      rcases ih₂ with ⟨v₂, rfl⟩ | ⟨t₂', s₂⟩
      · obtain ⟨n₂, rfl⟩ := canonical_nat h₂
        exact .inr ⟨_, .add⟩
      · exact .inr ⟨_, .addR s₂⟩
    · exact .inr ⟨_, .addL s₁⟩
```

#### 保存

型付けの導出についての帰納法を`t'`を一般化して行い，簡約の規則で場合を分けた．
`if`の場合，`iteTrue`なら`then`の枝の型付け`ht`が，そのまま簡約後の式の型付けになる．

```lean
  | ite hc ht he ihc _ _ =>
    cases s with
    | iteTrue => exact ht
    | iteFalse => exact he
    | ite s => exact .ite (ihc s) ht he
```

#### 型安全性

簡約列についての帰納法で，0ステップの場合は進行を，1ステップ以上の場合は保存を使った．

```lean
theorem type_safety {t t' : Term} {T : Ty} (h : HasType t T) (s : t ⟶* t') : ¬ Stuck t' := by
  induction s with
  | refl =>
    intro ⟨hn, hv⟩
    rcases progress h with ⟨v, rfl⟩ | ⟨u, su⟩
    · exact hv v rfl
    · exact hn u su
  | step s₁ _ ih => exact ih (preservation h s₁)
```

### 型の付く式の評価

`eval_of_hasType`は，値の型も主張に含めて帰納法を使った．
`add`の場合，部分式の値の型は`Nat`なので，値は数である．
すると`eval`を計算できる．

### `run`と`mini check`

既存の統合テストの期待値を変えないまま`run`に型検査を足すと，次のように失敗する．

```text
error: MiniTest/Integration/RunTest.lean:33:62: Tactic `decide` proved that the proposition
  run "1 + true" = "実行時エラー：評価が行き詰まった(1 + true)"
is false
```

期待値を型エラーに変えた．
`run_well_typed`は，型検査器の健全性と`eval_of_hasType`から，評価が値を返すことを導いて証明した．

```lean
theorem run_well_typed {s : String} {t : Term} {T : Ty} (hp : parse s = .ok t) (ht : typeOf t = .ok T) :
    ∃ v : Value, run s = v.pretty := by
  obtain ⟨v, he, _⟩ := TypingTest.eval_of_hasType (TypingTest.typeOf_sound ht)
  exact ⟨v, run_of_eval hp ht he⟩
```

```text
$ lake exe mini check "if iszero 0 then 1 else 2"
Nat
$ lake exe mini check "1 + true"
型エラー：+の右辺の型が合わない(期待：Nat，実際：Bool)
```

## 4-6 振り返り

1. 型安全性の証明に必要な補題(標準形補題，進行，保存)を，テストリストの段階で挙げられたかを確かめる．
2. Iteration 3で実行時エラーになった式は，すべて型エラーになった．`run_well_typed`により，型検査を通った式を`run`しても実行時エラーにはならない．`run`の中の実行時エラーの場合は，型検査を通った式では使われない．
3. 大ステップ意味論では，行き詰まる式と評価の終わらない式は，どちらも「値がない」として区別できない．小ステップ意味論では，行き詰まりを「値でない正規形」として直接述べられる．
4. 模範解答の設計書は，`mise run check-design`で`一致`になる．`HasType`の規則名も照合される．

## 4-7 発展課題

緩い規則は，元の規則に`iteLoose`を足した帰納的述語として定義できる．

```lean
inductive HasTypeLoose : Term → Ty → Prop where
  | base {t : Term} {T : Ty} : HasType t T → HasTypeLoose t T
  | iteLoose {c t e : Term} {T : Ty} : HasType c .bool → HasType t T → HasTypeLoose (.ite c t e) T
  | add {t₁ t₂ : Term} : HasTypeLoose t₁ .nat → HasTypeLoose t₂ .nat → HasTypeLoose (.add t₁ t₂) .nat
```

$(\mathsf{if}\ \mathsf{false}\ \mathsf{then}\ 1\ \mathsf{else}\ \mathsf{true}) + 1$には型$\mathsf{Nat}$が付くが，1ステップで$\mathsf{true} + 1$に簡約されて行き詰まる．

```lean
theorem loose_unsafe : ¬ ∀ t t' T, HasTypeLoose t T → t ⟶* t' → ¬ Stuck t' := by
  intro h
  have ht : HasTypeLoose (.add (.ite .fls (.num 1) .tru) (.num 1)) .nat :=
    .add (.iteLoose .fls .num) (.base .num)
  have hs : Term.add (.ite .fls (.num 1) .tru) (.num 1) ⟶* .add .tru (.num 1) :=
    .step (.addL .iteFalse) .refl
  apply h _ _ _ ht hs
  constructor
  · intro t s
    cases s with
    | addL s => cases s
  · intro v hv
    cases v with
    | num n => cases hv
    | bool b => cases b <;> cases hv
```

この緩い規則では，保存が成り立たない．
`if`の式に付いた型が，`else`の枝に簡約した後の式には付かないからである．
