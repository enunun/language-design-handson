# Iteration 2 解説

演習の各手順の解説である．
見出しの番号は，演習の`docs/iteration-2.md`の手順に対応する．

## 2-1 準備

演習のパッケージはIteration 1の解答と同じなので，テストはすべて通る．

## 2-2 構文と概念

課題2の結果は`none`である．
`[]`の先頭はないので，`map`は関数を使わずに`none`を返す．
課題3の証明は`⟨3, rfl⟩`である．

## 2-3 テストリスト

模範解答は`TESTLIST.md`にある．

- `Step`の具体例では，使用例の簡約列の3つのステップを1つずつ確かめた．そのうえで，簡約できない例を1つ足し，左が数になる前は右を簡約しないことを確かめた．
- 性質として，数が正規形であること，決定性，大ステップ意味論との一致を挙げた．
- `step`については，Iteration 1の`eval`にならい，具体例と健全性・完全性を挙げた．
- `Term.pretty`では，かっこが要る場合と要らない場合を，結合の強さと結合の向きの両方について挙げた．
- 統合テストでは，使用例のほか，左結合の式，数だけの式，構文エラーを挙げた．

## 2-4 設計書

### 言語仕様書

- `## 意味`：`### 小ステップ意味論\`Step\``に9つの規則を書いた．演算子ごとに，左を簡約する規則(`addL`など)，右を簡約する規則(`addR`など)，計算する規則(`add`など)がある．右を簡約する規則の左辺の左の部分式を数$n_1$にして，評価の順序を表した．
- 計算する規則の結論の数は，横線の右に条件$n = n_1 + n_2$として書いた．
- `### 多ステップ簡約\`Steps\``に，`refl`と`step`の2つの規則を書いた．
- `## 性質`：`num_normal`，`step_deterministic`，`bigstep_iff_steps`，`step_sound`，`step_complete`を足した．

### モジュール依存図

- `Mini.SmallStep`は`Term`だけを使う仕様のモジュールなので，`Mini.Syntax`だけに依存する．
- `Mini.Pretty`も`Mini.Syntax`だけに依存する．`Mini.Run`が簡約列を表示するときに使う．
- `step`は`eval`と同じ`Mini.Eval`に置いた．どちらも式を計算する実装である．

## 2-5 テストファーストの実装

### `Mini.SmallStep`

#### 簡約の具体例

使用例の各ステップを，規則を組み合わせた導出で書いた．

```lean
example : Term.mul (.add (.num 1) (.num 2)) (.add (.num 3) (.num 4))
    ⟶ .mul (.num 3) (.add (.num 3) (.num 4)) :=
  Step.mulL Step.add
```

規則`mulL`と`add`を足すと，この例が通る．
`mulR`と`mul`を足すと，残りの2つの例が通る．
`+`と`-`の規則も同じ形で足した．

左が数になる前は右を簡約しないことを，`cases`で確かめる．
右辺の右の部分式が`.num 7`なので，`addL`(右の部分式が変わらない)も`addR`(左の部分式が数)も当てはまらない．

```lean
example : ¬ Term.add (.add (.num 1) (.num 2)) (.add (.num 3) (.num 4))
    ⟶ .add (.add (.num 1) (.num 2)) (.num 7) := by
  intro h
  cases h
```

#### `step_deterministic`

主張を書き，証明を`sorry`にして失敗を確かめた．

```text
error: MiniTest/Unit/SmallStepTest.lean:42:8: declaration uses `sorry`
```

`h₁`についての帰納法を`t₂`を一般化して行い，各場合で`h₂`を分解する．
`addL`と`addR`の組み合わせでは，`addR`の左の部分式が数なので，`addL`の前提`h`(数の簡約)を`cases`で分解すると矛盾する．

```lean
  induction h₁ generalizing t₂ with
  | addL h ih =>
    cases h₂ with
    | addL h' => rw [ih h']
    | addR _ => cases h
    | add => cases h
```

残りの8つの規則も同じ形である．

#### `bigstep_iff_steps`

まず多ステップ簡約の補題を証明した．
推移性`Steps.trans`と，部分式の簡約列を式全体の簡約列にする補題`Steps.addL`，`Steps.addR`などである．

```lean
theorem Steps.addL {t₁ t₁' t₂ : Term} (h : t₁ ⟶* t₁') : Term.add t₁ t₂ ⟶* .add t₁' t₂ := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.addL s) ih
```

右向きの`bigstep_steps`は，大ステップの導出についての帰納法で，左の簡約列，右の簡約列，最後の計算の1ステップをつなぐ．

```lean
  | add _ _ ih₁ ih₂ => exact Steps.trans (Steps.addL ih₁) (Steps.trans (Steps.addR ih₂) (Steps.single .add))
```

左向きでは，補題`step_bigstep`(1ステップ簡約した式の値は，簡約する前の式の値でもある)を先に示した．
`steps_bigstep`は，簡約列についての帰納法で`step_bigstep`を繰り返し使う．
簡約列の終わりが`Term.num n`という式なので，`generalize`で変数にしてから帰納法を使う．

```lean
theorem steps_bigstep {t : Term} {n : Nat} (h : t ⟶* .num n) : t ⇓ n := by
  generalize hu : Term.num n = u at h
  induction h with
  | refl => subst hu; exact .num
  | step s _ ih => exact step_bigstep s (ih hu)
```

### `step`

まず具体例を書き，`step`を実装した．

```lean
def step : Term → Option Term
  | .num _ => none
  | .add t₁ t₂ =>
    match t₁, t₂ with
    | .num n₁, .num n₂ => some (.num (n₁ + n₂))
    | .num n₁, t₂ => (step t₂).map (.add (.num n₁))
    | t₁, t₂ => (step t₁).map (.add · t₂)
```

`-`と`*`も同じ形である．
`match`は上の行から順に試すので，3行目の`t₁, t₂`は「左が数でない場合」になる．

#### `step_sound`

`simp only [step] at h`では`h`を展開できなかった．
入れ子の`match`のため，Leanが作る`step`の等式が，引数の形が具体的な場合だけになっているからである．
`unfold step at h`で定義そのものに置き換え，`split at h`で`match`の場合に分けた．

```lean
  | add t₁ t₂ ih₁ ih₂ =>
    unfold step at h
    split at h
    · cases h; exact .add
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .addR (ih₂ hu)
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨u, hu, rfl⟩ := h
      exact .addL (ih₁ hu)
```

#### `step_complete`

導出についての帰納法で証明した．
`addL`の場合，前提`s : t₁ ⟶ t₁'`を`cases`で分解すると，`t₁`が`add`，`sub`，`mul`のどれかの形に決まる．
すると`step`の`match`の場合が決まり，`simp_all [step]`で計算できる．

```lean
  | addL s ih => cases s <;> simp_all [step]
```

### `Term.pretty`

結合の強さ`p`の位置に置く式を文字列にする`Term.prettyPrec`を作り，`Term.pretty`は強さ`0`の位置から始めた．

```lean
def Term.prettyPrec : Nat → Term → String
  | _, .num n => toString n
  | p, .add t₁ t₂ => parenIf (p > 1) s!"{prettyPrec 1 t₁} + {prettyPrec 2 t₂}"
  | p, .sub t₁ t₂ => parenIf (p > 1) s!"{prettyPrec 1 t₁} - {prettyPrec 2 t₂}"
  | p, .mul t₁ t₂ => parenIf (p > 2) s!"{prettyPrec 2 t₁} * {prettyPrec 3 t₂}"
```

`+`の右の部分式を強さ`2`の位置に置くので，`10 - (2 - 3)`の右には，かっこが付く．

### `runSteps`と`mini steps`

統合テストを書くと，仮に`""`を返す`runSteps`では次のように失敗する．

```text
error: MiniTest/Integration/RunTest.lean:37:2: Tactic `decide` proved that the proposition
  runSteps "(1 + 2) * (3 + 4)" = "(1 + 2) * (3 + 4)\n⟶ 3 * (3 + 4)\n⟶ 3 * 7\n⟶ 21"
is false
```

`step`を燃料の回数まで繰り返す`trace`と，式の演算子の数`Term.size`を`Mini.Run`に作り，`runSteps`で使った．
1ステップで演算子が1つ減るので，`Term.size`回の繰り返しで数に着く．

```text
$ lake exe mini steps "(1 + 2) * (3 + 4)"
(1 + 2) * (3 + 4)
⟶ 3 * (3 + 4)
⟶ 3 * 7
⟶ 21
```

## 2-6 振り返り

1. 簡約の具体例では，簡約しない例(否定の例)も足しておくと，評価の順序を確かめられる．
2. `addR`の左の部分式が数$n_1$に限られているので，左が数でない式には`addL`しか当てはまらない．`addR`の左を任意の式にすると，$(1 + 2) + (3 + 4)$は左と右のどちらからも簡約でき，決定性が成り立たなくなる．
3. `eval_sound`と`eval_complete`で`eval`と大ステップ意味論が，`bigstep_iff_steps`で2つの意味論が，`step_sound`と`step_complete`で`step`と小ステップ意味論が一致する．したがって，`eval`が返す値と，`step`を繰り返して着く数は同じになる．
4. 模範解答の設計書は，`mise run check-design`で`一致`になる．

## 2-7 発展課題

`StepR`でも，決定性と大ステップ意味論との一致が成り立つ．
規則は，右の部分式を先に簡約し，右が数になったら左を簡約する形になる．
決定性は，規則の左辺が重ならないことから従う．
大ステップ意味論との一致は，この言語の式の評価に副作用がなく，どちらの部分式を先に評価しても値が変わらないことから従う．
Iteration 3で`if`を足すと，評価の順序が結果を左右する例が現れる．
