# Iteration 8 解説

演習の各手順の解説である．
見出しの番号は，演習の`docs/iteration-8.md`の手順に対応する．

## 8-1 準備

演習のパッケージはIteration 7の解答と同じなので，テストはすべて通る．

## 8-2 構文と概念

課題2は，先行評価なら3ステップで値になる．
完成した`mini steps`で確かめられる．

```text
$ lake exe mini steps "fst (1 + 2, iszero 0)"
fst (1 + 2, iszero 0)
⟶ fst (3, iszero 0)
⟶ fst (3, true)
⟶ 3
```

遅延評価なら，$\mathsf{fst}\ (1 + 2, \mathsf{iszero}\ 0) \longrightarrow 1 + 2 \longrightarrow 3$の2ステップで値になる．
使わない成分$\mathsf{iszero}\ 0$は評価しない．

課題3では，先行評価なら`Value`の組は値の組`pair (v w : Value)`になる．
遅延評価なら，成分は評価していない式なので`pair (t u : Term)`になる．

## 8-3 テストリスト

模範解答は`TESTLIST.md`にある．
模範解答は，組の成分を左から順に値まで評価する設計(先行評価)を選んだ．

- 組の評価，簡約，型付けの具体例を挙げた．使わない成分も評価することは，2つ目の成分に値がない`fst (1, 1 + true)`に値がないことで確かめた．
- 型エラーは，組でない式を射影する場合を挙げた．
- 既存の定理には，組と射影の場合を足した．値が再帰的になったので，値についての補題の証明を`cases`から帰納法に変えた．

## 8-4 設計書

### 言語仕様書

- `## 構文`に組と射影を，`## 値`に値の組を足した．値を表す式の規則`pair`は，2つの成分が値を表す式であることを前提にとる．
- 大ステップ意味論に`pair`，`fst`，`snd`の規則を足した．
- 小ステップ意味論に`pairL`，`pairR`，`fst`，`fstPair`，`snd`，`sndPair`の規則を足した．
- 先行評価を選んだ理由を書いた．1つ目は，関数適用の値呼びと揃うことである．2つ目は，置換に使う式が閉じた値を表す式だけのままであることである．
- `## 型`に組の型と，`pair`，`fst`，`snd`の型付け規則を足した．

### モジュール依存図

依存の矢印は変わらない．
`Mini.Pretty`の説明に，組の値の表示を書き足した．

## 8-5 テストファーストの実装

### 構文と構文解析器

構成子を足して構文解析器を置き換えると，場合の足りない定義がエラーになる．

```text
error: Mini/Subst.lean:16:2: Missing cases:
error: Mini/Typing.lean:54:2: Missing cases:
error: Mini/Pretty.lean:17:2: Missing cases:
error: Mini/Pretty.lean:29:2: Missing cases:
error: Mini/Pretty.lean:50:2: Missing cases:
```

`Value`が値の組を持つので，`Term.toValue?`は2つの成分を再帰的に調べる．

```lean
  | .pair t u =>
    match t.toValue?, u.toValue? with
    | some v, some w => some (.pair v w)
    | _, _ => none
```

### 意味論と評価器

小ステップ意味論の規則は次のとおりである．
`pairR`の前提`IsValue v`が，左の成分から簡約することを表す．

```lean
  | pairL {t t' u : Term} : Step t t' → Step (.pair t u) (.pair t' u)
  | pairR {v u u' : Term} : IsValue v → Step u u' → Step (.pair v u) (.pair v u')
  | fst {t t' : Term} : Step t t' → Step (.fst t) (.fst t')
  | fstPair {v w : Term} : IsValue v → IsValue w → Step (.fst (.pair v w)) v
```

値についての補題は，`cases`を`induction`に変えた．
`value_normal`では，組の場合に，成分についての帰納法の仮定を使う．

```lean
theorem value_normal (v : Value) : Normal v.toTerm := by
  induction v with
  | num n => intro t h; cases h
  | bool b => intro t h; cases b <;> cases h
  | lam x A t => intro t' h; cases h
  | fix f x A B t => intro t' h; cases h
  | pair v w ihv ihw =>
    intro t h
    cases h with
    | pairL h => exact ihv _ h
    | pairR _ h => exact ihw _ h
```

`isValue_exists_value`も，`IsValue`の導出についての帰納法にした．

```lean
  | pair _ _ ih₁ ih₂ =>
    obtain ⟨v, rfl⟩ := ih₁
    obtain ⟨w, rfl⟩ := ih₂
    exact ⟨.pair v w, rfl⟩
```

`step_complete`は，値を表す式の場合を分けて計算する方法では通らなくなった．
`IsValue`の場合を分けると組が現れ，その`toValue?`が計算できないからである．
そこで，値を表す式を`isValue_exists_value`で`v.toTerm`の形にし，`toValue?_toTerm`で書き換えるように直した．

```lean
  | fstPair hv hw =>
    obtain ⟨v, rfl⟩ := isValue_exists_value hv
    obtain ⟨w, rfl⟩ := isValue_exists_value hw
    simp [step, Term.toValue?, toValue?_toTerm]
```

### 型付け

組の型の標準形補題を足した．

```lean
theorem canonical_prod {Γ : Ctx} {v : Value} {A B : Ty} (h : HasType Γ v.toTerm (.prod A B)) :
    ∃ v₁ v₂, v = .pair v₁ v₂ := by
```

進行の射影の場合は，射影する式が値なら，この補題で組の形にして`fstPair`を使う．
保存の`fstPair`の場合は，組の型付けを`cases`で分解し，1つ目の成分の型付けを返す．

```lean
  | fst h ih =>
    cases s with
    | fst s => exact .fst (ih s hΓ)
    | fstPair _ _ => cases h with | pair h₁ _ => exact h₁
```

### 表示と`run`

組の型の`×`は，強さを`1`として`→`より強く結合させ，右に結合させた．
組はいつもかっこで囲むので，成分にはかっこを付けない．

```text
$ lake exe mini check "fun (p : Nat × Bool) => if snd p then fst p else 0"
Nat × Bool → Nat
$ lake exe mini eval "fst (1 + 2, true)"
3
$ lake exe mini eval "let swap = fun (p : Nat × Bool) => (snd p, fst p) in swap (1, true)"
(true, 1)
$ lake exe mini check "fst 1"
型エラー：組でない式から成分を取り出している(型：Nat)
```

## 8-6 振り返り

1. 模範解答の`TESTLIST.md`は，先行評価の設計で確かめることを並べている．
2. 遅延評価を選んだ場合，値は再帰的にならないので，値についての補題は`cases`のまま証明できる．先行評価では，`Value`と`IsValue`が再帰的になるので，値についての補題に帰納法が要る．
3. `pairR`から前提`IsValue v`を落とすと，`(1 + 2, 3 + 4)`に`pairL`と`pairR`の両方が当てはまる．`step_deterministic`の証明が通らなくなる．`step`は1つの式しか返さないので，`step_complete`も成り立たなくなる．
4. 模範解答の設計書は，`mise run check-design`で`一致`になる．

## 8-7 発展課題

模範解答は先行評価を選んだので，遅延評価の射影の簡約を定義する．
$\mathsf{fst}\ (1, \mathit{loop}\ 0)$は，遅延評価では1ステップで$1$になる．
先行評価では，2つ目の成分$\mathit{loop}\ 0$を簡約し続けるので，式全体も自分自身にしか簡約されない．

```lean
/-- 組を遅延評価する簡約．組はいつでも値で，射影するときに成分を取り出す． -/
inductive StepLazy : Term → Term → Prop where
  | fst {t t' : Term} : StepLazy t t' → StepLazy (.fst t) (.fst t')
  | fstPair {t u : Term} : StepLazy (.fst (.pair t u)) t
  | snd {t t' : Term} : StepLazy t t' → StepLazy (.snd t) (.snd t')
  | sndPair {t u : Term} : StepLazy (.snd (.pair t u)) u

/-- `fst (1, loop 0)`． -/
def fstLoop : Term := .fst (.pair (.num 1) loopApp)

example : StepLazy fstLoop (.num 1) := .fstPair

example {t : Term} (h : fstLoop ⟶* t) : t = fstLoop := by
  suffices ∀ s, s ⟶* t → s = fstLoop → t = fstLoop from this _ h rfl
  clear h
  intro s hs
  induction hs with
  | refl => exact id
  | step h₁ _ ih =>
    intro heq
    subst heq
    exact ih (step_deterministic h₁ (Step.fst (Step.pairR IsValue.num (Step.betaFix IsValue.num))))
```

この式には型$\mathsf{Nat}$が付く．

```lean
example : HasType [] fstLoop .nat := .fst (.pair .num (.app (.fix (.app (.var rfl) (.var rfl))) .num))
```

Iteration 7の値呼びと名前呼びと同じく，型の付く式でも，設計の選択によって値に着くかどうかが変わる．
