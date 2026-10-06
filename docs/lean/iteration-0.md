# Iteration 0 Leanの基礎

Iteration 0で使うLeanの構文とtacticを説明する．
例には，図形の面積を求める小さなプログラムを使う．
例のコードを1つのファイルに書き，エディタで開くと，結果を確かめられる．

## Leanのファイルとエディタ

Leanのファイルの拡張子は`.lean`である．
VSCodeでLeanのファイルを開くと，右側のInfoviewに，カーソル位置の情報(`#eval`の結果，証明の途中の状態，エラー)が表示される．
Infoviewが表示されないときは，コマンドパレットで「Lean 4: Infoview: Toggle Infoview」を実行する．

`t₁`のような添字や`→`，`¬`などの記号は，エディタで`t\1`，`\to`，`\not`と打ち，スペースを押すと入力できる．
`--`から行末まではコメントである．`/-! … -/`はモジュールの説明，`/-- … -/`は直後の定義の説明である．

## 帰納型`inductive`

`inductive`で，いくつかの形のどれかをとるデータ型を定義する．
次の`Shape`は，「半径`r`の円」か「幅`w`と高さ`h`の長方形」のどちらかである．
`circle`と`rect`を構成子という．

```lean
inductive Shape where
  | circle (r : Nat)
  | rect (w h : Nat)
  deriving Repr, DecidableEq
```

`Nat`は自然数(`0`，`1`，`2`，…)の型である．
`deriving Repr`は値を表示できるようにし，`deriving DecidableEq`は2つの値が等しいかを計算で判定できるようにする．

構成子は`Shape.rect 2 3`のように型名を付けて書く．
期待される型が`Shape`だとわかっている場所では，`.rect 2 3`と省略できる．

## パターンマッチによる関数の定義

`def`で関数を定義する．
構成子ごとに場合を分けて書く書き方を，パターンマッチという．

```lean
def area : Shape → Nat
  | .circle r => 3 * r * r
  | .rect w h => w * h
```

`Shape → Nat`は「`Shape`を受け取り`Nat`を返す関数」の型である．
`| .rect w h => w * h`は，「引数が`rect w h`の形なら，`w * h`を返す」と読む．
関数適用は`area (.rect 2 3)`のように，かっこを使わずに引数を並べて書く．

関数の定義の中で，同じ関数を部分の値に適用してもよい(再帰)．
Leanは，引数が構成子を1つずつはがしながら小さくなっていくことを確かめ，必ず停止すると判断する．

## `#eval`で値を見る

`#eval`は式を計算して，その結果をInfoviewに表示する．

```lean
#eval area (.rect 2 3)
#eval area (.circle 2)
#eval Shape.rect 2 3
#eval 2 - 5
```

結果は次のとおりである．

```text
6
12
Shape.rect 2 3
0
```

`Nat`の引き算は，引く数のほうが大きいとき`0`を返す．

端末で確かめるときは，パッケージのディレクトリで`lake env lean <ファイル>`を実行する．
`#eval`の結果とエラーが，端末に表示される．

## `namespace`と`open`

`namespace Mini … end Mini`の中で定義した`eval`の正式な名前は`Mini.eval`である．
別のファイルで`open Mini`と書くと，`Mini.`を省いて`eval`と書ける．

## 定理と証明

Leanでは，命題(真か偽かが決まる主張)も型であり，その型を持つ値が証明である．
`theorem 名前 : 命題 := 証明`で，名前の付いた定理を書く．
名前を付けない場合は`example : 命題 := 証明`と書く．

```lean
example : area (.rect 2 3) = 6 := by rfl
```

`by`の後には，証明を組み立てる命令(tactic)を書く．
Infoviewには，tacticを実行するたびに，残りの証明すべきこと(ゴール)が表示される．
ゴールがなくなれば，証明は完成である．

証明を後回しにするときは，証明の代わりに`sorry`と書く．
`sorry`を含む定理は，証明が終わっていないものとして警告が出る．
このハンズオンのパッケージは警告をエラーとして扱うので，`sorry`が残っていると`lake test`が失敗する．

## 計算で証明する：`rfl`と`decide`

`rfl`は，両辺を計算すると同じ値になる等式を証明する．
`decide`は，計算で真偽を判定できる命題を，実際に計算して証明する．

```lean
example : area (.rect 2 3) = 6 := by decide
example : area (.rect 2 3) = 7 := by decide
```

2つ目は偽なので，`decide`は次のエラーを出す．

```text
error: Tactic `decide` proved that the proposition
  area (Shape.rect 2 3) = 7
is false
```

文字列を入力にした計算(構文解析を含むもの)には，`decide +kernel`を使う．
`decide`と同じく計算で証明するが，計算をLeanのカーネルに任せるので，長い計算でも速く終わる．

## 等式を書き換えて証明する：`simp`，`rw`，`exact`

変数を含む等式は，計算だけでは証明できない．
定義を展開し，既にある定理を使って証明する．

```lean
theorem area_rect_comm (w h : Nat) : area (.rect w h) = area (.rect h w) := by
  simp only [area]
  exact Nat.mul_comm w h
```

定理の主張の`(w h : Nat)`は，「どんな自然数`w`と`h`についても」という意味である．

- `simp only [area]`は，ゴールの中の`area`を定義に従って展開する．ゴールは`w * h = h * w`になる．
- `exact Nat.mul_comm w h`は，ゴールとまったく同じ形の定理を当てはめて，証明を終える．

`simp only [area]`だけで止めると，Infoviewに残りのゴールが表示される．
そのままファイルを確かめると，次のエラーが出る．

```text
error: unsolved goals
w h : Nat
⊢ w * h = h * w
```

`⊢`の上の行は使える仮定，`⊢`の右が証明すべきことである．

`rw [定理]`は，定理の等式の左辺をゴールの中から探し，右辺に書き換える．
定義の名前を渡すと，その定義の等式で書き換える．

```lean
theorem area_rect_comm' (w h : Nat) : area (.rect w h) = area (.rect h w) := by
  rw [area, area, Nat.mul_comm]
```

書き換えた結果，両辺が同じになると，`rw`はゴールを自動的に閉じる．

`simp`(`only`なし)は，Leanが用意している多くの書き換え規則を使って，ゴールを簡単にする．
`simp [area]`のように，展開したい定義を足して使う．

## 定理を探す：`#check`と`exact?`

自然数の性質の多くは，`Nat.`で始まる名前の定理として用意されている．
`#check`で定理の主張を表示できる．

```lean
#check Nat.mul_comm
#check @Nat.add_zero
```

```text
Nat.mul_comm (n m : Nat) : n * m = m * n
Nat.add_zero : ∀ (n : Nat), n + 0 = n
```

名前がわからないときは，ゴールの位置で`exact?`と書くと，使える定理をLeanが探す．

```lean
theorem area_rect_one (w : Nat) : area (.rect w 1) = w := by
  simp only [area]
  exact?
```

Infoviewに，次の提案が表示される．
提案をクリックすると，`exact?`がその証明に置き換わる．

```text
Try this:
  [apply] exact Nat.mul_one w
```

## 否定と反例：`¬`，`intro`，`have`

`¬ P`は「`P`ではない」である．
Leanでは，`¬ P`は「`P`を仮定すると矛盾する」という意味である．

「すべての`w`と`h`について`P`が成り立つ」ことを否定するには，`P`が成り立たない例(反例)を1つ示せばよい．

```lean
theorem not_all_square : ¬ ∀ w h : Nat, area (.rect w h) = w * w := by
  intro h
  have h' := h 1 2
  simp [area] at h'
```

- `intro h`は，否定の中身「すべての`w`と`h`について…」を仮定`h`として受け取る．ゴールは矛盾(`False`)になる．
- `have h' := h 1 2`は，仮定`h`を`w = 1`，`h = 2`に当てはめた`area (.rect 1 2) = 1 * 1`を，新しい仮定`h'`として加える．
- `simp [area] at h'`は，仮定`h'`を計算して`2 = 1`にする．偽の仮定が得られたので，証明が終わる．

`∀`は「すべての」を表す記号で，`\forall`と打つと入力できる．

## 仮定を受け取る定理

定理の主張に，前提を引数として書ける．

```lean
theorem name {s : String} {t : Term} (h : parse s = .ok t) : … := by
  simp [run, h]
```

`(h : parse s = .ok t)`は，「`parse s = .ok t`が成り立つとき」という前提である．
証明の中では，前提を`h`という名前の仮定として使える．
`simp [run, h]`のように，仮定を`simp`に渡すと，その等式で書き換える．

`{s : String}`のように波かっこで書いた引数は，暗黙の引数である．
定理を使うときに書かなくても，Leanが`h`の型から推論する．

## `Except`と`match`

`Except String α`は，計算が成功したときは`.ok`に`α`の値を，失敗したときは`.error`にエラーの文字列を入れて返す型である．
構文解析器`parse`は`Except String Term`を返す．

`match`で，どちらの形かによって場合を分けられる．

```lean
match parse s with
| .ok t => …
| .error e => …
```

文字列の中に`{…}`で値を埋め込むには，`s!"…"`と書く．
`toString n`は，自然数`n`を文字列にする．
