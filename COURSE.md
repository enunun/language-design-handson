# コース計画

このファイルは，教材を作る人とエージェントのための計画である．
受講者向けの内容は`README.md`と`docs/ROADMAP.md`に書く．
各Iterationで何を作るかは`docs/ROADMAP.md`だけに従い，配置・コマンド・ツールなどの約束事はこのファイルだけに従う．

## 受講者と到達目標

- 受講者：実務でソフトウェアを開発している人．Python，TypeScript，Javaなどで開発し，単体テストを書いた経験がある．Leanと操作的意味論は初めてである．
- 到達目標：
  - 小さな言語を設計し，検証できる．新しい言語機能の構文・評価規則・型付け規則を定義し，型安全性などの性質をLeanで証明できる．
  - 論文や言語仕様にある推論規則を読み，何を定義しているかがわかる．
  - 評価戦略や型付け規則の選択肢を，性質が保たれるかどうかで比べられる．
  - 評価器や型検査器を実装し，それが意味論に従うことを証明できる．
- 学ぶ技術：Lean 4(v4.34.1)．Mathlibは使わず，Leanの標準ライブラリだけを使う．
- 教材の言語：日本語．である調で，読点は「，」，句点は「．」とする．識別子は英語にする．
- 分量：Iteration 0から8までの9回．1回あたり3〜4時間とする．

## 題材

受講者は，小さな関数型言語Miniの処理系を育てる．
完成した処理系には，式の評価(`eval`)，簡約列の表示(`steps`)，型検査(`check`)の3つのコマンドがある．
完成時の使用例は`docs/ROADMAP.md`の冒頭にある．

## テストの考え方

テストはすべてLeanの定理(`theorem`と`example`)である．

- Red：定理の主張を書き，証明を`sorry`にする．テストライブラリは警告をエラーとして扱うので，`lake test`は失敗する．具体例の`example`は，実装が誤っていれば`decide`が失敗する．
- Green：定義を実装し，証明を書き終える．
- Refactor：定理の主張を変えずに，定義と証明を整理する．

単体テストは1つのモジュールの定義についての性質で，`MiniTest/Unit/<モジュール名>Test.lean`に置く．
統合テストは`Mini.Run`の関数(構文解析・型検査・評価をつないだもの)の性質で，`MiniTest/Integration/RunTest.lean`に置く．
テストファイルはモジュールごとに1つで，モジュールがある限り残す．Iterationの名前をファイル名にしない．

## 設計書

受講者は，各パッケージの`design/`に次の2つを書く．

| ファイル | 内容 | 記法 | 育ち方 |
| --- | --- | --- | --- |
| `design/spec.md` | 言語仕様書．構文，意味(推論規則)，成り立つべき性質 | Markdownと数式(MathJax) | 構文・規則・性質がIterationごとに増える |
| `design/modules.md` | モジュール依存図．`Mini`の各モジュールと`Main`がどれをimportするか | Mermaidのflowchart | モジュールと依存の矢印が増える |

### 言語仕様書の約束

- 数式は，文中では`$…$`で，独立した式は数式のコードブロック(` ```math `)で書く．GitHubとMarkdown Preview Enhancedのどちらでも表示でき，textlintは数式のコードブロックを文章として検査しない．
- `## 構文`：BNFを数式のコードブロックで書く．
- `## 意味`：関係ごとに`### <説明>\`<Leanの名前>\``という見出しを立て，その下に推論規則を書く．
- `## 型`(Iteration 4から)：型の構文と，型付け規則を`## 意味`と同じ形で書く．
  推論規則は`\frac{前提}{結論}\ \textsf{<構成子名>}`の形で書く．
- `## 性質`：`- \`<定理名>\`：<主張の説明>`の形の箇条書き．
- Iteration 0は推論規則を使わず，`eval`の等式で意味を書く．Iteration 1で推論規則に置き換える．

### 設計書と実装の照合

`mise run check-design`が，次の3点を照合する．

- モジュール依存図の矢印と，`Mini/`と`Main.lean`のimport文．図にだけある矢印と，コードにだけあるimportを報告する．`Mini.lean`(ライブラリの入口)とLeanの標準ライブラリは照合から外す．
- 言語仕様書の`## 意味`と`## 型`にある`### …\`Name\``の節の規則名の集合と，`inductive Name`の構成子名の集合．
- 言語仕様書の`## 性質`に挙げた定理名が，`MiniTest/`に`theorem`として存在すること．

数式はMathJaxで，Mermaidの図はMermaidの構文解析器で検査する(`mise run lint`)．

## 開発環境

### Dev Container

- ベースイメージ：`jdxcode/mise:2026.9.12-debian`．
- Lean：elanで入れ，版はリポジトリ直下の`lean-toolchain`で固定する．各パッケージは親ディレクトリの`lean-toolchain`を使う．
- miseで入れるツール：Node.js，pnpm，lefthook，rtk．版は`mise.toml`と`mise.lock`で固定する．
- npmパッケージ：textlint，markdownlint-cli2，mermaid，jsdom，mathjax-full．版は`pnpm-lock.yaml`で固定する．
- エディタ拡張：
  - Lean 4(`leanprover.lean4`)：証明の途中の状態を見ながら書く．
  - Markdown Preview Enhanced(`shd101wyy.markdown-preview-enhanced`)：言語仕様書の数式をMathJaxで，依存図をMermaidで表示する．
  - markdownlint(`DavidAnson.vscode-markdownlint`)とtextlint(`3w36zj6.textlint`)：文書の検査．
  - Claude Code(`anthropic.claude-code`，`growthjack.claude-code-usage`)．

### 配置

``` text
COURSE.md                          コース計画(教材を作る人向け)
README.md                          コースの概要とIterationの一覧(受講者向け)
docs/ROADMAP.md                    Iterationごとの要件・学ぶこと・設計書の更新
docs/tdd.md                        定理によるテスト駆動開発とテストリストの書き方
docs/design.md                     設計書の書き方
docs/lean/iteration-N.md           Iteration Nで初めて使うLeanの構文とtactic
docs/semantics/iteration-N.md      Iteration Nで初めて扱う意味論の概念
scripts/                           教材の検査スクリプト
iterations/iteration-N/
  exercise/                        受講者が作業するパッケージ
  solution/                        完成した演習と模範解答
```

各パッケージの中身は次のとおりである．

``` text
README.md                このIterationで作るもの，進め方，ディレクトリ構成
TESTLIST.md              テストリスト(演習は雛形，解答は模範解答)
design/spec.md           言語仕様書
design/modules.md        モジュール依存図
docs/iteration-N.md      演習の手順(演習)，各手順の解説(解答)
lakefile.toml            パッケージ名はmini-iteration-N-exerciseとmini-iteration-N-solution
Mini.lean                ライブラリMiniの入口．各モジュールをimportする
Mini/<モジュール>.lean    言語の定義，評価器，型検査器など
Main.lean                コマンドmini
MiniTest.lean            テストの入口．MiniTest.UnitとMiniTest.Integrationをimportする
MiniTest/Unit.lean       単体テストの入口．各単体テストファイルをimportする
MiniTest/Unit/<モジュール>Test.lean
MiniTest/Integration.lean
MiniTest/Integration/RunTest.lean
handout/Parser.lean      演習だけにある，このIterationの構文に対応した構文解析器
```

`lakefile.toml`は次の形である．`Mini`と`MiniTest`はどちらも警告をエラーとして扱い，`sorry`を残したテストを失敗させる．

``` toml
name = "mini-iteration-N-solution"
defaultTargets = ["Mini", "mini"]
testDriver = "MiniTest"

[[lean_lib]]
name = "Mini"
leanOptions = { autoImplicit = false, warningAsError = true }

[[lean_lib]]
name = "MiniTest"
leanOptions = { autoImplicit = false, warningAsError = true }

[[lean_exe]]
name = "mini"
root = "Main"
```

### コマンド

受講者はパッケージのディレクトリで次を実行する．

| 操作 | コマンド |
| --- | --- |
| ビルド | `lake build` |
| テスト | `lake test` |
| 単体テストだけ | `lake build MiniTest.Unit` |
| 統合テストだけ | `lake build MiniTest.Integration` |
| 1つのモジュールだけビルド | `lake build Mini.Eval` |
| 実行 | `lake exe mini eval "1 + 2"` |
| 式の値をその場で見る | エディタで`#eval`を書く．端末では`lake env lean <ファイル>` |
| 設計書の照合 | `mise run check-design`(パッケージのディレクトリで実行すると，そのパッケージだけを照合する) |

リポジトリ全体の検証は`mise run check`で行う．
`lint`(textlint，markdownlint，Mermaid，数式)，`test`(全パッケージのビルドとテスト)，`check-design`，`check-exercises`をまとめて実行する．
`check-exercises`は，Iteration Nの演習がIteration N-1の解答と一致することを確かめる．
比較から外すのは`lakefile.toml`，`README.md`，`TESTLIST.md`，`docs/`，`handout/`，ビルド出力である．

### 受講者が行うツールの操作

| 操作 | 初めて全文を示すIteration |
| --- | --- |
| `lake build`，`lake test`，`lake exe mini eval "<式>"` | 0 |
| テストファイルを作り，`MiniTest/Unit.lean`または`MiniTest/Integration.lean`に登録する | 0 |
| `mise run check-design` | 0 |
| モジュールを作り，`Mini.lean`に登録する | 1 |
| 1つのモジュールだけをビルドする | 1 |
| `handout/Parser.lean`で`Mini/Parser.lean`を置き換える | 3 |
| 単体テストだけ，統合テストだけを実行する | 4 |
| `lake exe mini`にオプションを渡す | 5 |

### 構文解析器の配布

構文解析器は意味論とは別の話題なので，教材として配布する．
演習は前のIterationの解答と同じ状態から始まるので，新しい構文に対応した構文解析器は演習の`handout/Parser.lean`に置く．
受講者は`Term`に構成子を足した後で，それを`Mini/Parser.lean`にコピーする．
Iteration 0だけは，演習の`Mini/Parser.lean`に最初から入れておく．

構文解析器は燃料についての構造的な再帰で書き，カーネルで評価できるようにする(「落とし穴」を参照)．

## Iteration 0の演習の形

- `Mini/Syntax.lean`：`Term`の定義(完成している．構文解析器が使うため)．
- `Mini/Parser.lean`：配布する構文解析器(完成している)．
- `Mini/Eval.lean`：`def eval : Term → Nat := fun _ => 0`という仮の実装．
- `Mini/Run.lean`：`def run : String → String := fun _ => ""`という仮の実装．
- `Main.lean`：コマンド`mini eval <式>`(完成している)．
- `MiniTest.lean`，`MiniTest/Unit.lean`，`MiniTest/Integration.lean`：テストの入口だけ．テストファイルはない．
- `design/spec.md`と`design/modules.md`：見出しと，そこに書く内容を説明するコメントだけ．
- `TESTLIST.md`：単体テストと統合テストの見出しだけの雛形．

## 落とし穴

- 文字列を入力にした具体例を`decide`や`rfl`で証明すると，入力が少し長いだけでメモリを使い果たす．
  エラボレータの評価器が部分計算を共有しないためである．
  `run "1 + 2" = "3"`のような具体例は`decide +kernel`で証明する．
  `native_decide`はコンパイラを信頼する公理が加わるので使わない．
- `Except`には等しさを判定するインスタンスがないので，`typeOf t = .ok T`のような具体例は`decide`で証明できない(`failed to synthesize Decidable`になる)．`rfl`で証明する．
- テストファイルの名前空間(`MiniTest.…`)で`theorem Steps.trans`のように定義した補題は，`h.trans`のようなドット記法では呼べない．ドット記法は`Mini.Steps.trans`を探すからである．`Steps.trans h₁ h₂`のように名前で呼ぶ．
- `\textsf{let\_}`のように，TeXでは`_`を`\_`と書く．`check-design`は`\_`を`_`に戻してから構成子名と比べる．
- textlintは文中の数式も文章として検査する．`$u[x := v] : B$`のように，`]`の後に空白がある数式は「かっこの外側にスペースを入れない」規則に当たる．数式を分けて書く．
- `open Term`の後で`ite`という名前の構成子をパターンに書くと，`_root_.ite`と曖昧になる．パターンでは`.ite`と書く．
- 警告をエラーとして扱うので，`@[inherit_doc]`を付けた記法の対象にはdocコメントが要る．
- コンテナの中では`mise.toml`がグローバル設定として読まれるので，`mise.lock`の更新は`mise lock --global`で行う．
