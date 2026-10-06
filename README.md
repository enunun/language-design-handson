# 操作的意味論による言語設計ハンズオン

小さな関数型言語Miniの処理系を，証明支援系Lean 4で育てるハンズオンである．
Iterationごとに言語へ機能を足し，その意味を推論規則で定め，評価器と型検査器を実装する．
テストはすべてLeanの定理として書く．
実装が意味論に従うことと，言語が満たすべき性質(決定性や型安全性など)を証明する．

## 学ぶこと

- 小さな言語を設計し，検証する．新しい言語機能の構文・評価規則・型付け規則を定義し，型安全性などの性質をLeanで証明する．
- 論文や言語仕様にある推論規則を読む．
- 評価戦略や型付け規則の選択肢を，性質が保たれるかどうかで比べる．
- 評価器と型検査器を実装し，それが意味論に従うことを証明する．

プログラミングと単体テストの経験を前提とする．
Leanと操作的意味論の知識は前提としない．

## 環境の準備

DockerとVSCode(拡張機能Dev Containers)を使う．

1. このリポジトリをVSCodeで開き，コマンドパレットで「Dev Containers: Reopen in Container」を実行する．
2. 初回は，コンテナの作成後に`mise run setup`が自動で実行され，依存パッケージとGitのフックが入る．
3. コンテナの端末で次のコマンドを実行し，すべての検査が通ることを確かめる．

``` sh
mise run check
```

コンテナにはLean 4が入っている．版は`lean-toolchain`で固定している．
VSCodeには，証明の状態を表示するLean 4拡張と，数式とMermaidの図を表示するMarkdown Preview Enhancedが入る．
使えるタスクの一覧は`mise tasks`で表示できる．

## 進め方

各Iterationは`iterations/iteration-N/`にある．
`exercise/`で作業し，`solution/`で模範解答を確かめる．
`exercise/`は前のIterationの`solution/`と同じ状態から始まる．

どのIterationも，テストリスト → 設計書 → テストファーストの実装 → 設計レビューの順に進める．
手順は各Iterationの`exercise/docs/iteration-N.md`にある．

- [ロードマップ](docs/ROADMAP.md)：完成するプログラムと，各Iterationで作るもの・学ぶこと．
- [定理によるテスト駆動開発](docs/tdd.md)：テストの書き方とテストリストの作り方．
- [設計書の書き方](docs/design.md)：言語仕様書とモジュール依存図．

## Iterationの一覧

| Iteration | 作る機能 | ノート |
| --- | --- | --- |
| [0](iterations/iteration-0/) | 自然数の四則と評価器 | [Lean](docs/lean/iteration-0.md)，[意味論](docs/semantics/iteration-0.md) |
| [1](iterations/iteration-1/) | 大ステップ意味論と評価器の正しさ | [Lean](docs/lean/iteration-1.md)，[意味論](docs/semantics/iteration-1.md) |
| [2](iterations/iteration-2/) | 簡約列の表示 | [Lean](docs/lean/iteration-2.md)，[意味論](docs/semantics/iteration-2.md) |
| [3](iterations/iteration-3/) | 真偽値と条件分岐 | [Lean](docs/lean/iteration-3.md)，[意味論](docs/semantics/iteration-3.md) |
| 4 | 型と型検査器 | |
| 5 | 変数と`let` | |
| 6 | 関数と関数適用 | |
| 7 | 再帰 | |
| 8 | 組 | |

ノートは，そのIterationで初めて使うLeanの構文と，初めて扱う意味論の考え方を説明する．

## ディレクトリ構成

``` text
iterations/iteration-N/
  exercise/            受講者が作業するパッケージ
  solution/            完成した演習と模範解答
docs/
  ROADMAP.md           ロードマップ
  tdd.md               定理によるテスト駆動開発
  design.md            設計書の書き方
  lean/                Iterationごとの，Leanの構文とtacticのノート
  semantics/           Iterationごとの，意味論の考え方のノート
scripts/               教材の検査スクリプト(数式，図，設計書と実装の照合)
COURSE.md              教材を作る人のためのコース計画
```
