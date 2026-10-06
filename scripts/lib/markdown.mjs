// Markdownの検査スクリプトが共通で使う関数．

import { execFileSync } from "node:child_process";

/** Gitが管理するMarkdownファイルの一覧を返す．引数があれば，それをそのまま返す． */
export function markdownFiles(args) {
  if (args.length > 0) return args;
  return execFileSync("git", ["ls-files", "--cached", "--others", "--exclude-standard", "*.md"], {
    encoding: "utf8",
  })
    .split("\n")
    .filter((f) => f !== "");
}

/** 文字列中の位置を1始まりの行番号に変える． */
export function lineOf(text, index) {
  return text.slice(0, index).split("\n").length;
}

/** フェンスで囲んだコードブロックを，言語名・本文・開始行とともに返す． */
export function fencedBlocks(text) {
  const blocks = [];
  const re = /^(```+|~~~+)[ \t]*([\w-]*)[^\n]*\n([\s\S]*?)^\1[ \t]*$/gm;
  for (const m of text.matchAll(re)) {
    blocks.push({ lang: m[2], body: m[3], line: lineOf(text, m.index) + 1, start: m.index, end: m.index + m[0].length });
  }
  return blocks;
}

/** コードブロックとインラインコードを，行数を変えずに空白へ置き換えた文字列を返す． */
export function withoutCode(text) {
  let out = text;
  for (const b of fencedBlocks(text)) {
    const blank = text.slice(b.start, b.end).replace(/[^\n]/g, " ");
    out = out.slice(0, b.start) + blank + out.slice(b.end);
  }
  return out.replace(/(`+)[\s\S]*?\1/g, (s) => s.replace(/[^\n]/g, " "));
}
