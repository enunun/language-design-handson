// MarkdownにあるMermaidの図を，Mermaidの構文解析器で検査する．
//
//   node scripts/check-diagrams.mjs [ファイル...]
//
// ファイルを指定しなければ，Gitが管理するすべてのMarkdownファイルを検査する．

import { readFileSync } from "node:fs";
import { JSDOM } from "jsdom";
import { fencedBlocks, markdownFiles } from "./lib/markdown.mjs";

// mermaidはブラウザのDOMを前提にするので，jsdomのDOMを用意してから読み込む．
const dom = new JSDOM("<!doctype html><html><body></body></html>");
globalThis.window = dom.window;
globalThis.document = dom.window.document;
const { default: mermaid } = await import("mermaid");

let errors = 0;
for (const file of markdownFiles(process.argv.slice(2))) {
  const text = readFileSync(file, "utf8");
  for (const block of fencedBlocks(text).filter((b) => b.lang === "mermaid")) {
    try {
      await mermaid.parse(block.body);
    } catch (e) {
      errors++;
      console.error(`${file}:${block.line}: Mermaidの図を解析できない`);
      console.error(String(e.message ?? e).replace(/^/gm, "    "));
    }
  }
}
process.exit(errors > 0 ? 1 : 0);
