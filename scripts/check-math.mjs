// Markdownにある数式(```mathのコードブロック，$$…$$，$…$)を，MathJaxで検査する．
//
//   node scripts/check-math.mjs [ファイル...]
//
// ファイルを指定しなければ，Gitが管理するすべてのMarkdownファイルを検査する．
// ```math以外のコードブロックとインラインコードの中の$は，数式として扱わない．

import { readFileSync } from "node:fs";
import { mathjax } from "mathjax-full/js/mathjax.js";
import { TeX } from "mathjax-full/js/input/tex.js";
import { AllPackages } from "mathjax-full/js/input/tex/AllPackages.js";
import { SVG } from "mathjax-full/js/output/svg.js";
import { liteAdaptor } from "mathjax-full/js/adaptors/liteAdaptor.js";
import { RegisterHTMLHandler } from "mathjax-full/js/handlers/html.js";
import { fencedBlocks, lineOf, markdownFiles, withoutCode } from "./lib/markdown.mjs";

RegisterHTMLHandler(liteAdaptor());
// noerrorsとnoundefinedを外し，構文の誤りと未定義の命令を例外として受け取る．
const tex = new TeX({
  packages: AllPackages.filter((p) => p !== "noerrors" && p !== "noundefined"),
  formatError: (_jax, err) => {
    throw err;
  },
});
const doc = mathjax.document("", { InputJax: tex, OutputJax: new SVG() });

let errors = 0;
for (const file of markdownFiles(process.argv.slice(2))) {
  const raw = readFileSync(file, "utf8");
  const formulas = fencedBlocks(raw)
    .filter((b) => b.lang === "math")
    .map((b) => ({ body: b.body, display: true, line: b.line }));
  const text = withoutCode(raw);
  const rest = text.replace(/\$\$([\s\S]+?)\$\$/g, (s, body, index) => {
    formulas.push({ body, display: true, line: lineOf(text, index) });
    return s.replace(/[^\n]/g, " ");
  });
  for (const m of rest.matchAll(/(?<![\\$])\$([^$\n]+?)\$/g)) {
    formulas.push({ body: m[1], display: false, line: lineOf(rest, m.index) });
  }
  for (const f of formulas) {
    try {
      doc.convert(f.body, { display: f.display });
    } catch (e) {
      errors++;
      console.error(`${file}:${f.line}: 数式を解析できない(${e.message})`);
    }
  }
}
process.exit(errors > 0 ? 1 : 0);
