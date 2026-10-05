// 模範解答(Solutions/)から，受講者に配る演習ファイル(Handson/)を生成する．
// 「-- 演習ここから」と「-- 演習ここまで」で囲んだ行を`sorry`に置き換え，
// モジュール名のSolutionsをHandsonに置き換える．
//
//   node scripts/gen-handson.mjs          演習ファイルを生成する．
//   node scripts/gen-handson.mjs --check  生成結果と現在の演習ファイルが一致するか確かめる．

import { readFileSync, writeFileSync, readdirSync, existsSync, mkdirSync } from "node:fs";
import { join } from "node:path";

const BEGIN = /^(\s*)-- 演習ここから\s*$/;
const END = /^\s*-- 演習ここまで\s*$/;

function toHandson(source, file) {
  const out = [];
  let indent = null;
  source.split("\n").forEach((line, i) => {
    if (indent === null) {
      const m = line.match(BEGIN);
      if (m) {
        indent = m[1];
      } else if (END.test(line)) {
        throw new Error(`${file}:${i + 1}: 対応する「演習ここから」がない`);
      } else {
        out.push(line.replace(/\bSolutions\b/g, "Handson"));
      }
    } else if (END.test(line)) {
      out.push(`${indent}sorry`);
      indent = null;
    } else if (BEGIN.test(line)) {
      throw new Error(`${file}:${i + 1}: 「演習ここから」が入れ子になっている`);
    }
  });
  if (indent !== null) {
    throw new Error(`${file}: 「演習ここまで」がない`);
  }
  return out.join("\n");
}

const check = process.argv.includes("--check");
const pairs = [["Solutions.lean", "Handson.lean"]];
for (const name of readdirSync("Solutions").filter((f) => f.endsWith(".lean")).sort()) {
  pairs.push([join("Solutions", name), join("Handson", name)]);
}

let stale = [];
for (const [src, dst] of pairs) {
  const expected = toHandson(readFileSync(src, "utf8"), src);
  if (check) {
    if (!existsSync(dst) || readFileSync(dst, "utf8") !== expected) {
      stale.push(dst);
    }
  } else {
    mkdirSync("Handson", { recursive: true });
    writeFileSync(dst, expected);
  }
}

if (stale.length > 0) {
  console.error("演習ファイルが模範解答と一致しない．`mise run gen`で作り直す：");
  for (const f of stale) console.error(`  ${f}`);
  process.exit(1);
}
