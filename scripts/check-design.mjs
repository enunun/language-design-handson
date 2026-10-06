// パッケージの設計書(design/)と実装を照合する．
//
//   node scripts/check-design.mjs [パッケージのディレクトリ...]
//
// ディレクトリを指定しなければ，mise runを実行したディレクトリを含むパッケージを照合する．
// そこがパッケージの中でなければ，すべての解答パッケージを照合する．
//
// 照合する内容：
//   1. design/modules.mdの依存の矢印と，Mini/とMain.leanのimport文．
//   2. design/spec.mdの「## 意味」と「## 型」にある「### …`Name`」の節の規則名(\textsf{…})と，inductive Nameの構成子名．
//   3. design/spec.mdの「## 性質」に挙げた定理名が，MiniTest/にtheoremとしてあること．

import { existsSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { fencedBlocks, withoutCode } from "./lib/markdown.mjs";
import { allPackages, leanFiles, moduleName, packageContaining } from "./lib/packages.mjs";

/** 推論規則を書く節．この下の「### …`Name`」の節を，inductive Nameと照合する． */
const RULE_SECTIONS = ["意味", "型"];

function targetDirs(args) {
  if (args.length > 0) return args;
  const here = packageContaining(process.env.MISE_ORIGINAL_CWD ?? process.cwd());
  if (here) return [here.dir];
  return allPackages()
    .filter((p) => p.kind === "solution")
    .map((p) => p.dir);
}

/** design/modules.mdのMermaidの図から，依存の矢印を「A -> B」の集合として読む． */
function diagramEdges(text) {
  const block = fencedBlocks(text).find((b) => b.lang === "mermaid");
  if (!block) return new Set();
  const labels = new Map();
  const node = /([A-Za-z_][\w]*)\s*\[\s*"?([^"\]]+)"?\s*\]/g;
  for (const m of block.body.matchAll(node)) labels.set(m[1], m[2].trim());
  const name = (id) => labels.get(id) ?? id;
  const edges = new Set();
  const ref = String.raw`([A-Za-z_][\w]*)(?:\s*\[[^\]]*\])?`;
  const edge = new RegExp(`${ref}\\s*-->\\s*${ref}`, "g");
  for (const line of block.body.split("\n")) {
    for (const m of line.matchAll(edge)) edges.add(`${name(m[1])} -> ${name(m[2])}`);
  }
  return edges;
}

/** Mini/とMain.leanのimport文から，パッケージ内の依存を「A -> B」の集合として読む． */
function codeEdges(dir) {
  const files = leanFiles(join(dir, "Mini"))
    .map((f) => join("Mini", f))
    .concat(existsSync(join(dir, "Main.lean")) ? ["Main.lean"] : []);
  const modules = new Set(files.map(moduleName));
  const edges = new Set();
  for (const f of files) {
    const from = moduleName(f);
    for (const m of readFileSync(join(dir, f), "utf8").matchAll(/^import\s+(\S+)/gm)) {
      if (modules.has(m[1])) edges.add(`${from} -> ${m[1]}`);
    }
  }
  return edges;
}

/** 見出しで区切った節を，{ level, title, parent, body }の一覧として返す．parentは直前の##見出しである． */
function sections(text) {
  const out = [];
  const heads = [...text.matchAll(/^(#{2,6})\s+(.*)$/gm)];
  let parent = null;
  heads.forEach((h, i) => {
    const level = h[1].length;
    const title = h[2].trim();
    if (level === 2) parent = title;
    const next = heads.slice(i + 1).find((n) => n[1].length <= level);
    out.push({ level, title, parent, body: text.slice(h.index + h[0].length, next ? next.index : text.length) });
  });
  return out;
}

/** inductive Nameの構成子名を，パッケージのMini/から探す．見つからなければnullを返す． */
function constructors(dir, name) {
  for (const f of leanFiles(join(dir, "Mini"))) {
    const lines = readFileSync(join(dir, "Mini", f), "utf8").split("\n");
    const start = lines.findIndex((l) => new RegExp(`^\\s*inductive\\s+${name}\\b`).test(l));
    if (start < 0) continue;
    const names = new Set();
    for (const l of lines.slice(start + 1)) {
      const m = l.match(/^\s*\|\s*([A-Za-z_][\w']*)/);
      if (m) names.add(m[1]);
      else if (/^\S/.test(l)) break;
    }
    return names;
  }
  return null;
}

function theoremExists(dir, name) {
  const re = new RegExp(`^\\s*(?:private\\s+)?theorem\\s+(?:[\\w.]+\\.)?${name.replace(/\./g, "\\.")}\\b`, "m");
  return leanFiles(join(dir, "MiniTest")).some((f) => re.test(readFileSync(join(dir, "MiniTest", f), "utf8")));
}

function difference(a, b) {
  return [...a].filter((x) => !b.has(x)).sort();
}

function checkPackage(dir) {
  const problems = [];
  const modulesDoc = join(dir, "design", "modules.md");
  const specDoc = join(dir, "design", "spec.md");

  if (existsSync(modulesDoc)) {
    const drawn = diagramEdges(readFileSync(modulesDoc, "utf8"));
    const coded = codeEdges(dir);
    for (const e of difference(drawn, coded)) problems.push(`${modulesDoc}: 図にだけある依存：${e}`);
    for (const e of difference(coded, drawn)) problems.push(`${modulesDoc}: 図にないimport：${e}`);
  } else {
    problems.push(`${modulesDoc}がない`);
  }

  if (existsSync(specDoc)) {
    const spec = sections(readFileSync(specDoc, "utf8"));
    for (const sec of spec.filter((x) => x.level === 3 && RULE_SECTIONS.includes(x.parent))) {
      const m = sec.title.match(/`([A-Za-z_][\w]*)`$/);
      if (!m) continue;
      const math = fencedBlocks(sec.body)
        .filter((b) => b.lang === "math")
        .map((b) => b.body)
        .concat(withoutCode(sec.body))
        .join("\n");
      const rules = new Set([...math.matchAll(/\\textsf\{([^}]+)\}/g)].map((r) => r[1]));
      const ctors = constructors(dir, m[1]);
      if (ctors === null) {
        problems.push(`${specDoc}: inductive ${m[1]}が見つからない`);
        continue;
      }
      for (const r of difference(rules, ctors)) problems.push(`${specDoc}: ${m[1]}の構成子にない規則：${r}`);
      for (const c of difference(ctors, rules)) problems.push(`${specDoc}: 仕様書にない${m[1]}の構成子：${c}`);
    }
    const props = spec.find((x) => x.level === 2 && x.title === "性質");
    for (const m of props ? props.body.matchAll(/^\s*-\s+`([\w.']+)`/gm) : []) {
      if (!theoremExists(dir, m[1])) problems.push(`${specDoc}: MiniTest/にない定理：${m[1]}`);
    }
  } else {
    problems.push(`${specDoc}がない`);
  }
  return problems;
}

let failed = false;
for (const dir of targetDirs(process.argv.slice(2))) {
  const problems = checkPackage(dir);
  if (problems.length === 0) {
    console.log(`一致   ${dir}`);
  } else {
    failed = true;
    console.log(`不一致 ${dir}`);
    for (const p of problems) console.log(`    ${p}`);
  }
}
process.exit(failed ? 1 : 0);
