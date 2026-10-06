// iterations/以下のLakeパッケージを探す関数．

import { existsSync, readdirSync, statSync } from "node:fs";
import { join, relative, resolve } from "node:path";

/** Iterationの番号の順に，{ iteration, kind, dir }の一覧を返す．kindは"exercise"か"solution"． */
export function allPackages(root = "iterations") {
  if (!existsSync(root)) return [];
  const packages = [];
  for (const name of readdirSync(root)) {
    const m = name.match(/^iteration-(\d+)$/);
    if (!m) continue;
    for (const kind of ["exercise", "solution"]) {
      const dir = join(root, name, kind);
      if (existsSync(join(dir, "lakefile.toml"))) packages.push({ iteration: Number(m[1]), kind, dir });
    }
  }
  return packages.sort((a, b) => a.iteration - b.iteration || a.kind.localeCompare(b.kind));
}

/** ディレクトリdirを含むパッケージを返す．含まなければnullを返す． */
export function packageContaining(dir) {
  const target = resolve(dir);
  for (const p of allPackages()) {
    const rel = relative(resolve(p.dir), target);
    if (!rel.startsWith("..") && !rel.startsWith("/")) return p;
  }
  return null;
}

/** dir以下の.leanファイルを，dirからの相対パスで返す．ビルド出力は含めない． */
export function leanFiles(dir) {
  const out = [];
  const walk = (d) => {
    for (const name of readdirSync(d)) {
      if (name === ".lake") continue;
      const p = join(d, name);
      if (statSync(p).isDirectory()) walk(p);
      else if (name.endsWith(".lean")) out.push(relative(dir, p));
    }
  };
  if (existsSync(dir)) walk(dir);
  return out.sort();
}

/** パッケージからの相対パスをモジュール名にする(Mini/Eval.lean → Mini.Eval)． */
export function moduleName(path) {
  return path.replace(/\.lean$/, "").split("/").join(".");
}
