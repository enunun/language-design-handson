// Iteration Nの演習が，Iteration N-1の解答と同じ状態から始まることを確かめる．
//
//   node scripts/check-exercises.mjs
//
// パッケージ名を書いたlakefile.toml，Iterationごとに書く文書(README.md，TESTLIST.md，docs/)，
// 配布物(handout/)，ビルド出力は比較しない．

import { execFileSync } from "node:child_process";
import { allPackages } from "./lib/packages.mjs";

const EXCLUDE = ["lakefile.toml", "lake-manifest.json", "README.md", "TESTLIST.md", "docs", "handout", ".lake"];

const packages = allPackages();
const solution = new Map(packages.filter((p) => p.kind === "solution").map((p) => [p.iteration, p.dir]));
let failed = false;
for (const p of packages.filter((p) => p.kind === "exercise" && p.iteration > 0)) {
  const previous = solution.get(p.iteration - 1);
  if (!previous) {
    failed = true;
    console.log(`前の解答がない ${p.dir}`);
    continue;
  }
  const args = ["-r", ...EXCLUDE.flatMap((x) => ["-x", x]), previous, p.dir];
  try {
    execFileSync("diff", args, { encoding: "utf8" });
    console.log(`一致   ${p.dir} = ${previous}`);
  } catch (e) {
    failed = true;
    console.log(`不一致 ${p.dir} ≠ ${previous}`);
    console.log(String(e.stdout).replace(/^/gm, "    "));
  }
}
process.exit(failed ? 1 : 0);
