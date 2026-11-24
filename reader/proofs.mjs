// The Lean proofs of a certified article, for the reader: the declaration that
// justifies each claim and definition, and the lemmas of the same files that it
// uses, so that a reader gets from a sentence to its proof without a search.
import fs from 'node:fs';
import path from 'node:path';

const HEAD = /^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:({\[]+)/;
const STOP = /^(?:\/--|\/-!|end\b|namespace\b|section\b|open\b|variable\b|set_option\b|attribute\b|#|@\[)/;

/** The top-level declarations of a Lean file: name, code (without its docstring), first line. */
export function declarations(text, file = '') {
  const lines = text.replace(/\r\n/g, '\n').split('\n');
  const out = [];
  for (let i = 0; i < lines.length; i++) {
    const m = HEAD.exec(lines[i]);
    if (!m) continue;
    let j = i + 1;
    while (j < lines.length && !HEAD.test(lines[j]) && !STOP.test(lines[j])) j++;
    const code = lines.slice(i, j).join('\n').replace(/\s+$/, '');
    out.push({name: m[2].split('.').pop(), kind: m[1], code, file, line: i + 1});
    i = j - 1;
  }
  return out;
}

/** The Lean files next to an article that hold its proofs: `Proofs.lean` of the
    namespace and the files beside it, without the generated ones. */
export function proofFiles(texPath, namespace) {
  const dir = path.dirname(path.resolve(texPath));
  const found = [];
  const walk = (d, depth) => {
    if (depth > 3) return;
    for (const e of fs.readdirSync(d, {withFileTypes: true})) {
      if (e.name === '.lake' || e.name === 'node_modules' || e.name.startsWith('.')) continue;
      const p = path.join(d, e.name);
      if (e.isDirectory()) walk(p, depth + 1);
      else if (e.name === 'Proofs.lean' && (!namespace || path.basename(d) === namespace)) found.push(p);
    }
  };
  walk(dir, 0);
  if (!found.length) return [];
  found.sort((a, b) => a.length - b.length);
  const home = path.dirname(found[0]);
  const generated = new Set(['Compiled.lean', 'Article.lean', 'Certified.lean']);
  return fs.readdirSync(home).filter(f => f.endsWith('.lean') && !generated.has(f)).sort().map(f => path.join(home, f));
}

/** `{name: {code, file, line, uses}}` for the declarations that justify a claim or a
    definition of the report, and for what they use among the given files. */
export function proofsOf(report, files) {
  const index = new Map();
  for (const f of files) {
    for (const d of declarations(fs.readFileSync(f, 'utf8'), path.basename(f))) if (!index.has(d.name)) index.set(d.name, d);
  }
  const out = {};
  const visit = name => {
    if (name in out) return;
    const d = index.get(name);
    if (!d) return;
    const uses = [...new Set((d.code.match(/[A-Za-z_][\w'!?₀-₉]*/g) ?? []))].filter(w => w !== name && index.has(w));
    out[name] = {code: d.code, file: d.file, line: d.line, uses};
    uses.forEach(visit);
  };
  const short = j => String(j ?? '').split('.').pop();
  for (const c of report.claims) visit(short(c.justification));
  for (const d of report.definitions) visit(short(d.justification));
  return out;
}
