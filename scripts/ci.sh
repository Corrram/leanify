#!/usr/bin/env bash
# The checks of the repository, as CI runs them: `bash scripts/ci.sh` (all of them), or one
# part: `build`, `checks`, `proofs`, `audit`, `reader`, `clean`. `bash scripts/ci.sh update`
# rewrites the expected outputs (review the diff before committing it).
#
# What is checked is read from the repository, so that a new test needs no change here and
# none in `.github/workflows/lean.yml`, which only calls this script:
#
# * every `[[lean_lib]]` of `lakefile.toml` is built (the certificates of the articles);
# * every `check.txt` (and `NAME.check.txt`) in `examples/` and `tests/` is the expected
#   output of `leanify check` on `article.tex` (on `NAME.tex`) in its folder, with the
#   options in `check.args` (`NAME.check.args`) next to it;
# * every article with a `Compiled.lean` is audited by the kernel.
set -euo pipefail
cd "$(dirname "$0")/.."

LEANIFY=.lake/build/bin/leanify
PYTHON=${PYTHON:-python3}
TMP=${RUNNER_TEMP:-$(mktemp -d)}

group() { if [ -n "${GITHUB_ACTIONS:-}" ]; then echo "::group::$1"; else echo "== $1"; fi; }
endgroup() { if [ -n "${GITHUB_ACTIONS:-}" ]; then echo "::endgroup::"; fi; }
fail() { echo "FAILED: $1" >&2; exit 1; }

libraries() { awk '/^\[\[lean_lib\]\]/{lib=1; next} lib && /^name *=/{gsub(/[" ]/,"",$0); sub(/^name=/,"",$0); if ($0 != "Leanify") print $0; lib=0}' lakefile.toml; }
articles() { for f in examples/*/Compiled.lean tests/*/Compiled.lean; do echo "$(dirname "$f")/article.tex"; done; }
expectations() { ls examples/*/*check.txt tests/*/*check.txt 2>/dev/null; }
# the article and the options of an expected output
article_of() { case "$(basename "$1")" in check.txt) echo "$(dirname "$1")/article.tex";; *) echo "${1%.check.txt}.tex";; esac; }
args_of() { local a="${1%check.txt}check.args"; if [ -f "$a" ]; then cat "$a"; fi; }

build() {
  group "Build the checker, the glossary and the certificates of the articles"
  # shellcheck disable=SC2046
  lake build leanify glossary $(libraries)
  endgroup
}

checks() {
  group "The articles are read as their expected outputs say"
  local bad=0
  for exp in $(expectations); do
    local art; art=$(article_of "$exp")
    # shellcheck disable=SC2046
    $LEANIFY check "$art" $(args_of "$exp") > "$TMP/check.out" 2>&1 || true
    if [ "${UPDATE:-}" = 1 ]; then cp "$TMP/check.out" "$exp"; echo "wrote $exp"
    elif diff "$exp" "$TMP/check.out" > "$TMP/check.diff"; then echo "ok   $exp"
    else echo "DIFF $exp"; head -20 "$TMP/check.diff"; bad=1; fi
  done
  [ $bad = 0 ] || fail "an article is not read as its check.txt says (bash scripts/ci.sh update rewrites them)"
  endgroup

  group "The example articles are read without a finding"
  $LEANIFY check examples/Means/article.tex --claims --prose > "$TMP/means.check.txt" || fail "examples/Means has a finding"
  $LEANIFY check tests/TailDependence/article.tex --vocab unitsquare --claims --prose > "$TMP/tail.check.txt" ||
    fail "tests/TailDependence has a finding"
  endgroup

  group "An article in several files is one article"
  $LEANIFY flatten tests/Inputs/article.tex "$TMP/flat.tex"
  $LEANIFY check "$TMP/flat.tex" > "$TMP/flat.check.txt" || true
  grep -q "2 definitions, 5 claims" "$TMP/flat.check.txt" || fail "the flattened article"
  endgroup

  group "The glossary of the vocabulary is up to date"
  lake exe glossary > "$TMP/glossary.md"
  if [ "${UPDATE:-}" = 1 ]; then cp "$TMP/glossary.md" docs/glossary.md; echo "wrote docs/glossary.md"
  else diff docs/glossary.md "$TMP/glossary.md" || fail "docs/glossary.md (lake exe glossary > docs/glossary.md)"; fi
  endgroup

  group "A suggested rewrite of an unread sentence is kept only if the check reads it"
  cp examples/Demo/draft.tex "$TMP/draft.tex"
  $PYTHON scripts/leanify_suggest.py "$TMP/draft.tex" --hook "$PYTHON tests/suggest_hook.py" \
    --leanify $LEANIFY > "$TMP/suggest.txt"
  grep -q "kept 1 of 1 suggestions" "$TMP/suggest.txt" || fail "the suggestion was not kept"
  grep -q "reads as: " "$TMP/suggest.txt" || fail "the suggestion has no reading"
  endgroup
}

proofs() {
  group "Every claim of the examples is verified"
  for a in examples/Demo examples/Means tests/TailDependence; do
    $PYTHON scripts/leanify_diagnostics.py $a/article.leanify.json --strict --verified
  done
  endgroup

  group "Proof steps are closed by the standard tactic, and no statement is empty"
  for a in tests/Arguments; do
    $PYTHON scripts/leanify_diagnostics.py $a/article.leanify.json --verified --standard --satisfiable > "$TMP/standard.txt"
    if grep -q "standard tactic does not close\|not shown to hold together" "$TMP/standard.txt"; then
      cat "$TMP/standard.txt"; fail "$a: a step is not standard, or hypotheses are not shown to hold together"; fi
  done
  # (the hypotheses of the copula example are met by the independence copula)
  $PYTHON scripts/leanify_diagnostics.py tests/TailDependence/article.leanify.json --satisfiable > "$TMP/tail.txt"
  if grep -q "not shown to hold together" "$TMP/tail.txt"; then cat "$TMP/tail.txt"; fail "tests/TailDependence: hypotheses"; fi
  # (a step that needs more than the standard tactic is reported as such)
  $PYTHON scripts/leanify_diagnostics.py examples/Means/article.leanify.json --standard > "$TMP/means.txt"
  grep -q "proof step (claim 1) is derived in the text, but the standard tactic does not close it" "$TMP/means.txt" ||
    fail "examples/Means: the step that is not standard is not reported"
  endgroup

  group "Quoted results are assumptions, and the claims resting on them say so"
  $PYTHON scripts/leanify_diagnostics.py tests/Undefined/article.leanify.json --prose --verified > "$TMP/undefined.txt"
  grep -q "statement (claim 0) is quoted from the literature: the article assumes it" "$TMP/undefined.txt" ||
    fail "tests/Undefined: the quoted statement"
  grep -q "claim 5 derived from its citations, given the quoted claims 0, 1" "$TMP/undefined.txt" ||
    fail "tests/Undefined: the claim that rests on the quoted statements"
  grep -q '"Undefined.Quoted.claim0"' tests/Undefined/article.leanify.json ||
    fail "tests/Undefined: the quoted statement is not among the axioms of the report"
  endgroup

  group "A verified claim after a sentence that is not read is verified as read"
  $PYTHON scripts/leanify_diagnostics.py tests/Context/article.leanify.json --verified > "$TMP/context.txt" 2> "$TMP/context.err"
  grep -q "proof step (claim 7) is verified as read, after a sentence that Leanify does not read (line 45)" "$TMP/context.txt" ||
    fail "tests/Context: the conclusion under the supposition that an unread sentence ends"
  if grep -q "claim \(8\|9\|10\)) is verified as read" "$TMP/context.txt"; then
    fail "tests/Context: a claim of the proof that is read completely is reported"; fi
  grep -q "4 of the verified after a sentence that is not read" "$TMP/context.err" || fail "tests/Context: the count"
  grep -q '^\\leanifycontext{4}$' tests/Context/article.leanify.tex || fail "tests/Context: the record of the status file"
  grep -q '^\\leanifysummary{11}{7}{5}' tests/Context/article.leanify.tex ||
    fail "tests/Context: the summary counts the claims that are verified as read among the verified"
  endgroup

  group "The refuted theorem is reported false, and the claims resting on it unverified"
  if $PYTHON scripts/leanify_diagnostics.py tests/Refuted/article.leanify.json > "$TMP/refuted.txt"; then
    fail "tests/Refuted: no error reported"; fi
  grep -q "error: statement (claim 2) is false as stated" "$TMP/refuted.txt" || fail "tests/Refuted: the false statement"
  grep -q "(claim 5) compiled but not verified: it rests on claim 2, which is refuted" "$TMP/refuted.txt" ||
    fail "tests/Refuted: the claim that rests on it"
  endgroup
}

audit() {
  group "The kernel evaluates the compiler on the articles (the audit)"
  for a in $(articles); do $LEANIFY audit "$a" | tail -1; done
  endgroup
}

reader() {
  group "Reader tests"
  npm test
  endgroup
}

clean() {
  group "Reports and dependency pins are up to date"
  git diff --exit-code -- lean-toolchain lakefile.toml lake-manifest.json examples tests ||
    fail "the build changed a committed report or pin: commit the new files"
  endgroup
}

case "${1:-all}" in
  build) build;;
  checks) checks;;
  proofs) proofs;;
  audit) audit;;
  reader) reader;;
  clean) clean;;
  update) UPDATE=1 checks;;
  all) build; checks; proofs; audit; reader; clean;;
  *) echo "usage: bash scripts/ci.sh [build|checks|proofs|audit|reader|clean|update|all]" >&2; exit 2;;
esac
