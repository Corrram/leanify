#!/bin/sh
# The LaTeX package for CTAN (https://ctan.org/pkg/leanify).
#
#   sh scripts/ctan.sh            builds build/ctan/leanify.zip: one top-level folder
#                                 leanify/ with the README, the package, and its
#                                 documentation as source and PDF
#   sh scripts/ctan.sh validate   builds it and asks CTAN to check it (nothing is stored)
#   sh scripts/ctan.sh upload     builds it and submits it as an update, unless CTAN
#                                 already has this version
#
# `validate` and `upload` use the upload interface of CTAN (https://ctan.org/help/submit)
# and need the address of the uploader in CTAN_EMAIL. It is sent to CTAN only, which
# confirms the upload to it. The version is the one of \ProvidesPackage in
# tex/leanify.sty: CTAN takes an update only under a new version, so a change of the
# package that is to be released changes that line (and tex/README.md, tex/leanify-doc.tex).
# CTAN_ANNOUNCEMENT, if set, is the text of the announcement on the CTAN mailing list
# (none is sent without it), and CTAN_NOTE is a note to the CTAN team.
# An upload is handled by the CTAN team by hand: release versions, not every commit.
set -e
cd "$(dirname "$0")/.."
mode="${1:-build}"
case "$mode" in build|validate|upload) ;; *) echo "usage: sh scripts/ctan.sh [validate|upload]" >&2; exit 2;; esac

out=build/ctan
rm -rf "$out"
mkdir -p "$out/leanify" "$out/doc"
cp tex/leanify-doc.tex tex/leanify.sty "$out/doc/"
(cd "$out/doc" && pdflatex -interaction=nonstopmode -halt-on-error leanify-doc.tex >/dev/null \
               && pdflatex -interaction=nonstopmode -halt-on-error leanify-doc.tex >/dev/null)
cp tex/README.md tex/leanify.sty tex/leanify-doc.tex "$out/doc/leanify-doc.pdf" "$out/leanify/"
(cd "$out" && zip -qrX leanify.zip leanify)
echo "$out/leanify.zip:"
unzip -l "$out/leanify.zip"
[ "$mode" = build ] && exit 0

# the version of the package: `\ProvidesPackage{leanify}[2026/11/10 v0.7 …]` gives 0.7
version="$(sed -n 's/^\\ProvidesPackage{leanify}\[[0-9\/]* v\([0-9][0-9.]*\).*/\1/p' tex/leanify.sty)"
[ -n "$version" ] || { echo "no version in the \\ProvidesPackage line of tex/leanify.sty" >&2; exit 1; }
# the three places that state it agree
grep -q "^Version $version," tex/README.md || { echo "tex/README.md does not say Version $version" >&2; exit 1; }
grep -q "Version $version," tex/leanify-doc.tex || { echo "tex/leanify-doc.tex does not say Version $version" >&2; exit 1; }
[ -n "$CTAN_EMAIL" ] || { echo "set CTAN_EMAIL to the address of the uploader" >&2; exit 1; }
echo "leanify $version"

if [ "$mode" = upload ]; then
  # the version that CTAN has (its catalogue as JSON); if it cannot be read, CTAN decides:
  # it refuses a version that it already has
  have="$(curl -fsS -m 30 https://ctan.org/json/2.0/pkg/leanify 2>/dev/null \
    | sed -n 's/.*"version" *: *{[^}]*"number" *: *"\([^"]*\)".*/\1/p' | head -n 1)"
  if [ "$have" = "$version" ]; then
    echo "CTAN has leanify $version: nothing to upload"
    exit 0
  fi
  echo "CTAN has leanify ${have:-(version not read)}: uploading $version"
fi

set -- \
  --form-string "pkg=leanify" \
  --form-string "version=$version" \
  --form-string "author=Marcus Rockel" \
  --form-string "uploader=Marcus Rockel" \
  --form-string "email=$CTAN_EMAIL" \
  --form-string "update=true" \
  --form-string "ctanPath=/macros/latex/contrib/leanify" \
  --form-string "license=apache2" \
  --form-string "summary=A LaTeX article checked by the Lean proof assistant" \
  --form-string "description=Leanify compiles an ordinary mathematical article, written in LaTeX, to the Lean proof assistant: every definition and theorem becomes a Lean statement checked by the kernel, and the proofs are checked sentence by sentence against the results they cite. The package is the typesetting side: it runs the checker during the compile and reports its findings as LaTeX warnings at their lines, marks every result in the margin with its verification status, and prints the formal reading of every statement. Without options and without shell escape it changes nothing in the typeset article." \
  --form-string "home=https://corrram.github.io/leanify/" \
  --form-string "repository=https://github.com/Corrram/leanify" \
  --form-string "bugtracker=https://github.com/Corrram/leanify/issues"
[ -z "$CTAN_ANNOUNCEMENT" ] || set -- "$@" --form-string "announcement=$CTAN_ANNOUNCEMENT"
[ -z "$CTAN_NOTE" ] || set -- "$@" --form-string "note=$CTAN_NOTE"

# CTAN answers 200 if it has no objection, and lists its messages in the body
code="$(curl -sS -m 120 -o "$out/ctan-answer.txt" -w '%{http_code}' "$@" \
  -F "file=@$out/leanify.zip;type=application/zip" "https://www.ctan.org/submit/$mode")" \
  || { echo "CTAN could not be reached" >&2; exit 1; }
cat "$out/ctan-answer.txt"; echo
if [ "$code" != 200 ]; then
  echo "CTAN answered $code to $mode" >&2
  exit 1
fi
if [ "$mode" = upload ]; then
  echo "leanify $version is submitted: the CTAN team installs it and confirms by mail"
else
  echo "CTAN has no objection to leanify $version (nothing was uploaded)"
fi
