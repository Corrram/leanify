#!/bin/sh
# Builds build/ctan/leanify.zip, the upload for CTAN (https://ctan.org/upload):
# one top-level folder leanify/ with the README, the package, and its
# documentation as source and PDF.
set -e
cd "$(dirname "$0")/.."
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
