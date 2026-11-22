# leanify — a LaTeX article checked by Lean

Version 0.7, 2026-11-10.

Leanify compiles an ordinary mathematical article, written in LaTeX, to the
Lean proof assistant: every definition and theorem becomes a Lean statement
checked by the kernel, and the proofs are checked sentence by sentence against
the results they cite. The same source is typeset as the paper you submit.

The LaTeX package `leanify.sty` is the typesetting side:

* it loads the notation the Leanify grammar reads (`mathtools`, `amssymb`);
* with shell escape, it runs the Leanify checker once on every compile and
  reports the findings as LaTeX warnings at their lines: the checker of the
  Lean project the article lies in, or else `leanify` on the `PATH`;
* an article in no Lean project gets one from that checker, once, in the
  folder `lean` next to it (not with the option `project=false`), so that its
  certificate has a place;
* with the option `status`, it marks every labelled result in the margin with
  its verification status (*derived*, *argued*, *checked*, *quoted*, *partly
  checked*, *compiled*, *false*);
* with the option `notions={graph, finite graph}`, the article names the nouns
  that it uses without defining them, and nothing is printed for them. A result
  whose heading cites its source and that has no proof is quoted from the
  literature, and the certificate lists it as an assumption;
* `\leanifyreadings` prints the formal reading of every definition and
  statement, so that a reader of the PDF sees what Lean was asked to prove;
* with the option `exe=COMMAND`, the check runs that checker instead;
* without shell escape nothing runs, and without options nothing changes in
  the typeset article, so the article compiles anywhere, e.g. on arXiv.

```latex
\usepackage{leanify}            % check as you compile
\usepackage[status]{leanify}    % and show the verification status
\usepackage[certify]{leanify}   % and build the certificate first
```

The package needs LaTeX 2022-06-01 or newer. Checking needs the checker: the
executable `leanify` on the `PATH`, or the Lean toolchain (`lake` on the `PATH`)
and the Leanify Lean package. The certificate needs Lean. Typesetting needs
neither.

Documentation: `leanify-doc.pdf`, and the full documentation, tutorial and
demo at https://corrram.github.io/leanify/.
Source and issues: https://github.com/Corrram/leanify.

## Licence

Copyright (C) 2026 Marcus Rockel. Released under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
