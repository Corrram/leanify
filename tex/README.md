# leanify — a LaTeX article checked by Lean

Version 0.7, 2026-11-10.

Leanify compiles an ordinary mathematical article, written in LaTeX, to the
Lean proof assistant: every definition and theorem becomes a Lean statement
checked by the kernel, and the proofs are checked sentence by sentence against
the results they cite. The same source is typeset as the paper you submit.

The LaTeX package `leanify.sty` is the typesetting side:

* it loads the notation the Leanify grammar reads (`mathtools`, `amssymb`);
* with shell escape, inside a Lean project, it runs the Leanify checker once
  on every compile and reports the findings as LaTeX warnings at their lines;
* with the option `status`, it marks every labelled result in the margin with
  its verification status (*derived*, *argued*, *checked*, *partly checked*,
  *compiled*, *false*);
* `\leanifyreadings` prints the formal reading of every definition and
  statement, so that a reader of the PDF sees what Lean was asked to prove;
* with the option `exe=leanify`, the check runs a checker on the `PATH`,
  outside a Lean project as well;
* without options and without shell escape, it changes nothing in the
  typeset article, so the article compiles anywhere, e.g. on arXiv.

```latex
\usepackage{leanify}            % check as you compile
\usepackage[status]{leanify}    % and show the verification status
\usepackage[certify]{leanify}   % and build the certificate first
```

The package needs LaTeX 2022-06-01 or newer. Checking needs the Lean toolchain
(`lake` on the `PATH`) and the Leanify Lean package; typesetting does not.

Documentation: `leanify-doc.pdf`, and the full documentation, tutorial and
demo at https://corrram.github.io/leanify/.
Source and issues: https://github.com/Corrram/leanify.

## Licence

Copyright (C) 2026 Marcus Rockel. Released under the Apache License,
Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
