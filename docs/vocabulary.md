# The vocabulary, and words with several meanings

Leanify reads an article's words through its *vocabulary*: nouns (`probability
distribution on $\mathbb{N}_0$`), adjectives (`prime`, `even`) and named notions
(`the Poisson distribution with mean $\lambda$`), each with one exact meaning, a
term of Leanify's formula language whose Lean reading is built on Mathlib
(`docs/glossary.md` lists every entry with its meaning and the Mathlib
definitions it rests on).

The same English word means different things in different parts of mathematics:
*normal* (a subgroup, a distribution, a vector, a space), *regular*, *closed*,
*distribution*, *natural number* (with or without 0), *increasing* (strictly or
not), *positive* (in French usage, `≥ 0`). This page explains how Leanify decides
which meaning an article uses.

## The principle: the printed text fixes the meaning

A certificate is only worth something if a reader of the PDF knows what was
certified. So Leanify never takes a meaning from anything the reader cannot see.
There are no hidden per-word annotations in the LaTeX source: an invisible
`\leanifymeaning{normal}{group theory}` would let the PDF say one thing while Lean
checks another, and "this article was leanified" would no longer tell the reader
what its theorems mean.

Every meaning is fixed by one of the following, from the most specific to the
most general; all of them are printed.

1. **The article's own definitions and conventions** come first. Besides its
   definitions (`We call a copula $C$ LTD if …`, `Let $\mathcal C$ denote the
   class of …`) an article can state which meaning it uses, in ordinary sentences:

   * `By a distribution we mean a probability distribution on $\mathbb{N}_0$.`
     (a noun: the article's own class, which takes precedence over any vocabulary
     noun with the same words);
   * `Throughout, increasing means non-decreasing.` (words that stand for other
     words in the following sentences; `strictly increasing` keeps its meaning);
   * `In this paper, positive means non-negative.`;
   * notation: `We write $\mathrm{Poi}(\lambda)$ for the Poisson distribution with
     mean $\lambda$.`, `We write $\mathcal P$ for the set of probability
     distributions on $\mathbb{N}_0$.`, `We write $a\sim b$ if $|a-b|\le1$.`,
     `We write $\langle a,b\rangle$ for $\frac{a+b}{2}$.`

   These are the sentences a careful author writes anyway, and a reader sees them.

2. **The whole phrase.** Leanify matches the longest phrase: *normal
   distribution* and *normal subgroup* are different entries, and neither is the
   adjective *normal*.

3. **The type of what the phrase is about.** An adjective applies to objects of
   one type: `$n$ is even` about an integer and `$f$ is even` about a real
   function are different entries, and the declared type of `n` or `f` (printed:
   `Let $f:\mathbb R\to\mathbb R$ …`) decides.

4. **The fields the article names.** The vocabulary is divided into fields
   (`numbers`, `unitsquare`, `distributions`, …); within a field every phrase has at
   most one meaning. The article names the fields it uses in its preamble,
   `\usepackage[vocab={numbers,analysis}]{leanify}`, and `\leanifyreport` prints
   them with the verification summary (`Leanify (vocabulary: core, numbers,
   analysis): …`), so the printed article states its dictionary. The core
   vocabulary is always used.

5. **Otherwise Leanify refuses.** If the article's fields give a phrase two
   meanings that the steps above do not separate, the sentence is not checked and
   Leanify says so: `"normal" has several meanings (in algebra and probability);
   say which is meant in the text (By a … we mean …)`. It never picks one silently.

Words Leanify does not know are prose: the sentence is reported as not read, and
nothing about it is certified.

One declaration is not in the printed text: the list of the nouns that an article uses
*without* a meaning (`\usepackage[notions={graph}]{leanify}`,
[Writing for Leanify](writing.md#notions-that-the-article-does-not-define)). It gives a
word no meaning, so it cannot change what a sentence means. It says that the word is
left undefined, and `\leanifyreport` and every report list these words.

## Words that are ambiguous in every field

Some words are ambiguous even within one field, and Leanify does not read them
alone, whatever the fields:

* *increasing* and *decreasing* (strictly or not): write *strictly increasing* or
  *non-decreasing*, or state the convention (`Throughout, increasing means
  non-decreasing.`);
* *natural number*: say *non-negative integer* or *positive integer*, or state
  the convention (`By a natural number we mean a non-negative integer.`). The
  symbol $\mathbb{N}$ includes 0, as in Mathlib; $\mathbb{N}_0$ says so explicitly.

## The core vocabulary

Every article is read with the core vocabulary, whatever fields it names: *real
number*, *integer*, *positive*, *negative* and *nonnegative integer*, *rational* and
*irrational number*, and the adjectives *positive*, *negative*, *nonnegative*,
*nonpositive*, *nonzero*, *rational*, *irrational* of a real number. So
`Let $x$ and $y$ be positive real numbers.` needs no field. The words of number
theory (*prime*, *even*, *squarefree*, the greatest common divisor) are the field
`numbers`. A symbol or noun that a field would read is reported with the field's
name: `unknown notation \cosh: the field hyperbolic of the vocabulary reads it`.

## Fields

`docs/glossary.md` lists the fields and their entries; `lake exe glossary`
regenerates it from the vocabulary itself. A field is a Lean value
(`Leanify.Vocab`) in `Leanify/Library/`, registered in
`Leanify.Fields.all`. Fields built from the core formula language (most of them)
need nothing else: their meaning is the meaning of the formula language, which
`Leanify.Denote` gives in terms of Mathlib. A field with constants of its own
(`unitsquare`, `torus`, `complex`, `hyperbolic`, `trigonometry`) names the Lean
meaning of each: a declaration of Mathlib (`Real.sinh`), or a definition written for
the field. A function of a field may have a domain (`\arcsin` on `[-1,1]`, in
`trigonometry`): a claim that uses it is meaningful only on the domain.
The field `unitsquare` also makes `[0,1]` a type of its own, with its integral and
Lebesgue measure; without it, `[0,1]` is a set of real numbers like any interval.
An article may use several such fields. A field can declare a type of
its own and say what notation means on it (`complex`: `z+w`, `|z|`, `\overline{z}` on
`\mathbb{C}`), as `docs/vocabularies.md` explains.

On the command line, `leanify check article.tex --vocab numbers,analysis` and
`leanify init article.tex --vocab numbers,analysis` use the same fields;
`leanify.sty` passes its `vocab` option on.
