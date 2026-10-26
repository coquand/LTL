# Constructive LTL decision procedures in Agda

This development constructs a decision procedure returning either a derivation
of a temporal formula or a certified lasso countermodel. It includes procedures
based on state elimination and on strongly connected components, and versions
with shorter proof certificates.

The current language has propositional variables, negation, implication,
**next**, and **always**. Eventually and the other Boolean connectives are
abbreviations. **Until is not yet implemented.**

## Start here

- [Master's thesis proposal](docs/ltl-master-thesis.pdf)
  ([LaTeX source](docs/ltl-master-thesis.tex)): learn LTL, understand the existing
  proof, extend it with Until, and study execution and readable certificates.
- [Proof extraction from a failed LTL tableau](m4.pdf)
  ([LaTeX](m4.tex)): the state-elimination argument.
- [The SCC decision procedure](m5.pdf)
  ([LaTeX](m5.tex)): the graph certificate argument and comparison.
- [LTL/Decide.agda](LTL/Decide.agda) and
  [LTL/DecideSCC.agda](LTL/DecideSCC.agda): the two public decision procedures.
- [LTL/ShortPC.agda](LTL/ShortPC.agda): shorter derivations using a checked
  propositional-consequence rule.

## Check the development

Tested with **Agda 2.8.0**. No Agda standard library is needed. From the repository
root:

```sh
agda -i . LTL/DecideSCC.agda
agda -i . LTL/ShortPC.agda
agda -i . LTL/Compare.agda
agda -i . LTL/Lecture.agda
agda -i . LTL/Proofs.agda
```

`Compare` imports the examples and contains computational comparisons on 47
formulas. `Lecture` examines a worked example. `Proofs` measures and inspects
proof certificates. These benchmark modules take longer than the core proofs.
The source comments include historical timings; those depend on the machine and
evaluation method.

The files use `--safe --without-K --exact-split`. There are no postulates,
unfinished goals, or termination overrides. The result is expressed in terms
of derivability and finite lasso countermodels. Its relationship to semantic
validity on arbitrary infinite words requires careful specification of the
semantics and constructive assumptions; the proposal discusses this distinction.

## Mathematical entry points

`Formula`, `Deriv`: syntax and deductive rules.

`Closure`, `Gfp`, `Elim`, `Trace`, `Extract`: the finite search and extraction of
derivations from eliminated states.

`Lasso`, `Run`, `Eval`, `Sound`, `Hintikka`: finite countermodels and their
correctness.

`Graph`, `SccLasso`, `SccExtract`, `SccTrap`: graph certificates and their
application to temporal logic.

The textbook and external papers used during the original development are not
included in this repository; bibliographic links are provided in the proposal.
