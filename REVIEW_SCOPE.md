# Review scope and manuscript alignment

## Manuscript and formal source are kept distinct

The PDF and TeX in `manuscript/v9/` are from the original v9 release ZIP.
The five Lean modules under `TPCV9/V9/` are byte-identical to the original
`supplement/lean/` files in that release. See `provenance/SOURCE_SHA256.json`.

In the v9 final capstone the principal declaration is:

```lean
theorem current_source_implies_tpc
    {H A3 E W Rpp T : ℕ → ℝ}
    (S : FinalAnalyticSourceCurrent H A3 E W Rpp T) :
    TwinPrimeConjecture := by
```

This type is printed during auditing: the package neither erases the input
`S` nor reports the theorem as an unconditional conclusion. The v9 manuscript
describes external analytic inputs and their use. This bundle makes its
computational audit inspectable without silently converting conditional
statements into unconditional ones.

## What is checked in the default Lake build

* The v9 final implication, coefficient inequalities, Weil normalization adapter,
  interior-boundary calculations, Selberg boundary, classical BV boundary, and
  smoothed PNT boundary files.
* Newer independently scoped TP120, TP128 and TP132 audit files.
* A definitional check that the final `TwinPrimeConjecture` uses `Nat.Prime`
  and means primes p,p+2 beyond every natural-number bound.
* `#print axioms` for explicitly named critical theorems; CI also checks the
  allowed axiom list for those names.

## What this package does not imply on its own

* It does not turn any paper-only theorem into a Mathlib theorem simply by
  declaring a proposition or supplying it as a structure field.
* It does not by itself prove that every external analytic theorem cited in
  the prose applies to the exact source coefficient system.
* A green CI build confirms the included Lean statements typecheck; a referee
  must still check their correspondence to the mathematical claims.

See https://leanprover-community.github.io/did_you_prove_it.html .

## Original evidence

Original Lean Web logs are placed under `evidence/`; those logs reflect the
environment used at the time and are not substitutes for an independently
successful `lake build` in this pinned repository.

## Historical sources

Sources under `archive/historical` are preserved verbatim but NOT imported
by the default Lake build. Some were written against older Mathlib versions.
The exact original sources cannot be assumed to compile on v4.35.0 without
porting; keep any adaptations in a separate directory and track their diff.

`archive/post-v9/TP127_V9_Unconditional_TPC_Gate.lean` was explicitly
withdrawn as an adjudication test in Turn 128. It is retained only for
transparency and is never compiled as a certification claim.
