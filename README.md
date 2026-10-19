# Twin Prime Conjecture v9 — reproducible Lean source repository

Richard Lieu  
Department of Physics and Astronomy, University of Alabama in Huntsville

**Purpose.** Make the original manuscript v9 Lean files and relevant later
audit modules available for public review in an ordinary Lean 4/Mathlib Lake
project. This is a repository of source files and diagnostics; GitHub hosting
and a green build are not scientific peer review.

## Quick start (Mac/Linux or GitHub Codespaces)

Install `git`, `elan` (the Lean version manager), and a standard C/C++ toolchain.
From the **root** of this repository run:

```bash
lake update
lake exe cache get
lake build
lake env lean TPCV9/StatementAudit.lean | tee lean_axioms.txt
python3 scripts/check_axiom_report.py lean_axioms.txt
python3 scripts/verify_sources.py
```

`lean-toolchain` and `lakefile.lean` pin **Lean and Mathlib v4.35.0**.
**Important**: `lake-manifest.json` could not be generated in the preparing
environment (no local Lean/Lake or network access). Run `lake update` in your
own environment and **commit the generated `lake-manifest.json`**. Until
then, transitive dependencies are not fully locked, and the repository is
a prepared project, **not yet a demonstrated successful pinned build**.

GitHub Actions `.github/workflows/lean.yml` invokes a full default-target
`lake build`, explicit statement and axiom reporting, and source integrity
verification. Look under **Actions** after uploading; fix any version-related
build errors without altering v9 sources. A green check should be interpreted
exactly as explained in [REVIEW_SCOPE.md](REVIEW_SCOPE.md).

## Paths and what is included

- `TPCV9/V9/`: five original v9 Lean files (unaltered source bytes).
- `TPCV9/PostV9/`: five relevant later files (TP120 x2, TP128, TP132 x2).
- `TPCV9/StatementAudit.lean`: added display of exact theorem statements,
  Nat.Prime semantics, and standard axiom reports.
- `TPCV9.lean`: an umbrella import ensuring the default build checks *all*
  ten source files and the new statement audit.
- `manuscript/v9/`: original v9 PDF, TeX, bibliography, and compiled references.
- `evidence/`: selected original Lean Web reports and dependency notes.
- `archive/`: earlier relevant Lean sources and a withdrawn Turn127 test,
  explicitly excluded from the default build to avoid redefinitions or
  untested older-library compatibility.
- `provenance/SOURCE_SHA256.json`: checksums and input-source provenance.

## Axioms and statement identity

Lean's trusted kernel only certifies *the statements actually encoded*.
See `TPCV9/StatementAudit.lean` and `REVIEW_SCOPE.md` for the verbatim
statement of the final v9 theorem, which explicitly takes the analytic
source packet as input. We have not removed that hypothesis or substituted
a different prime predicate.

Our explicit axiom checker permits precisely
`propext`, `Classical.choice`, and `Quot.sound` for the **named declarations**.
It is not a proof of semantic fidelity to the paper.

## Publishing to GitHub

1. Create an **empty** public repository on GitHub (do not initialise README).
2. Extract the ZIP, and **upload the contents of the extracted folder**, including
   hidden `.github/workflows/lean.yml`. A ZIP uploaded as one file is not a
   GitHub source repository and will not run CI.
3. Use GitHub Actions to inspect `lake build` and axiom-report status.
4. Run `lake update` locally and commit `lake-manifest.json`, including any
   needed version-compatible changes in **separately named copies**.
5. Optional: tag a reproducible release and archive with Zenodo for a DOI.

Git command-line alternative:

```bash
git init -b main
git add .
git commit -m "Archive v9 Lean sources with reproducible Lake setup"
git remote add origin https://github.com/YOUR_ACCOUNT/YOUR_REPOSITORY.git
git push -u origin main
```

## Cautions

- No Lean binary is installed in the preparation environment: local builds
  and CI have **not** been run there.
- Historical Lean Web successes are not automatically transferable to Lean
  4.35.0; compiler API changes sometimes require explicit porting.
- The owner should add an appropriate software licence before public release.
- Ask an independent Lean/number-theory reviewer to check correspondence
  of statements with v9 and hypotheses of cited theorems.

For Lean community audit criteria see
https://leanprover-community.github.io/did_you_prove_it.html .
