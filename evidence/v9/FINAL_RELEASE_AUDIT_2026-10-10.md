# Release audit - 10 October 2026 - v8 complete

## Manuscript

The 19-page manuscript was rebuilt from the supplied TeX using the archived BBL and visually checked after rendering. Section 10 is the intended trace-first replacement: it makes the opened-second-moment order explicit, gives the single completion prefactor, and contrasts it with the unused fibrewise `Q^2 M^3` route. No new factor-M theorem is introduced.

The main proof architecture remains the historical Turn-390--397 weighted-budget strategy: analytic strength is allocated by mass, with difficult endpoint/sliver regions paid by explicit constants rather than by demanding a uniform strongest theorem.

## Rebuttal

The revised response to critique and both standalone vector flowcharts are included under `response/`. The response retains the G1, G2 and G4 corrections and rebuts only the claim that the fibrewise factor-M loss is the route used by Section 10.

## Lean evidence

The current source `TP_Audit_Current_Final_Certification_2026-10-09.lean` has a clean supplied Lean-Web verdict. The decisive declarations elaborate and the printed axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is present.

Run 16 is now also raw-evidence complete. The user supplied a clean Lean-Web output on 10 October for `TP_Audit_16_Item12_SmoothedPNTTrustBoundary.lean`. The recovered source is byte-for-byte identical to the copy already in the package, and the output contains the expected Run-16 declarations together with three clean axiom reports containing only the standard Lean/Mathlib trio. The verdict PDF and searchable text are included under `supplement/verdicts/`. The old truncated first upload remains only in `supplement/provenance/` as historical evidence.

No further Lean rerun is required for v8.

## Numerical certificates

The P3 certificate was reproduced at its default grid `N=800`. The P4 certificate is the run with explicit command-line argument `4000`, reproducing `upper=0.136946421369577659 < 0.1370`.

## Packaging status

The README, supplement, Lean index, dependency note, manifest and SHA-256 checksums have been reconciled with the complete Run-16 evidence. Superseded analytic branches and obsolete formal harnesses remain outside the current package in the project archive.

There is no remaining raw-evidence caveat in the v8 current Lean bundle.
