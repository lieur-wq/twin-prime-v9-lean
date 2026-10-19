# Current dependency note - 10 October 2026 - v8 complete

This package contains only artifacts relevant to the current manuscript and rebuttal.

## Mathematical architecture

- Lower side: current audited three-piece P3 plus P4 route; manuscript uses the conservative bound `c_A > 0.7541`.
- Upper side: trace-first natural-scale variance only on the fixed interior `theta <= 0.498`; final strip paid at relative constant 8; integrated upper coefficient `0.74938`.
- Factor-M clarification: the critic's `Q^2 M^3` calculation results from bounding completed m-fibres separately and applying Cauchy in m too early. Section 10 opens the m1,m2 second moment first, applies the normalized product-kernel bound, and only then applies Cauchy to the coefficient sequence, reaching the natural `Q^2 M^2` scale.
- Terminal support: `W = A3 - E`; higher prime powers give `Rpp = o(H)`; genuine twins satisfy `T = W - Rpp`.

## Current formal evidence

The current replacement source `TP_Audit_Current_Final_Certification_2026-10-09.lean` has been run and passed cleanly. Its verdict PDF is included under `supplement/verdicts/`.

The retained source/verdict pairs for Runs 10j, 11, 15 and 16 now all have complete clean raw Lean-Web verdict PDFs in the package. The Run-16 source supplied on 10 October is byte-for-byte identical to the source already in the package, and the new verdict closes the former archival evidence caveat. The earlier truncated first Run-16 upload remains only under `supplement/provenance/`.

No new Lean audit is required by the v8 completion.

## Numerical certificates

- GP3 directed certificate: default `N=800`, reproduced exactly in the release audit.
- B4 directed certificate: run explicitly with argument `4000`; reproduced archived `upper=0.136946421369577659 < 0.1370`.

## Retired material

Historical reciprocal-square/one-completion branches, obsolete ledgers, failed/repaired Lean sources and old integration harnesses remain in `/TwinPrime/` for provenance but are excluded from this current dependency package.
