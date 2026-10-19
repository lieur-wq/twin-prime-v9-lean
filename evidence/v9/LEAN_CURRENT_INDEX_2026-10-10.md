# Lean current evidence index - 10 October 2026 - v8 complete

## Retained current sources

1. `TP_Audit_10j_Item13_InteriorBoundary_NoQ132_v2.lean`
   - raw verdict: `LeanWebVerdict_TP_Audit_10j_v2_CLEAN_PASS_2026-10-04.pdf`
   - clean: no error / unsolved goal / `sorryAx`.
2. `TP_Audit_11_Item14_SelbergTrustBoundary.lean`
   - raw verdict: `LeanWebVerdict_TP_Audit_11_CLEAN_PASS_2026-10-04.pdf`
   - clean: no error / unsolved goal / `sorryAx`.
3. `TP_Audit_15_Item11_ClassicalBVTrustBoundary.lean`
   - raw verdict: `LeanWebVerdict_TP_Audit_15_Item11_CLEAN_PASS_2026-10-04.pdf`
   - clean: no error / unsolved goal / `sorryAx`.
4. `TP_Audit_16_Item12_SmoothedPNTTrustBoundary.lean`
   - raw verdict: `LeanWebVerdict_TP_Audit_16_Item12_CLEAN_PASS_2026-10-10.pdf`;
   - the source is byte-for-byte identical to the recovered historical Run-16 source;
   - decisive axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`;
   - the old truncated first upload is retained only under `supplement/provenance/`.
5. `TP_Audit_Current_Final_Certification_2026-10-09.lean`
   - raw verdict: `LeanWebVerdict_TP_Audit_Current_Final_Certification_CLEAN_PASS_2026-10-09.pdf`;
   - roles: current Kloosterman/Weil product-kernel interface and current terminal closure with explicit higher-prime-power subtraction;
   - status: clean Lean-Web pass; decisive axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`.

The obsolete historical Run-14 and Run-18 verdicts are not current evidence. No fresh Lean rerun is required by the completed v8 package.
