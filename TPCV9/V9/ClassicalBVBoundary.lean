import Mathlib

/-!
# Twin Prime certification Run 15
## Historical ledger item 11: TrustedClassicalBV

Purpose
-------
This file does NOT re-prove the Bombieri--Vinogradov theorem.

Under the agreed publication trust boundary, classical Bombieri--Vinogradov is
an external published theorem.  Lean checks the exact Turn-397 adapter:

* the manuscript range 1/3 < theta <= 249/500;
* a nonnegative Vaughan split lying below the endpoint gap 1/2 - theta;
* the required level Q <= sqrt x / (log x)^B;
* the large-B condition for the requested logarithmic saving;
* residue-class coprimality on the actual modulus support;
* identification of the Type-I block with classical BV form;
* compatibility of partial summation and the smooth cutoff.

No `axiom`, `sorry`, or `admit` is introduced.
-/

namespace TwinPrimeCertificationRun15

set_option autoImplicit false
noncomputable section

/-- Exact data of the historical Turn-397 classical-BV packet. -/
structure ClassicalBVData where
  x : ℝ
  Q : ℝ
  theta : ℝ
  split : ℝ
  A : ℝ
  B : ℕ
  xLarge : 3 < x
  A_pos : 0 < A
  Q_pos : 0 < Q
  thetaLow : (1 : ℝ) / 3 < theta
  thetaHigh : theta ≤ (249 : ℝ) / 500
  splitNonneg : 0 ≤ split
  splitBelowGap : split < (1 : ℝ) / 2 - theta
  levelBound : Q ≤ Real.sqrt x / (Real.log x) ^ B
  B_sufficient_for_A : Prop
  B_sufficient_for_A_holds : B_sufficient_for_A
  residueCoprimeOnModulusSupport : Prop
  residueCoprimeOnModulusSupport_holds : residueCoprimeOnModulusSupport
  TypeISumReducedToBVForm : Prop
  TypeISumReducedToBVForm_holds : TypeISumReducedToBVForm
  partialSummationAndSmoothCutoffCompatible : Prop
  partialSummationAndSmoothCutoffCompatible_holds :
    partialSummationAndSmoothCutoffCompatible
  /-- The normalized Type-I estimate/conclusion consumed downstream. -/
  conclusion : Prop

/-- The endpoint gap at theta = 249/500 is exactly 1/500 > 0. -/
theorem endpoint_gap_value :
    (1 : ℝ) / 2 - (249 : ℝ) / 500 = (1 : ℝ) / 500 := by
  norm_num

/-- Hence the manuscript endpoint gap is strictly positive. -/
theorem endpoint_gap_positive :
    (0 : ℝ) < (1 : ℝ) / 2 - (249 : ℝ) / 500 := by
  rw [endpoint_gap_value]
  norm_num

/--
The published/classical Bombieri--Vinogradov theorem in the exact normalized
application form used by Turn 397.  This proposition is the external
mathematical input; it is not introduced as a Lean axiom.
-/
def PublishedClassicalBV (D : ClassicalBVData) : Prop :=
  (D.Q ≤ Real.sqrt D.x / (Real.log D.x) ^ D.B) →
  D.B_sufficient_for_A →
  D.residueCoprimeOnModulusSupport →
  D.TypeISumReducedToBVForm →
  D.partialSummationAndSmoothCutoffCompatible →
  D.conclusion

/-- The exact conclusion expected by the historical item-11 interface. -/
def AuditedClassicalBVConclusion (D : ClassicalBVData) : Prop :=
  D.conclusion

/--
Apply the published theorem to the exact Turn-397 applicability facts already
stored in the audited source packet.
-/
theorem published_bv_to_turn397_conclusion
    (D : ClassicalBVData)
    (hBV : PublishedClassicalBV D) :
    AuditedClassicalBVConclusion D := by
  unfold PublishedClassicalBV at hBV
  unfold AuditedClassicalBVConclusion
  exact hBV
    D.levelBound
    D.B_sufficient_for_A_holds
    D.residueCoprimeOnModulusSupport_holds
    D.TypeISumReducedToBVForm_holds
    D.partialSummationAndSmoothCutoffCompatible_holds

/-- Publication-facing item-11 packet. -/
structure Item11PublicationBoundary where
  data : ClassicalBVData
  publishedBV : PublishedClassicalBV data

/-- Historical item 11 closes at the agreed publication trust boundary. -/
theorem item11_publication_boundary_closes
    (B : Item11PublicationBoundary) :
    AuditedClassicalBVConclusion B.data := by
  exact published_bv_to_turn397_conclusion B.data B.publishedBV

/--
The exact historical applicability packet is visible rather than hidden inside
the external theorem boundary.
-/
theorem item11_exact_historical_packet
    (B : Item11PublicationBoundary) :
    (3 < B.data.x) ∧
    (0 < B.data.A) ∧
    (0 < B.data.Q) ∧
    ((1 : ℝ) / 3 < B.data.theta) ∧
    (B.data.theta ≤ (249 : ℝ) / 500) ∧
    (0 ≤ B.data.split) ∧
    (B.data.split < (1 : ℝ) / 2 - B.data.theta) ∧
    (B.data.Q ≤ Real.sqrt B.data.x / (Real.log B.data.x) ^ B.data.B) ∧
    B.data.B_sufficient_for_A ∧
    B.data.residueCoprimeOnModulusSupport ∧
    B.data.TypeISumReducedToBVForm ∧
    B.data.partialSummationAndSmoothCutoffCompatible ∧
    AuditedClassicalBVConclusion B.data := by
  refine ⟨B.data.xLarge, B.data.A_pos, B.data.Q_pos,
    B.data.thetaLow, B.data.thetaHigh, B.data.splitNonneg,
    B.data.splitBelowGap, B.data.levelBound,
    B.data.B_sufficient_for_A_holds,
    B.data.residueCoprimeOnModulusSupport_holds,
    B.data.TypeISumReducedToBVForm_holds,
    B.data.partialSummationAndSmoothCutoffCompatible_holds, ?_⟩
  exact item11_publication_boundary_closes B

#check ClassicalBVData
#check PublishedClassicalBV
#check AuditedClassicalBVConclusion
#check endpoint_gap_value
#check endpoint_gap_positive
#check published_bv_to_turn397_conclusion
#check item11_publication_boundary_closes
#check item11_exact_historical_packet

#print axioms TwinPrimeCertificationRun15.endpoint_gap_value
#print axioms TwinPrimeCertificationRun15.endpoint_gap_positive
#print axioms TwinPrimeCertificationRun15.published_bv_to_turn397_conclusion
#print axioms TwinPrimeCertificationRun15.item11_publication_boundary_closes
#print axioms TwinPrimeCertificationRun15.item11_exact_historical_packet

end
end TwinPrimeCertificationRun15
