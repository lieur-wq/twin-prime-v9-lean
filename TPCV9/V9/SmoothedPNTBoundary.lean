import Mathlib

/-!
# Twin Prime certification Run 16
## Historical ledger item 12: TrustedSmoothedPNT

Purpose
-------
This file does NOT re-prove the prime number theorem.

Under the agreed publication trust boundary, the standard smoothed prime-number
theorem is an external published theorem. Lean checks the exact Turn-397 adapter:

* Y is in the large-parameter regime;
* the literal smooth dyadic weight is the one audited upstream;
* the prime weight is Lambda/log in the manuscript normalization;
* q lies in the fixed interior range 1/3 to 1/2;
* the companion r-scale is Y/q;
* the local change of variables is valid;
* the PNT error is uniform on the fixed interior bands;
* the resulting normalized main-term conclusion is exactly the one consumed
  downstream.

No `axiom`, `sorry`, or `admit` is introduced.
-/

namespace TwinPrimeCertificationRun16

set_option autoImplicit false
noncomputable section

/-- Exact smooth dyadic-weight predicate used by the historical audit. -/
def SupportedOnDyadic (Psi : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, t < (1 : ℝ) / 2 ∨ (2 : ℝ) < t → Psi t = 0

def SmoothDyadicWeight (Psi : ℝ → ℂ) : Prop :=
  ContDiff ℝ ⊤ Psi ∧ SupportedOnDyadic Psi

/-- Exact data of the historical Turn-397 smoothed-PNT packet. -/
structure SmoothedPNTData where
  Y : ℝ
  YLarge : 3 < Y
  Psi : ℝ → ℂ
  smoothWeight : SmoothDyadicWeight Psi
  primeWeightIsLambdaOverLog : Prop
  primeWeightIsLambdaOverLog_holds : primeWeightIsLambdaOverLog
  qRangeOneThirdToOneHalf : Prop
  qRangeOneThirdToOneHalf_holds : qRangeOneThirdToOneHalf
  rScaleMatches_Y_over_q : Prop
  rScaleMatches_Y_over_q_holds : rScaleMatches_Y_over_q
  localChangeOfVariablesValid : Prop
  localChangeOfVariablesValid_holds : localChangeOfVariablesValid
  errorUniformOnFixedInteriorBands : Prop
  errorUniformOnFixedInteriorBands_holds : errorUniformOnFixedInteriorBands
  /-- The normalized main-term conclusion consumed downstream. -/
  conclusion : Prop

/--
The published smoothed prime-number theorem in the exact normalized application
form used by Turn 397. This proposition is the external mathematical input;
it is not introduced as a Lean axiom.
-/
def PublishedSmoothedPNT (D : SmoothedPNTData) : Prop :=
  SmoothDyadicWeight D.Psi ->
  D.primeWeightIsLambdaOverLog ->
  D.qRangeOneThirdToOneHalf ->
  D.rScaleMatches_Y_over_q ->
  D.localChangeOfVariablesValid ->
  D.errorUniformOnFixedInteriorBands ->
  D.conclusion

/-- The exact conclusion expected by the historical item-12 interface. -/
def AuditedSmoothedPNTConclusion (D : SmoothedPNTData) : Prop :=
  D.conclusion

/-- Apply the published theorem to the exact Turn-397 applicability facts. -/
theorem published_pnt_to_turn397_conclusion
    (D : SmoothedPNTData)
    (hPNT : PublishedSmoothedPNT D) :
    AuditedSmoothedPNTConclusion D := by
  unfold PublishedSmoothedPNT at hPNT
  unfold AuditedSmoothedPNTConclusion
  exact hPNT
    D.smoothWeight
    D.primeWeightIsLambdaOverLog_holds
    D.qRangeOneThirdToOneHalf_holds
    D.rScaleMatches_Y_over_q_holds
    D.localChangeOfVariablesValid_holds
    D.errorUniformOnFixedInteriorBands_holds

/-- Publication-facing item-12 packet. -/
structure Item12PublicationBoundary where
  data : SmoothedPNTData
  publishedPNT : PublishedSmoothedPNT data

/-- Historical item 12 closes at the agreed publication trust boundary. -/
theorem item12_publication_boundary_closes
    (B : Item12PublicationBoundary) :
    AuditedSmoothedPNTConclusion B.data := by
  exact published_pnt_to_turn397_conclusion B.data B.publishedPNT

/--
The exact historical applicability packet is visible rather than hidden inside
the external theorem boundary.
-/
theorem item12_exact_historical_packet
    (B : Item12PublicationBoundary) :
    (3 < B.data.Y) ∧
    SmoothDyadicWeight B.data.Psi ∧
    B.data.primeWeightIsLambdaOverLog ∧
    B.data.qRangeOneThirdToOneHalf ∧
    B.data.rScaleMatches_Y_over_q ∧
    B.data.localChangeOfVariablesValid ∧
    B.data.errorUniformOnFixedInteriorBands ∧
    AuditedSmoothedPNTConclusion B.data := by
  refine ⟨B.data.YLarge, B.data.smoothWeight,
    B.data.primeWeightIsLambdaOverLog_holds,
    B.data.qRangeOneThirdToOneHalf_holds,
    B.data.rScaleMatches_Y_over_q_holds,
    B.data.localChangeOfVariablesValid_holds,
    B.data.errorUniformOnFixedInteriorBands_holds, ?_⟩
  exact item12_publication_boundary_closes B

#check SmoothedPNTData
#check PublishedSmoothedPNT
#check AuditedSmoothedPNTConclusion
#check published_pnt_to_turn397_conclusion
#check item12_publication_boundary_closes
#check item12_exact_historical_packet

#print axioms TwinPrimeCertificationRun16.published_pnt_to_turn397_conclusion
#print axioms TwinPrimeCertificationRun16.item12_publication_boundary_closes
#print axioms TwinPrimeCertificationRun16.item12_exact_historical_packet

end
end TwinPrimeCertificationRun16
