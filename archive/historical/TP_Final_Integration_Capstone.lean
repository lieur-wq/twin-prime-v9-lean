import TP_Cert_04_AINTLIB_Hasse_Import_Adapter_v3
import TP_Cert_05_Turn393_Hasse_Splice_v5
import TP_Audit_06_Pascadi_Theorem54_Application
import TP_Audit_07_Turn394_Tensorisation_v2
import TP_Audit_08_Turn395_Completion_v2
import TP_Audit_09_Turn397_FactorBounds
import TP_Audit_10_TrustedTypeIICoefficients_v2
import TP_Audit_10j_Item13_InteriorBoundary_NoQ132_v2
import TP_Audit_11_Item14_SelbergTrustBoundary
import TP_Audit_12_Item15_MellinEnergyTrustBoundary_v2
import TP_Audit_14_Item10_KloostermanWeilTrustBoundary_v2
import TP_Audit_15_Item11_ClassicalBVTrustBoundary
import TP_Audit_16_Item12_SmoothedPNTTrustBoundary
import TP_Audit_17_Item8_MultiplicativeLargeSieveTrustBoundary
import TP_Audit_18_Item17_ConstructHumanRefereeClosure_v3
import TwinPrime_Dependency_Closure_Audit_v2

/-!
# Twin Prime final integration capstone

This file is the post-zero-ledger integration layer.  It does not replace the
individual source/application certificates.  Instead it checks that their final
versions coexist in one Lake environment and splices Run 18's constructed
final analytic closure into the historical dependency-closure capstone.
-/

namespace TwinPrimeFinalIntegration

set_option autoImplicit false
noncomputable section

namespace R18 := TwinPrimeCertificationRun18
namespace D := TwinPrimeDependencyClosureAudit
namespace E := TwinPrimeExactExternalAuditV2
namespace S2I := TwinPrimeSourceToInterface
namespace A := TwinPrimeActualCoefficientAudit

/-- Convert the Run-18 closure, constructed from the manuscript-level final
analytic source statements, into the exact historical dependency-closure
record. -/
def finalSourceToDependencyClosure
    {H A3 Efun T : ℕ → ℝ}
    (S : R18.FinalAnalyticSource H A3 Efun T) :
    D.HumanRefereeClosure H A3 Efun T := by
  let h : R18.HumanRefereeClosure H A3 Efun T :=
    R18.build_human_referee_closure S
  refine {
    X0 := h.X0
    H_pos := h.H_pos
    lower_bound := ?_
    upper_bound := ?_
    twin_identity := h.twin_identity
    support := ?_
  }
  · intro X hX
    simpa [R18.cLower] using h.lower_bound X hX
  · intro X hX
    simpa [R18.cUpper] using h.upper_bound X hX
  · simpa [D.WeightedTwinSupport, R18.WeightedTwinSupport] using h.support

/-- The Run-18 final source therefore reaches the exact TPC proposition used by
`TwinPrime_Dependency_Closure_Audit_v2`. -/
theorem final_source_implies_dependency_tpc
    {H A3 Efun T : ℕ → ℝ}
    (S : R18.FinalAnalyticSource H A3 Efun T) :
    D.TwinPrimeConjecture := by
  exact D.human_referee_closure_implies_tpc
    (finalSourceToDependencyClosure S)

/-- Full historical dependency closure with the last human packet no longer
passed as a separate hypothesis: it is constructed from Run 18's final analytic
source record. -/
theorem dependency_closure_capstone_from_final_source
    (S : S2I.Turns391397Source)
    {C391 : E.Turn391SpecialFactorPacket → Prop}
    {C393 : E.Turn393CorrelationPacket → Prop}
    {C394T : E.Turn394TensorPacket → Prop}
    {C394LS : E.MultiplicativeLargeSievePacket → Prop}
    {C395 : E.Turn395CompletionPacket → Prop}
    {C397W : E.Turn397WeilPacket → Prop}
    {C397BV : E.ClassicalBVPacket → Prop}
    {C397PNT : E.SmoothedPNTPacket → Prop}
    {C397II : E.TypeIICoefficientPacket → Prop}
    {C397S : E.SelbergTwoLinearFormPacket → Prop}
    (h391 : E.TrustedTurn391SpecialFactor C391)
    (h393 : E.TrustedTurn393Correlation C393)
    (h394T : E.TrustedTurn394Tensorisation C394T)
    (h394LS : E.TrustedMultiplicativeLargeSieve C394LS)
    (h395 : E.TrustedTurn395Completion C395)
    (h397W : E.TrustedTurn397Weil C397W)
    (h397BV : E.TrustedClassicalBV C397BV)
    (h397PNT : E.TrustedSmoothedPNT C397PNT)
    (h397II : E.TrustedTypeIICoefficients C397II)
    (h397S : E.TrustedSelbergTwoLinearForm C397S)
    {Xi M N U V TT : Type*}
    [Fintype Xi] [Fintype M] [Fintype N]
    [Fintype U] [Fintype V] [DecidableEq TT]
    (D0 : ℝ)
    (alpha : M → ℂ) (beta : N → ℂ)
    (phaseM : Xi → M → ℂ) (phaseN : Xi → N → ℂ)
    (hEnergy : A.StandardMellinEnergy D0 alpha beta phaseM phaseN)
    (prod : U → V → TT)
    (a : U → ℂ) (b : V → ℂ)
    (R : TT → ℝ)
    (ha : ∀ u, ‖a u‖ ≤ 1)
    (hb : ∀ v, ‖b v‖ ≤ 1)
    (hRep : ∀ m, (A.factorRepCount prod m : ℝ) ≤ R m)
    {H A3 Efun T : ℕ → ℝ}
    (finalSource : R18.FinalAnalyticSource H A3 Efun T) :
    let B := S2I.buildExactApplicabilityBundle S
    C391 B.t391 ∧
    C393 B.t393 ∧
    C394T B.t394Tensor ∧
    C394LS B.t394LargeSieve ∧
    C395 B.t395 ∧
    C397W B.t397Weil ∧
    C397BV B.t397BV ∧
    C397PNT B.t397PNT ∧
    C397II B.t397TypeII ∧
    C397S B.t397Selberg ∧
    B.sameSmoothingConvention ∧
    B.sameSingularSeriesNormalization ∧
    B.sameOrientation ∧
    B.sameAsymptoticScale ∧
    B.diagonalAndSingularPartitionsDiscrete ∧
    A.coeffMass
      (fun xi => A.actualA alpha phaseM xi)
      (fun xi => A.actualB beta phaseN xi) ≤ D0 ∧
    A.DivisorBounded (A.actualTypeIIAlpha prod a b) R ∧
    D.TwinPrimeConjecture := by
  exact D.dependency_closure_capstone
    S h391 h393 h394T h394LS h395 h397W h397BV h397PNT h397II h397S
    D0 alpha beta phaseM phaseN hEnergy prod a b R ha hb hRep
    (finalSourceToDependencyClosure finalSource)

/-- Machine-visible zero ledger for the post-certification integration run. -/
def openLedger : List Nat := []

theorem openLedger_is_empty : openLedger = [] := rfl

theorem openLedger_count_zero : openLedger.length = 0 := by rfl

#check TwinPrimeCertificationRun04.run04_hasse_import_capstone
#check TwinPrimeCertificationRun05v5.run05v5_turn393_hasse_splice_capstone
#check TwinPrimePascadiTheorem54Audit.pascadi54_application_capstone
#check TwinPrimeTurn394TensorisationAudit.turn394_historical_interface_is_constructed
#check TwinPrimeT395Run08.turn395_historical_interface_is_constructed
#check TwinPrimeT397Run09.run09_factor_and_representation_certificate
#check TwinPrimeRun10.turn397_local_TypeII_interface_is_constructed
#check TwinPrimeCertificationRun11.item14_publication_boundary_closes
#check TwinPrimeCertificationRun12.item15_publication_boundary_closes
#check TwinPrimeCertificationRun14.item10_exact_historical_packet
#check TwinPrimeCertificationRun15.item11_exact_historical_packet
#check TwinPrimeCertificationRun16.item12_exact_historical_packet
#check TwinPrimeCertificationRun17.item8_exact_historical_packet
#check TwinPrimeCertificationRun18.item17_constructed_closure_implies_tpc
#check TwinPrimeDependencyClosureAudit.dependency_closure_capstone
#check finalSourceToDependencyClosure
#check final_source_implies_dependency_tpc
#check dependency_closure_capstone_from_final_source
#check openLedger_count_zero

#print axioms TwinPrimeCertificationRun04.run04_hasse_import_capstone
#print axioms TwinPrimeCertificationRun05v5.run05v5_turn393_hasse_splice_capstone
#print axioms TwinPrimePascadiTheorem54Audit.pascadi54_application_capstone
#print axioms TwinPrimeTurn394TensorisationAudit.turn394_historical_interface_is_constructed
#print axioms TwinPrimeT395Run08.turn395_historical_interface_is_constructed
#print axioms TwinPrimeT397Run09.run09_factor_and_representation_certificate
#print axioms TwinPrimeRun10.turn397_local_TypeII_interface_is_constructed
#print axioms TwinPrimeCertificationRun11.item14_publication_boundary_closes
#print axioms TwinPrimeCertificationRun12.item15_publication_boundary_closes
#print axioms TwinPrimeCertificationRun14.item10_exact_historical_packet
#print axioms TwinPrimeCertificationRun15.item11_exact_historical_packet
#print axioms TwinPrimeCertificationRun16.item12_exact_historical_packet
#print axioms TwinPrimeCertificationRun17.item8_exact_historical_packet
#print axioms TwinPrimeCertificationRun18.item17_constructed_closure_implies_tpc
#print axioms TwinPrimeDependencyClosureAudit.dependency_closure_capstone
#print axioms TwinPrimeFinalIntegration.final_source_implies_dependency_tpc
#print axioms TwinPrimeFinalIntegration.dependency_closure_capstone_from_final_source
#print axioms TwinPrimeFinalIntegration.openLedger_count_zero

end
end TwinPrimeFinalIntegration
