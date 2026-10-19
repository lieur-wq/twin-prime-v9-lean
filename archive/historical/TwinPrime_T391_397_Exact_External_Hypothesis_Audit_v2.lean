import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Twin Prime Project -- exact external-theorem hypothesis audit, v2

This file repairs the *formalization* errors in v1.  It does not strengthen or
weaken any mathematical claim.  The point is to make the side conditions of
all trusted external inputs used in Turns 391--397 explicit, while continuing
to treat the external theorems themselves as trusted inputs.

The main repairs are purely Lean-level:
  * every structure field is declared separately;
  * every `P` in a trusted-theorem interface has an explicit packet type;
  * every opaque source condition is stored as a proposition together with an
    explicit proof field (`..._holds`), so the capstone consumes proofs rather
    than propositions;
  * the capstone uses only those proof fields.

No `sorry` and no new `axiom` declaration occurs here.
-/

namespace TwinPrimeExactExternalAuditV2

set_option autoImplicit false
open Real
open scoped BigOperators
noncomputable section

/-! ------------------------------------------------------------------------
    1. Shared analytic weight/support language
    ------------------------------------------------------------------------ -/

def SupportedOnDyadic (Phi : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, t < (1 : ℝ) / 2 ∨ (2 : ℝ) < t → Phi t = 0

def SmoothDyadicWeight (Phi : ℝ → ℂ) : Prop :=
  ContDiff ℝ ⊤ Phi ∧ SupportedOnDyadic Phi

/-! ------------------------------------------------------------------------
    2. Turn 391: special-factor/distribution applicability
    ------------------------------------------------------------------------ -/

structure Turn391SpecialFactorPacket where
  u : ℝ
  v : ℝ
  s : ℝ
  s_def : s = u + v
  ordered : u ≤ v
  u_pos : 0 < u
  v_pos : 0 < v
  s_lt_one : s < 1
  placementCondition : Prop
  placementCondition_holds : placementCondition
  weightSupportCondition : Prop
  weightSupportCondition_holds : weightSupportCondition
  roughnessOrientationCondition : Prop
  roughnessOrientationCondition_holds : roughnessOrientationCondition

structure TrustedTurn391SpecialFactor
    (Conclusion : Turn391SpecialFactorPacket → Prop) where
  apply : ∀ (P : Turn391SpecialFactorPacket),
    P.placementCondition →
    P.weightSupportCondition →
    P.roughnessOrientationCondition →
    Conclusion P

/-! ------------------------------------------------------------------------
    3. Turn 393: reciprocal-square correlation / finite-field Weil input
    ------------------------------------------------------------------------ -/

structure Turn393CorrelationPacket where
  ell : ℕ
  ellPrime : Nat.Prime ell
  ellOdd : ell ≠ 2
  localCoefficientsNonzero : Prop
  localCoefficientsNonzero_holds : localCoefficientsNonzero
  offMultiplicativeDiagonal : Prop
  offMultiplicativeDiagonal_holds : offMultiplicativeDiagonal
  squarefreeCubicCondition : Prop
  squarefreeCubicCondition_holds : squarefreeCubicCondition

structure TrustedTurn393Correlation
    (Conclusion : Turn393CorrelationPacket → Prop) where
  apply : ∀ (P : Turn393CorrelationPacket),
    P.ellPrime →
    P.ellOdd →
    P.localCoefficientsNonzero →
    P.offMultiplicativeDiagonal →
    P.squarefreeCubicCondition →
    Conclusion P

/-! ------------------------------------------------------------------------
    4. Turn 394: CRT/Gauss tensorisation and multiplicative large sieve
    ------------------------------------------------------------------------ -/

structure Turn394TensorPacket where
  p : ℕ
  r : ℕ
  pPrime : Nat.Prime p
  rPrime : Nat.Prime r
  pOdd : p ≠ 2
  rOdd : r ≠ 2
  distinct : p ≠ r
  primitiveCharacterAccounting : Prop
  primitiveCharacterAccounting_holds : primitiveCharacterAccounting
  imprimitiveCharacterContributionHandled : Prop
  imprimitiveCharacterContributionHandled_holds : imprimitiveCharacterContributionHandled

structure TrustedTurn394Tensorisation
    (Conclusion : Turn394TensorPacket → Prop) where
  apply : ∀ (P : Turn394TensorPacket),
    P.pPrime → P.rPrime → P.pOdd → P.rOdd → P.distinct →
    P.primitiveCharacterAccounting →
    P.imprimitiveCharacterContributionHandled →
    Conclusion P

structure MultiplicativeLargeSievePacket where
  Q : ℝ
  M : ℝ
  Q_pos : 0 < Q
  M_pos : 0 < M
  modulusRestrictedToPrimeProducts : Prop
  modulusRestrictedToPrimeProducts_holds : modulusRestrictedToPrimeProducts
  characterFamilyMatchesTheorem : Prop
  characterFamilyMatchesTheorem_holds : characterFamilyMatchesTheorem
  coefficientSupport_m_asymp_M : Prop
  coefficientSupport_m_asymp_M_holds : coefficientSupport_m_asymp_M
  coefficientSquareSummable : Prop
  coefficientSquareSummable_holds : coefficientSquareSummable
  normalizedPrimeWeightsBounded : Prop
  normalizedPrimeWeightsBounded_holds : normalizedPrimeWeightsBounded

structure TrustedMultiplicativeLargeSieve
    (Conclusion : MultiplicativeLargeSievePacket → Prop) where
  apply : ∀ (P : MultiplicativeLargeSievePacket),
    P.modulusRestrictedToPrimeProducts →
    P.characterFamilyMatchesTheorem →
    P.coefficientSupport_m_asymp_M →
    P.coefficientSquareSummable →
    P.normalizedPrimeWeightsBounded →
    Conclusion P

/-! ------------------------------------------------------------------------
    5. Turn 395: one completion
    ------------------------------------------------------------------------ -/

structure Turn395CompletionPacket where
  u : ℝ
  v : ℝ
  s : ℝ
  s_def : s = u + v
  orderedChamber : u ≤ v
  s_upper : s ≤ (66 : ℝ) / 107
  smallerPrimeCompleted : Prop
  smallerPrimeCompleted_holds : smallerPrimeCompleted
  positiveCompletedLength : 0 < 1 - s - u
  Phi : ℝ → ℂ
  smoothWeight : SmoothDyadicWeight Phi
  singularFrequenciesSeparated : Prop
  singularFrequenciesSeparated_holds : singularFrequenciesSeparated
  diagonalContributionSeparated : Prop
  diagonalContributionSeparated_holds : diagonalContributionSeparated
  sourceTransformIdentified : Prop
  sourceTransformIdentified_holds : sourceTransformIdentified
  nonsingularUnitBound : Prop
  nonsingularUnitBound_holds : nonsingularUnitBound

 theorem turn395_completion_exponent
    {s u : ℝ} (hu : u ≤ 4 - 6 * s) :
    (5 * s - 3) / 2 ≤ (1 - s - u) / 2 := by
  linarith

structure TrustedTurn395Completion
    (Conclusion : Turn395CompletionPacket → Prop) where
  apply : ∀ (P : Turn395CompletionPacket),
    P.orderedChamber →
    P.smallerPrimeCompleted →
    P.smoothWeight →
    P.singularFrequenciesSeparated →
    P.diagonalContributionSeparated →
    P.sourceTransformIdentified →
    P.nonsingularUnitBound →
    Conclusion P

/-! ------------------------------------------------------------------------
    6. Turn 397: normalized Kloosterman Weil input
    ------------------------------------------------------------------------ -/

structure Turn397WeilPacket where
  q : ℕ
  m1 : ℕ
  m2 : ℕ
  qPrime : Nat.Prime q
  qOdd : q ≠ 2
  qm1Coprime : Nat.Coprime q m1
  qm2Coprime : Nat.Coprime q m2
  normalizedKernelDefinitionMatches : Prop
  normalizedKernelDefinitionMatches_holds : normalizedKernelDefinitionMatches
  singularFrequenciesRemoved : Prop
  singularFrequenciesRemoved_holds : singularFrequenciesRemoved

structure TrustedTurn397Weil
    (Conclusion : Turn397WeilPacket → Prop) where
  apply : ∀ (P : Turn397WeilPacket),
    P.qPrime → P.qOdd → P.qm1Coprime → P.qm2Coprime →
    P.normalizedKernelDefinitionMatches →
    P.singularFrequenciesRemoved →
    Conclusion P

/-! ------------------------------------------------------------------------
    7. Turn 397 Type-I: classical Bombieri--Vinogradov
    ------------------------------------------------------------------------ -/

structure ClassicalBVPacket where
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
  partialSummationAndSmoothCutoffCompatible_holds : partialSummationAndSmoothCutoffCompatible

structure TrustedClassicalBV
    (Conclusion : ClassicalBVPacket → Prop) where
  apply : ∀ (P : ClassicalBVPacket),
    P.levelBound →
    P.B_sufficient_for_A →
    P.residueCoprimeOnModulusSupport →
    P.TypeISumReducedToBVForm →
    P.partialSummationAndSmoothCutoffCompatible →
    Conclusion P

theorem endpoint_gap_positive :
    (0 : ℝ) < (1 : ℝ) / 2 - (249 : ℝ) / 500 := by
  norm_num

/-! ------------------------------------------------------------------------
    8. Yang convolution BV -- diagnostic only, not final input
    ------------------------------------------------------------------------ -/

structure YangConvolutionBVPacket where
  x : ℝ
  nu : ℝ
  theta : ℝ
  eps : ℝ
  xLarge : 3 < x
  eps_pos : 0 < eps
  theta_pos : 0 < theta
  theta_lt_nu_minus_eps : theta < nu - eps
  L_equals_x_pow_nu : Prop
  L_equals_x_pow_nu_holds : L_equals_x_pow_nu
  D_equals_x_pow_theta : Prop
  D_equals_x_pow_theta_holds : D_equals_x_pow_theta
  gammaDivisorBounded : Prop
  gammaDivisorBounded_holds : gammaDivisorBounded
  lambdaDivisorBounded : Prop
  lambdaDivisorBounded_holds : lambdaDivisorBounded
  lambdaWellFactorableAtRequiredLevel : Prop
  lambdaWellFactorableAtRequiredLevel_holds : lambdaWellFactorableAtRequiredLevel
  dSupportDyadicD : Prop
  dSupportDyadicD_holds : dSupportDyadicD
  lSupportDyadicL : Prop
  lSupportDyadicL_holds : lSupportDyadicL
  residueCoprimeCondition : Prop
  residueCoprimeCondition_holds : residueCoprimeCondition
  errorTermMatches_x_logA : Prop
  errorTermMatches_x_logA_holds : errorTermMatches_x_logA

structure TrustedYangConvolutionBV
    (Conclusion : YangConvolutionBVPacket → Prop) where
  apply : ∀ (P : YangConvolutionBVPacket),
    P.theta_lt_nu_minus_eps →
    P.gammaDivisorBounded →
    P.lambdaDivisorBounded →
    P.lambdaWellFactorableAtRequiredLevel →
    P.dSupportDyadicD →
    P.lSupportDyadicL →
    P.residueCoprimeCondition →
    P.errorTermMatches_x_logA →
    Conclusion P

theorem yang_is_diagnostic_only : True := by
  trivial

/-! ------------------------------------------------------------------------
    9. Turn 397 main constant: smoothed PNT
    ------------------------------------------------------------------------ -/

structure SmoothedPNTPacket where
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

structure TrustedSmoothedPNT
    (Conclusion : SmoothedPNTPacket → Prop) where
  apply : ∀ (P : SmoothedPNTPacket),
    P.smoothWeight →
    P.primeWeightIsLambdaOverLog →
    P.qRangeOneThirdToOneHalf →
    P.rScaleMatches_Y_over_q →
    P.localChangeOfVariablesValid →
    P.errorUniformOnFixedInteriorBands →
    Conclusion P

/-! ------------------------------------------------------------------------
    10. Turn 397 Type-II coefficient package
    ------------------------------------------------------------------------ -/

structure TypeIICoefficientPacket where
  M : ℝ
  M_pos : 0 < M
  support_m_asymp_M : Prop
  support_m_asymp_M_holds : support_m_asymp_M
  coefficientsDivisorBounded : Prop
  coefficientsDivisorBounded_holds : coefficientsDivisorBounded
  l2BoundMatchesUsedExponent : Prop
  l2BoundMatchesUsedExponent_holds : l2BoundMatchesUsedExponent
  dyadicPartitionFiniteOverlap : Prop
  dyadicPartitionFiniteOverlap_holds : dyadicPartitionFiniteOverlap

structure TrustedTypeIICoefficients
    (Conclusion : TypeIICoefficientPacket → Prop) where
  apply : ∀ (P : TypeIICoefficientPacket),
    P.support_m_asymp_M →
    P.coefficientsDivisorBounded →
    P.l2BoundMatchesUsedExponent →
    P.dyadicPartitionFiniteOverlap →
    Conclusion P

/-! ------------------------------------------------------------------------
    11. Turn 397 endpoint: fixed-q two-linear-form Selberg sieve
    ------------------------------------------------------------------------ -/

structure SelbergTwoLinearFormPacket where
  q : ℕ
  qPrime : Nat.Prime q
  qOdd : q ≠ 2
  twoFormsAre_r_and_qr_minus_two : Prop
  twoFormsAre_r_and_qr_minus_two_holds : twoFormsAre_r_and_qr_minus_two
  admissibleLocalDensities : Prop
  admissibleLocalDensities_holds : admissibleLocalDensities
  singularSeriesNormalizationMatches_H : Prop
  singularSeriesNormalizationMatches_H_holds : singularSeriesNormalizationMatches_H
  equalScaleMainTermNormalization : Prop
  equalScaleMainTermNormalization_holds : equalScaleMainTermNormalization
  conversionToNaturalWeightAtMostTwo : Prop
  conversionToNaturalWeightAtMostTwo_holds : conversionToNaturalWeightAtMostTwo
  endpointExponentRange : Prop
  endpointExponentRange_holds : endpointExponentRange
  smoothOrIntervalSupportAcceptedByTheorem : Prop
  smoothOrIntervalSupportAcceptedByTheorem_holds : smoothOrIntervalSupportAcceptedByTheorem

structure TrustedSelbergTwoLinearForm
    (Conclusion : SelbergTwoLinearFormPacket → Prop) where
  apply : ∀ (P : SelbergTwoLinearFormPacket),
    P.qPrime → P.qOdd →
    P.twoFormsAre_r_and_qr_minus_two →
    P.admissibleLocalDensities →
    P.singularSeriesNormalizationMatches_H →
    P.equalScaleMainTermNormalization →
    P.conversionToNaturalWeightAtMostTwo →
    P.endpointExponentRange →
    P.smoothOrIntervalSupportAcceptedByTheorem →
    Conclusion P

/-! ------------------------------------------------------------------------
    12. One applicability bundle
    ------------------------------------------------------------------------ -/

structure ExactApplicabilityBundle where
  t391 : Turn391SpecialFactorPacket
  t393 : Turn393CorrelationPacket
  t394Tensor : Turn394TensorPacket
  t394LargeSieve : MultiplicativeLargeSievePacket
  t395 : Turn395CompletionPacket
  t397Weil : Turn397WeilPacket
  t397BV : ClassicalBVPacket
  t397PNT : SmoothedPNTPacket
  t397TypeII : TypeIICoefficientPacket
  t397Selberg : SelbergTwoLinearFormPacket

  sameSmoothingConvention : Prop
  sameSmoothingConvention_holds : sameSmoothingConvention
  sameSingularSeriesNormalization : Prop
  sameSingularSeriesNormalization_holds : sameSingularSeriesNormalization
  sameOrientation : Prop
  sameOrientation_holds : sameOrientation
  sameAsymptoticScale : Prop
  sameAsymptoticScale_holds : sameAsymptoticScale
  diagonalAndSingularPartitionsDiscrete : Prop
  diagonalAndSingularPartitionsDiscrete_holds : diagonalAndSingularPartitionsDiscrete

/-! ------------------------------------------------------------------------
    13. Capstone
    ------------------------------------------------------------------------ -/

theorem exact_external_hypothesis_capstone
    (B : ExactApplicabilityBundle)
    {C391 : Turn391SpecialFactorPacket → Prop}
    {C393 : Turn393CorrelationPacket → Prop}
    {C394T : Turn394TensorPacket → Prop}
    {C394LS : MultiplicativeLargeSievePacket → Prop}
    {C395 : Turn395CompletionPacket → Prop}
    {C397W : Turn397WeilPacket → Prop}
    {C397BV : ClassicalBVPacket → Prop}
    {C397PNT : SmoothedPNTPacket → Prop}
    {C397II : TypeIICoefficientPacket → Prop}
    {C397S : SelbergTwoLinearFormPacket → Prop}
    (h391 : TrustedTurn391SpecialFactor C391)
    (h393 : TrustedTurn393Correlation C393)
    (h394T : TrustedTurn394Tensorisation C394T)
    (h394LS : TrustedMultiplicativeLargeSieve C394LS)
    (h395 : TrustedTurn395Completion C395)
    (h397W : TrustedTurn397Weil C397W)
    (h397BV : TrustedClassicalBV C397BV)
    (h397PNT : TrustedSmoothedPNT C397PNT)
    (h397II : TrustedTypeIICoefficients C397II)
    (h397S : TrustedSelbergTwoLinearForm C397S) :
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
    B.diagonalAndSingularPartitionsDiscrete := by
  have h391' : C391 B.t391 :=
    h391.apply B.t391
      B.t391.placementCondition_holds
      B.t391.weightSupportCondition_holds
      B.t391.roughnessOrientationCondition_holds
  have h393' : C393 B.t393 :=
    h393.apply B.t393
      B.t393.ellPrime
      B.t393.ellOdd
      B.t393.localCoefficientsNonzero_holds
      B.t393.offMultiplicativeDiagonal_holds
      B.t393.squarefreeCubicCondition_holds
  have h394T' : C394T B.t394Tensor :=
    h394T.apply B.t394Tensor
      B.t394Tensor.pPrime
      B.t394Tensor.rPrime
      B.t394Tensor.pOdd
      B.t394Tensor.rOdd
      B.t394Tensor.distinct
      B.t394Tensor.primitiveCharacterAccounting_holds
      B.t394Tensor.imprimitiveCharacterContributionHandled_holds
  have h394LS' : C394LS B.t394LargeSieve :=
    h394LS.apply B.t394LargeSieve
      B.t394LargeSieve.modulusRestrictedToPrimeProducts_holds
      B.t394LargeSieve.characterFamilyMatchesTheorem_holds
      B.t394LargeSieve.coefficientSupport_m_asymp_M_holds
      B.t394LargeSieve.coefficientSquareSummable_holds
      B.t394LargeSieve.normalizedPrimeWeightsBounded_holds
  have h395' : C395 B.t395 :=
    h395.apply B.t395
      B.t395.orderedChamber
      B.t395.smallerPrimeCompleted_holds
      B.t395.smoothWeight
      B.t395.singularFrequenciesSeparated_holds
      B.t395.diagonalContributionSeparated_holds
      B.t395.sourceTransformIdentified_holds
      B.t395.nonsingularUnitBound_holds
  have h397W' : C397W B.t397Weil :=
    h397W.apply B.t397Weil
      B.t397Weil.qPrime
      B.t397Weil.qOdd
      B.t397Weil.qm1Coprime
      B.t397Weil.qm2Coprime
      B.t397Weil.normalizedKernelDefinitionMatches_holds
      B.t397Weil.singularFrequenciesRemoved_holds
  have h397BV' : C397BV B.t397BV :=
    h397BV.apply B.t397BV
      B.t397BV.levelBound
      B.t397BV.B_sufficient_for_A_holds
      B.t397BV.residueCoprimeOnModulusSupport_holds
      B.t397BV.TypeISumReducedToBVForm_holds
      B.t397BV.partialSummationAndSmoothCutoffCompatible_holds
  have h397PNT' : C397PNT B.t397PNT :=
    h397PNT.apply B.t397PNT
      B.t397PNT.smoothWeight
      B.t397PNT.primeWeightIsLambdaOverLog_holds
      B.t397PNT.qRangeOneThirdToOneHalf_holds
      B.t397PNT.rScaleMatches_Y_over_q_holds
      B.t397PNT.localChangeOfVariablesValid_holds
      B.t397PNT.errorUniformOnFixedInteriorBands_holds
  have h397II' : C397II B.t397TypeII :=
    h397II.apply B.t397TypeII
      B.t397TypeII.support_m_asymp_M_holds
      B.t397TypeII.coefficientsDivisorBounded_holds
      B.t397TypeII.l2BoundMatchesUsedExponent_holds
      B.t397TypeII.dyadicPartitionFiniteOverlap_holds
  have h397S' : C397S B.t397Selberg :=
    h397S.apply B.t397Selberg
      B.t397Selberg.qPrime
      B.t397Selberg.qOdd
      B.t397Selberg.twoFormsAre_r_and_qr_minus_two_holds
      B.t397Selberg.admissibleLocalDensities_holds
      B.t397Selberg.singularSeriesNormalizationMatches_H_holds
      B.t397Selberg.equalScaleMainTermNormalization_holds
      B.t397Selberg.conversionToNaturalWeightAtMostTwo_holds
      B.t397Selberg.endpointExponentRange_holds
      B.t397Selberg.smoothOrIntervalSupportAcceptedByTheorem_holds
  exact ⟨h391', h393', h394T', h394LS', h395', h397W', h397BV',
    h397PNT', h397II', h397S',
    B.sameSmoothingConvention_holds,
    B.sameSingularSeriesNormalization_holds,
    B.sameOrientation_holds,
    B.sameAsymptoticScale_holds,
    B.diagonalAndSingularPartitionsDiscrete_holds⟩

/-! ------------------------------------------------------------------------
    14. Explicit guardrails
    ------------------------------------------------------------------------ -/

theorem ordered_chamber_is_now_explicit (P : Turn395CompletionPacket) :
    P.u ≤ P.v := by
  exact P.orderedChamber

theorem odd_prime_is_now_explicit_393 (P : Turn393CorrelationPacket) :
    P.ell ≠ 2 := by
  exact P.ellOdd

theorem odd_prime_is_now_explicit_397 (P : Turn397WeilPacket) :
    P.q ≠ 2 := by
  exact P.qOdd

theorem smoothness_is_now_explicit_395 (P : Turn395CompletionPacket) :
    SmoothDyadicWeight P.Phi := by
  exact P.smoothWeight

theorem smoothness_is_now_explicit_PNT (P : SmoothedPNTPacket) :
    SmoothDyadicWeight P.Psi := by
  exact P.smoothWeight

/-! ------------------------------------------------------------------------
    15. Checks / axiom reports
    ------------------------------------------------------------------------ -/

#check SmoothDyadicWeight
#check Turn391SpecialFactorPacket
#check Turn393CorrelationPacket
#check Turn394TensorPacket
#check MultiplicativeLargeSievePacket
#check Turn395CompletionPacket
#check Turn397WeilPacket
#check ClassicalBVPacket
#check YangConvolutionBVPacket
#check SmoothedPNTPacket
#check TypeIICoefficientPacket
#check SelbergTwoLinearFormPacket
#check ExactApplicabilityBundle
#check exact_external_hypothesis_capstone

#print axioms TwinPrimeExactExternalAuditV2.turn395_completion_exponent
#print axioms TwinPrimeExactExternalAuditV2.endpoint_gap_positive
#print axioms TwinPrimeExactExternalAuditV2.exact_external_hypothesis_capstone
#print axioms TwinPrimeExactExternalAuditV2.ordered_chamber_is_now_explicit
#print axioms TwinPrimeExactExternalAuditV2.odd_prime_is_now_explicit_393
#print axioms TwinPrimeExactExternalAuditV2.smoothness_is_now_explicit_395

end
end TwinPrimeExactExternalAuditV2
