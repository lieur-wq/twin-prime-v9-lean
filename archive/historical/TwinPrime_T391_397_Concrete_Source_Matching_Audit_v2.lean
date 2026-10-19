import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Twin Prime Project -- exact external-theorem hypothesis audit, v3

This file repairs the remaining *formalization* errors in v2.  It does not strengthen or
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
    Nat.Prime P.ell →
    P.ell ≠ 2 →
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
    Nat.Prime P.p → Nat.Prime P.r → P.p ≠ 2 → P.r ≠ 2 → P.p ≠ P.r →
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
    P.u ≤ P.v →
    P.s = P.u + P.v →
    P.s ≤ (66 : ℝ) / 107 →
    0 < 1 - P.s - P.u →
    P.smallerPrimeCompleted →
    SmoothDyadicWeight P.Phi →
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
    Nat.Prime P.q → P.q ≠ 2 → Nat.Coprime P.q P.m1 → Nat.Coprime P.q P.m2 →
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
    3 < P.x →
    0 < P.A →
    0 < P.Q →
    (1 : ℝ) / 3 < P.theta →
    P.theta ≤ (249 : ℝ) / 500 →
    0 ≤ P.split →
    P.split < (1 : ℝ) / 2 - P.theta →
    P.Q ≤ Real.sqrt P.x / (Real.log P.x) ^ P.B →
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
    3 < P.x →
    0 < P.eps →
    0 < P.theta →
    P.theta < P.nu - P.eps →
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
    3 < P.Y →
    SmoothDyadicWeight P.Psi →
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
    Nat.Prime P.q → P.q ≠ 2 →
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
      B.t395.s_def
      B.t395.s_upper
      B.t395.positiveCompletedLength
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
      B.t397BV.xLarge
      B.t397BV.A_pos
      B.t397BV.Q_pos
      B.t397BV.thetaLow
      B.t397BV.thetaHigh
      B.t397BV.splitNonneg
      B.t397BV.splitBelowGap
      B.t397BV.levelBound
      B.t397BV.B_sufficient_for_A_holds
      B.t397BV.residueCoprimeOnModulusSupport_holds
      B.t397BV.TypeISumReducedToBVForm_holds
      B.t397BV.partialSummationAndSmoothCutoffCompatible_holds
  have h397PNT' : C397PNT B.t397PNT :=
    h397PNT.apply B.t397PNT
      B.t397PNT.YLarge
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

/-!
===============================================================================
SOURCE-TO-INTERFACE MATCHING LAYER
===============================================================================

The preceding v3 layer proved that an ExactApplicabilityBundle is sufficient for
all trusted external theorem applications.  The purpose of this additional layer
is narrower and more concrete: transcribe the actual variables, ranges and
source statements of Turns 391--397, derive every elementary side condition that
can be derived inside Lean, and construct an ExactApplicabilityBundle from those
source facts.

This is intentionally *not* a re-proof of the external theorems.  It also does
not pretend that Lean can parse a PDF.  Instead, each non-elementary source
statement is named explicitly by the turn/equation role it serves, while the
arithmetic/range/order/parity consequences are proved here.

No `sorry` and no new `axiom` declaration occurs in this layer.
-/

namespace TwinPrimeSourceToInterface

open TwinPrimeExactExternalAuditV2
open Real
open scoped BigOperators
set_option autoImplicit false
noncomputable section

/-! ------------------------------------------------------------------------
    A. Literal numerical constants appearing in Turns 391--397
    ------------------------------------------------------------------------ -/

def sourceSTop : ℝ := (66 : ℝ) / 107

def sourceThetaCut : ℝ := (249 : ℝ) / 500

def sourceVaughanSplit : ℝ := (1 : ℝ) / 1000

def betaRichert : ℝ := (39 : ℝ) / 500

def gammaRichert : ℝ := (159 : ℝ) / 500

lemma sourceSTop_lt_one : sourceSTop < 1 := by
  norm_num [sourceSTop]

lemma sourceThetaCut_lt_half : sourceThetaCut < (1 : ℝ) / 2 := by
  norm_num [sourceThetaCut]

lemma sourceVaughanSplit_nonneg : 0 ≤ sourceVaughanSplit := by
  norm_num [sourceVaughanSplit]

lemma sourceVaughanSplit_below_endpoint_gap :
    sourceVaughanSplit < (1 : ℝ) / 2 - sourceThetaCut := by
  norm_num [sourceVaughanSplit, sourceThetaCut]

/-! ------------------------------------------------------------------------
    B. Source statements transcribed from Turns 391--397

Only statements which are not elementary consequences of the displayed
ranges/equalities are retained as source facts.  Their names record exactly
where they enter the proof.
    ------------------------------------------------------------------------ -/

structure Turns391397Source where
  /- Turn 391/395 exponent geometry. -/
  u : ℝ
  v : ℝ
  s : ℝ
  s_eq : s = u + v
  ordered : u ≤ v
  u_pos : 0 < u
  v_pos : 0 < v
  s_top : s ≤ sourceSTop

  /- Turn 391, Eq. (5845) range used to verify the Richert-weight support. -/
  u_lower_5845 : (25 : ℝ) / 107 ≤ u
  u_upper_5845 : u ≤ (5 : ℝ) / 16

  /- Turn 391/Pascadi application on the cells to which that theorem is used. -/
  t391PlacementCondition : Prop
  t391PlacementCondition_holds : t391PlacementCondition
  t391RoughnessOrientation : Prop
  t391RoughnessOrientation_holds : t391RoughnessOrientation

  /- Turn 393 local correlation data. -/
  ell : ℕ
  ellPrime : Nat.Prime ell
  ell_gt_two : 2 < ell
  t393LocalCoefficientsNonzero : Prop
  t393LocalCoefficientsNonzero_holds : t393LocalCoefficientsNonzero
  t393OffMultiplicativeDiagonal : Prop
  t393OffMultiplicativeDiagonal_holds : t393OffMultiplicativeDiagonal
  t393SquarefreeCubic : Prop
  t393SquarefreeCubic_holds : t393SquarefreeCubic

  /- Turn 394 prime-product CRT/tensorisation data. -/
  p : ℕ
  r : ℕ
  pPrime : Nat.Prime p
  rPrime : Nat.Prime r
  p_gt_two : 2 < p
  r_gt_two : 2 < r
  p_ne_r : p ≠ r
  t394PrimitiveCharacterAccounting : Prop
  t394PrimitiveCharacterAccounting_holds : t394PrimitiveCharacterAccounting
  t394ImprimitiveContributionHandled : Prop
  t394ImprimitiveContributionHandled_holds : t394ImprimitiveContributionHandled

  /- Turn 394 multiplicative large-sieve block, Eqs. (5931)--(5932). -/
  Q394 : ℝ
  M394 : ℝ
  Q394_pos : 0 < Q394
  M394_pos : 0 < M394
  t394ModuliArePrimeProducts : Prop
  t394ModuliArePrimeProducts_holds : t394ModuliArePrimeProducts
  t394CharacterFamilyMatches : Prop
  t394CharacterFamilyMatches_holds : t394CharacterFamilyMatches
  t394CoefficientSupport : Prop
  t394CoefficientSupport_holds : t394CoefficientSupport
  t394CoefficientSquareSummable : Prop
  t394CoefficientSquareSummable_holds : t394CoefficientSquareSummable
  t394NormalizedPrimeWeightsBounded : Prop
  t394NormalizedPrimeWeightsBounded_holds : t394NormalizedPrimeWeightsBounded

  /- Turn 395 one-completion source, Eqs. (5944)--(5948). -/
  Phi395 : ℝ → ℂ
  Phi395_smooth : SmoothDyadicWeight Phi395
  t395SingularFrequenciesSeparated : Prop
  t395SingularFrequenciesSeparated_holds : t395SingularFrequenciesSeparated
  t395DiagonalSeparated : Prop
  t395DiagonalSeparated_holds : t395DiagonalSeparated
  t395SourceTransformIdentified : Prop
  t395SourceTransformIdentified_holds : t395SourceTransformIdentified
  t395NonsingularUnitBound : Prop
  t395NonsingularUnitBound_holds : t395NonsingularUnitBound

  /- Turn 397 normalized Kloosterman/Weil input, Eqs. (5999)--(6001). -/
  q397 : ℕ
  m1 : ℕ
  m2 : ℕ
  q397Prime : Nat.Prime q397
  q397_gt_two : 2 < q397
  q397_coprime_m1 : Nat.Coprime q397 m1
  q397_coprime_m2 : Nat.Coprime q397 m2
  t397NormalizedKernelMatches : Prop
  t397NormalizedKernelMatches_holds : t397NormalizedKernelMatches
  t397SingularFrequenciesRemoved : Prop
  t397SingularFrequenciesRemoved_holds : t397SingularFrequenciesRemoved

  /- Turn 397 Type-I/BV interior, Eq. (6005): 1/3 < theta <= 0.498. -/
  x397 : ℝ
  theta397 : ℝ
  A397 : ℝ
  B397 : ℕ
  Q397 : ℝ
  x397_large : 3 < x397
  A397_pos : 0 < A397
  Q397_pos : 0 < Q397
  theta397_low : (1 : ℝ) / 3 < theta397
  theta397_high : theta397 ≤ sourceThetaCut
  t397BVLevelEventually : Q397 ≤ Real.sqrt x397 / (Real.log x397) ^ B397
  t397BEnoughForA : Prop
  t397BEnoughForA_holds : t397BEnoughForA
  t397ResidueCoprime : Prop
  t397ResidueCoprime_holds : t397ResidueCoprime
  t397TypeIReducedToBV : Prop
  t397TypeIReducedToBV_holds : t397TypeIReducedToBV
  t397PartialSummationSmoothCompatible : Prop
  t397PartialSummationSmoothCompatible_holds : t397PartialSummationSmoothCompatible

  /- Turn 397 smoothed PNT/main constant, Eqs. (5981)--(5988). -/
  Y397 : ℝ
  Y397_large : 3 < Y397
  Psi397 : ℝ → ℂ
  Psi397_smooth : SmoothDyadicWeight Psi397
  t397PrimeWeightLambdaOverLog : Prop
  t397PrimeWeightLambdaOverLog_holds : t397PrimeWeightLambdaOverLog
  t397QRangeOneThirdToHalf : Prop
  t397QRangeOneThirdToHalf_holds : t397QRangeOneThirdToHalf
  t397RScaleYOverQ : Prop
  t397RScaleYOverQ_holds : t397RScaleYOverQ
  t397LocalChangeVariables : Prop
  t397LocalChangeVariables_holds : t397LocalChangeVariables
  t397PNTUniformInterior : Prop
  t397PNTUniformInterior_holds : t397PNTUniformInterior

  /- Turn 397 Type-II coefficients, Eqs. (5999)--(6004). -/
  M397 : ℝ
  M397_pos : 0 < M397
  t397MSupport : Prop
  t397MSupport_holds : t397MSupport
  t397CoefficientsDivisorBounded : Prop
  t397CoefficientsDivisorBounded_holds : t397CoefficientsDivisorBounded
  t397L2Bound : Prop
  t397L2Bound_holds : t397L2Bound
  t397DyadicFiniteOverlap : Prop
  t397DyadicFiniteOverlap_holds : t397DyadicFiniteOverlap

  /- Turn 397 endpoint Selberg strip, Eqs. (6007)--(6011). -/
  qSelberg : ℕ
  qSelbergPrime : Nat.Prime qSelberg
  qSelberg_gt_two : 2 < qSelberg
  t397Forms_r_qr_minus_two : Prop
  t397Forms_r_qr_minus_two_holds : t397Forms_r_qr_minus_two
  t397AdmissibleLocalDensities : Prop
  t397AdmissibleLocalDensities_holds : t397AdmissibleLocalDensities
  t397SingularSeriesMatchesH : Prop
  t397SingularSeriesMatchesH_holds : t397SingularSeriesMatchesH
  t397EqualScaleNormalization : Prop
  t397EqualScaleNormalization_holds : t397EqualScaleNormalization
  t397NaturalWeightConversionAtMostTwo : Prop
  t397NaturalWeightConversionAtMostTwo_holds : t397NaturalWeightConversionAtMostTwo
  t397EndpointExponentRange : Prop
  t397EndpointExponentRange_holds : t397EndpointExponentRange
  t397SelbergSupportAccepted : Prop
  t397SelbergSupportAccepted_holds : t397SelbergSupportAccepted

  /- Cross-turn identity of conventions. -/
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
    C. Elementary consequences proved from the displayed source equations
    ------------------------------------------------------------------------ -/

lemma source_s_lt_one (S : Turns391397Source) : S.s < 1 := by
  exact lt_of_le_of_lt S.s_top sourceSTop_lt_one

lemma source_ell_odd (S : Turns391397Source) : S.ell ≠ 2 := by
  have h : 2 < S.ell := S.ell_gt_two
  omega

lemma source_p_odd (S : Turns391397Source) : S.p ≠ 2 := by
  have h : 2 < S.p := S.p_gt_two
  omega

lemma source_r_odd (S : Turns391397Source) : S.r ≠ 2 := by
  have h : 2 < S.r := S.r_gt_two
  omega

lemma source_q397_odd (S : Turns391397Source) : S.q397 ≠ 2 := by
  have h : 2 < S.q397 := S.q397_gt_two
  omega

lemma source_qSelberg_odd (S : Turns391397Source) : S.qSelberg ≠ 2 := by
  have h : 2 < S.qSelberg := S.qSelberg_gt_two
  omega

lemma source_completion_length_positive (S : Turns391397Source) :
    0 < 1 - S.s - S.u := by
  have h2u : 2 * S.u ≤ S.s := by
    linarith [S.s_eq, S.ordered]
  have hs : S.s ≤ (66 : ℝ) / 107 := by
    simpa [sourceSTop] using S.s_top
  nlinarith

lemma source_turn391_weight_support (S : Turns391397Source) :
    betaRichert ≤ S.u ∧ S.u ≤ gammaRichert ∧ gammaRichert < 1 - S.s := by
  have h1 : betaRichert ≤ (25 : ℝ) / 107 := by
    norm_num [betaRichert]
  have h2 : (5 : ℝ) / 16 ≤ gammaRichert := by
    norm_num [gammaRichert]
  have h3 : gammaRichert < 1 - sourceSTop := by
    norm_num [gammaRichert, sourceSTop]
  constructor
  · linarith [S.u_lower_5845, h1]
  constructor
  · linarith [S.u_upper_5845, h2]
  · linarith [S.s_top, h3]

lemma source_BV_split_nonnegative : 0 ≤ sourceVaughanSplit := by
  exact sourceVaughanSplit_nonneg

lemma source_BV_split_below_gap (S : Turns391397Source) :
    sourceVaughanSplit < (1 : ℝ) / 2 - S.theta397 := by
  have hcut : S.theta397 ≤ sourceThetaCut := S.theta397_high
  have hgap : sourceVaughanSplit < (1 : ℝ) / 2 - sourceThetaCut :=
    sourceVaughanSplit_below_endpoint_gap
  linarith

/-! ------------------------------------------------------------------------
    D. Construct the exact v3 applicability packets from Turns 391--397
    ------------------------------------------------------------------------ -/

def buildExactApplicabilityBundle (S : Turns391397Source) : ExactApplicabilityBundle where
  t391 := {
    u := S.u
    v := S.v
    s := S.s
    s_def := S.s_eq
    ordered := S.ordered
    u_pos := S.u_pos
    v_pos := S.v_pos
    s_lt_one := source_s_lt_one S
    placementCondition := S.t391PlacementCondition
    placementCondition_holds := S.t391PlacementCondition_holds
    weightSupportCondition :=
      betaRichert ≤ S.u ∧ S.u ≤ gammaRichert ∧ gammaRichert < 1 - S.s
    weightSupportCondition_holds := source_turn391_weight_support S
    roughnessOrientationCondition := S.t391RoughnessOrientation
    roughnessOrientationCondition_holds := S.t391RoughnessOrientation_holds
  }

  t393 := {
    ell := S.ell
    ellPrime := S.ellPrime
    ellOdd := source_ell_odd S
    localCoefficientsNonzero := S.t393LocalCoefficientsNonzero
    localCoefficientsNonzero_holds := S.t393LocalCoefficientsNonzero_holds
    offMultiplicativeDiagonal := S.t393OffMultiplicativeDiagonal
    offMultiplicativeDiagonal_holds := S.t393OffMultiplicativeDiagonal_holds
    squarefreeCubicCondition := S.t393SquarefreeCubic
    squarefreeCubicCondition_holds := S.t393SquarefreeCubic_holds
  }

  t394Tensor := {
    p := S.p
    r := S.r
    pPrime := S.pPrime
    rPrime := S.rPrime
    pOdd := source_p_odd S
    rOdd := source_r_odd S
    distinct := S.p_ne_r
    primitiveCharacterAccounting := S.t394PrimitiveCharacterAccounting
    primitiveCharacterAccounting_holds := S.t394PrimitiveCharacterAccounting_holds
    imprimitiveCharacterContributionHandled := S.t394ImprimitiveContributionHandled
    imprimitiveCharacterContributionHandled_holds := S.t394ImprimitiveContributionHandled_holds
  }

  t394LargeSieve := {
    Q := S.Q394
    M := S.M394
    Q_pos := S.Q394_pos
    M_pos := S.M394_pos
    modulusRestrictedToPrimeProducts := S.t394ModuliArePrimeProducts
    modulusRestrictedToPrimeProducts_holds := S.t394ModuliArePrimeProducts_holds
    characterFamilyMatchesTheorem := S.t394CharacterFamilyMatches
    characterFamilyMatchesTheorem_holds := S.t394CharacterFamilyMatches_holds
    coefficientSupport_m_asymp_M := S.t394CoefficientSupport
    coefficientSupport_m_asymp_M_holds := S.t394CoefficientSupport_holds
    coefficientSquareSummable := S.t394CoefficientSquareSummable
    coefficientSquareSummable_holds := S.t394CoefficientSquareSummable_holds
    normalizedPrimeWeightsBounded := S.t394NormalizedPrimeWeightsBounded
    normalizedPrimeWeightsBounded_holds := S.t394NormalizedPrimeWeightsBounded_holds
  }

  t395 := {
    u := S.u
    v := S.v
    s := S.s
    s_def := S.s_eq
    orderedChamber := S.ordered
    s_upper := by simpa [sourceSTop] using S.s_top
    smallerPrimeCompleted := S.u ≤ S.v
    smallerPrimeCompleted_holds := S.ordered
    positiveCompletedLength := source_completion_length_positive S
    Phi := S.Phi395
    smoothWeight := S.Phi395_smooth
    singularFrequenciesSeparated := S.t395SingularFrequenciesSeparated
    singularFrequenciesSeparated_holds := S.t395SingularFrequenciesSeparated_holds
    diagonalContributionSeparated := S.t395DiagonalSeparated
    diagonalContributionSeparated_holds := S.t395DiagonalSeparated_holds
    sourceTransformIdentified := S.t395SourceTransformIdentified
    sourceTransformIdentified_holds := S.t395SourceTransformIdentified_holds
    nonsingularUnitBound := S.t395NonsingularUnitBound
    nonsingularUnitBound_holds := S.t395NonsingularUnitBound_holds
  }

  t397Weil := {
    q := S.q397
    m1 := S.m1
    m2 := S.m2
    qPrime := S.q397Prime
    qOdd := source_q397_odd S
    qm1Coprime := S.q397_coprime_m1
    qm2Coprime := S.q397_coprime_m2
    normalizedKernelDefinitionMatches := S.t397NormalizedKernelMatches
    normalizedKernelDefinitionMatches_holds := S.t397NormalizedKernelMatches_holds
    singularFrequenciesRemoved := S.t397SingularFrequenciesRemoved
    singularFrequenciesRemoved_holds := S.t397SingularFrequenciesRemoved_holds
  }

  t397BV := {
    x := S.x397
    Q := S.Q397
    theta := S.theta397
    split := sourceVaughanSplit
    A := S.A397
    B := S.B397
    xLarge := S.x397_large
    A_pos := S.A397_pos
    Q_pos := S.Q397_pos
    thetaLow := S.theta397_low
    thetaHigh := by simpa [sourceThetaCut] using S.theta397_high
    splitNonneg := source_BV_split_nonnegative
    splitBelowGap := source_BV_split_below_gap S
    levelBound := S.t397BVLevelEventually
    B_sufficient_for_A := S.t397BEnoughForA
    B_sufficient_for_A_holds := S.t397BEnoughForA_holds
    residueCoprimeOnModulusSupport := S.t397ResidueCoprime
    residueCoprimeOnModulusSupport_holds := S.t397ResidueCoprime_holds
    TypeISumReducedToBVForm := S.t397TypeIReducedToBV
    TypeISumReducedToBVForm_holds := S.t397TypeIReducedToBV_holds
    partialSummationAndSmoothCutoffCompatible := S.t397PartialSummationSmoothCompatible
    partialSummationAndSmoothCutoffCompatible_holds := S.t397PartialSummationSmoothCompatible_holds
  }

  t397PNT := {
    Y := S.Y397
    YLarge := S.Y397_large
    Psi := S.Psi397
    smoothWeight := S.Psi397_smooth
    primeWeightIsLambdaOverLog := S.t397PrimeWeightLambdaOverLog
    primeWeightIsLambdaOverLog_holds := S.t397PrimeWeightLambdaOverLog_holds
    qRangeOneThirdToOneHalf := S.t397QRangeOneThirdToHalf
    qRangeOneThirdToOneHalf_holds := S.t397QRangeOneThirdToHalf_holds
    rScaleMatches_Y_over_q := S.t397RScaleYOverQ
    rScaleMatches_Y_over_q_holds := S.t397RScaleYOverQ_holds
    localChangeOfVariablesValid := S.t397LocalChangeVariables
    localChangeOfVariablesValid_holds := S.t397LocalChangeVariables_holds
    errorUniformOnFixedInteriorBands := S.t397PNTUniformInterior
    errorUniformOnFixedInteriorBands_holds := S.t397PNTUniformInterior_holds
  }

  t397TypeII := {
    M := S.M397
    M_pos := S.M397_pos
    support_m_asymp_M := S.t397MSupport
    support_m_asymp_M_holds := S.t397MSupport_holds
    coefficientsDivisorBounded := S.t397CoefficientsDivisorBounded
    coefficientsDivisorBounded_holds := S.t397CoefficientsDivisorBounded_holds
    l2BoundMatchesUsedExponent := S.t397L2Bound
    l2BoundMatchesUsedExponent_holds := S.t397L2Bound_holds
    dyadicPartitionFiniteOverlap := S.t397DyadicFiniteOverlap
    dyadicPartitionFiniteOverlap_holds := S.t397DyadicFiniteOverlap_holds
  }

  t397Selberg := {
    q := S.qSelberg
    qPrime := S.qSelbergPrime
    qOdd := source_qSelberg_odd S
    twoFormsAre_r_and_qr_minus_two := S.t397Forms_r_qr_minus_two
    twoFormsAre_r_and_qr_minus_two_holds := S.t397Forms_r_qr_minus_two_holds
    admissibleLocalDensities := S.t397AdmissibleLocalDensities
    admissibleLocalDensities_holds := S.t397AdmissibleLocalDensities_holds
    singularSeriesNormalizationMatches_H := S.t397SingularSeriesMatchesH
    singularSeriesNormalizationMatches_H_holds := S.t397SingularSeriesMatchesH_holds
    equalScaleMainTermNormalization := S.t397EqualScaleNormalization
    equalScaleMainTermNormalization_holds := S.t397EqualScaleNormalization_holds
    conversionToNaturalWeightAtMostTwo := S.t397NaturalWeightConversionAtMostTwo
    conversionToNaturalWeightAtMostTwo_holds := S.t397NaturalWeightConversionAtMostTwo_holds
    endpointExponentRange := S.t397EndpointExponentRange
    endpointExponentRange_holds := S.t397EndpointExponentRange_holds
    smoothOrIntervalSupportAcceptedByTheorem := S.t397SelbergSupportAccepted
    smoothOrIntervalSupportAcceptedByTheorem_holds := S.t397SelbergSupportAccepted_holds
  }

  sameSmoothingConvention := S.sameSmoothingConvention
  sameSmoothingConvention_holds := S.sameSmoothingConvention_holds
  sameSingularSeriesNormalization := S.sameSingularSeriesNormalization
  sameSingularSeriesNormalization_holds := S.sameSingularSeriesNormalization_holds
  sameOrientation := S.sameOrientation
  sameOrientation_holds := S.sameOrientation_holds
  sameAsymptoticScale := S.sameAsymptoticScale
  sameAsymptoticScale_holds := S.sameAsymptoticScale_holds
  diagonalAndSingularPartitionsDiscrete := S.diagonalAndSingularPartitionsDiscrete
  diagonalAndSingularPartitionsDiscrete_holds := S.diagonalAndSingularPartitionsDiscrete_holds

/-! ------------------------------------------------------------------------
    E. Source-to-interface capstone
    ------------------------------------------------------------------------ -/

theorem source_builds_exact_bundle (S : Turns391397Source) :
    let B := buildExactApplicabilityBundle S
    B.t391.s = S.u + S.v ∧
    B.t393.ell ≠ 2 ∧
    B.t394Tensor.p ≠ 2 ∧
    B.t394Tensor.r ≠ 2 ∧
    B.t395.u ≤ B.t395.v ∧
    0 < 1 - B.t395.s - B.t395.u ∧
    B.t397Weil.q ≠ 2 ∧
    B.t397BV.split = sourceVaughanSplit ∧
    B.t397BV.split < (1 : ℝ) / 2 - B.t397BV.theta ∧
    B.t397Selberg.q ≠ 2 := by
  dsimp [buildExactApplicabilityBundle]
  exact ⟨S.s_eq, source_ell_odd S, source_p_odd S, source_r_odd S,
    S.ordered, source_completion_length_positive S, source_q397_odd S,
    rfl, source_BV_split_below_gap S, source_qSelberg_odd S⟩

theorem source_to_external_applicability
    (S : Turns391397Source)
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
    let B := buildExactApplicabilityBundle S
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
  exact exact_external_hypothesis_capstone
    (buildExactApplicabilityBundle S)
    h391 h393 h394T h394LS h395 h397W h397BV h397PNT h397II h397S

/-! ------------------------------------------------------------------------
    F. Axiom reports for the source-matching layer
    ------------------------------------------------------------------------ -/

#check Turns391397Source
#check buildExactApplicabilityBundle
#check source_s_lt_one
#check source_completion_length_positive
#check source_turn391_weight_support
#check source_BV_split_below_gap
#check source_builds_exact_bundle
#check source_to_external_applicability

#print axioms TwinPrimeSourceToInterface.source_s_lt_one
#print axioms TwinPrimeSourceToInterface.source_completion_length_positive
#print axioms TwinPrimeSourceToInterface.source_turn391_weight_support
#print axioms TwinPrimeSourceToInterface.source_BV_split_below_gap
#print axioms TwinPrimeSourceToInterface.source_builds_exact_bundle
#print axioms TwinPrimeSourceToInterface.source_to_external_applicability

end
end TwinPrimeSourceToInterface
