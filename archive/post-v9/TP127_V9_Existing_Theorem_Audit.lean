import Mathlib

/-!
# Current Twin Prime publication-boundary certification
## 9 October 2026

This file supersedes two historical audit roles in one self-contained Lean file:

1. the normalized Kloosterman/Weil product-kernel interface used by the
   trace-first interior variance argument; and
2. the terminal logical closure for the CURRENT manuscript, including the
   explicit higher-prime-power subtraction.

It deliberately does not re-prove external analytic number theory.  Those
statements remain publication-boundary inputs.  The purpose here is to check
only the finite normalization/inequality logic and the final implication.

No `axiom`, `sorry`, or `admit` is used.
-/

namespace TwinPrimeCurrentCertification

set_option autoImplicit false
noncomputable section

/-! ## Part I. Normalized Kloosterman product-kernel interface -/

structure Turn397KloostermanData where
  q : ℕ
  m1 : ℕ
  m2 : ℕ
  qPrime : Nat.Prime q
  qOdd : q ≠ 2
  qm1Coprime : Nat.Coprime q m1
  qm2Coprime : Nat.Coprime q m2
  kl1 : ℂ
  kl2 : ℂ
  sourceKernel : ℂ
  normalizedKernelDefinitionMatches : Prop
  normalizedKernelDefinitionMatches_holds : normalizedKernelDefinitionMatches
  singularFrequenciesRemoved : Prop
  singularFrequenciesRemoved_holds : singularFrequenciesRemoved
  kernelFactorisation : sourceKernel = kl1 * kl2

/-- Publication-boundary form of the normalized local Weil input.
The arithmetic applicability data are already fields of `D`; this packet
supplies only the two normalized local bounds used downstream. -/
structure PublishedPrimeKloostermanWeil (D : Turn397KloostermanData) : Prop where
  localBounds : ‖D.kl1‖ ≤ 2 ∧ ‖D.kl2‖ ≤ 2

/-- Constant bound for the normalized opened product kernel. -/
def AuditedTurn397KernelBound (D : Turn397KloostermanData) : Prop :=
  ‖D.sourceKernel‖ ≤ 4

theorem two_normalized_weil_bounds_give_kernel_four
    (D : Turn397KloostermanData)
    (h1 : ‖D.kl1‖ ≤ 2)
    (h2 : ‖D.kl2‖ ≤ 2) :
    AuditedTurn397KernelBound D := by
  unfold AuditedTurn397KernelBound
  rw [D.kernelFactorisation, norm_mul]
  have hmul : ‖D.kl1‖ * ‖D.kl2‖ ≤ (2 : ℝ) * 2 :=
    mul_le_mul h1 h2 (norm_nonneg D.kl2) (by norm_num)
  norm_num at hmul ⊢
  exact hmul

theorem published_weil_to_turn397_kernel_bound
    (D : Turn397KloostermanData)
    (hWeil : PublishedPrimeKloostermanWeil D) :
    AuditedTurn397KernelBound D := by
  exact two_normalized_weil_bounds_give_kernel_four
    D hWeil.localBounds.1 hWeil.localBounds.2

/-! ## Part II. Current final crossing, including prime-power subtraction -/

/-- Conservative lower coefficient displayed in the current manuscript. -/
def cLower : ℝ := (7541 : ℝ) / 10000

/-- Conservative upper coefficient displayed in the current manuscript. -/
def cUpper : ℝ := (74938 : ℝ) / 100000

/-- Published conservative coefficient gap. -/
def coeffGap : ℝ := cLower - cUpper

theorem coeffGap_pos : 0 < coeffGap := by
  norm_num [coeffGap, cLower, cUpper]

/-- Standard infinitude formulation of TPC. -/
def TwinPrimeConjecture : Prop :=
  ∀ B : ℕ, ∃ p : ℕ, B < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-- Positivity of the genuine weighted count at scale X exhibits a true twin pair. -/
def WeightedTwinSupport (T : ℕ → ℝ) : Prop :=
  ∀ X : ℕ, 0 < T X →
    ∃ p : ℕ, X ≤ p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-- Exact publication-boundary source packet for the CURRENT manuscript.

`W = A3 - E` is the quotient-weighted remainder.  `Rpp` is the contribution
from p+2 being a higher prime power, and `T = W - Rpp` is the genuine
prime-pair count.  The three asymptotic fields encode precisely

  A3 >= (cLower + o(1)) H,
  E  <= (cUpper + o(1)) H,
  Rpp = o(H)

in the one-sided forms needed for the proof. -/
structure FinalAnalyticSourceCurrent
    (H A3 E W Rpp T : ℕ → ℝ) where
  H0 : ℕ
  H_pos : ∀ X, H0 ≤ X → 0 < H X

  lowerThreshold : ∀ δ : ℝ, 0 < δ → ℕ
  lower_asymptotic : ∀ (δ : ℝ) (hδ : 0 < δ) (X : ℕ),
    lowerThreshold δ hδ ≤ X →
      (cLower - δ) * H X ≤ A3 X

  upperThreshold : ∀ δ : ℝ, 0 < δ → ℕ
  upper_asymptotic : ∀ (δ : ℝ) (hδ : 0 < δ) (X : ℕ),
    upperThreshold δ hδ ≤ X →
      E X ≤ (cUpper + δ) * H X

  primePowerThreshold : ∀ δ : ℝ, 0 < δ → ℕ
  prime_power_asymptotic : ∀ (δ : ℝ) (hδ : 0 < δ) (X : ℕ),
    primePowerThreshold δ hδ ≤ X →
      Rpp X ≤ δ * H X

  weighted_identity : ∀ X : ℕ, W X = A3 X - E X
  genuine_identity : ∀ X : ℕ, T X = W X - Rpp X
  support : WeightedTwinSupport T

/-- One quarter of the conservative coefficient gap.  Three such error
allowances are spent on the lower o(1), upper o(1), and prime-power o(1),
leaving one quarter of the gap strictly positive. -/
def deltaSafe : ℝ := coeffGap / 4

theorem deltaSafe_pos : 0 < deltaSafe := by
  dsimp [deltaSafe]
  linarith [coeffGap_pos]

theorem coefficient_margin_after_three_errors :
    cUpper + deltaSafe + deltaSafe < cLower - deltaSafe := by
  dsimp [deltaSafe, coeffGap, cLower, cUpper]
  norm_num

/-- The current manuscript's publication-boundary inputs imply a positive
GENUINE twin count at every sufficiently large common scale. -/
theorem current_source_eventually_positive
    {H A3 E W Rpp T : ℕ → ℝ}
    (S : FinalAnalyticSourceCurrent H A3 E W Rpp T) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X → 0 < T X := by
  let δ : ℝ := deltaSafe
  have hδ : 0 < δ := by
    dsimp [δ]
    exact deltaSafe_pos
  let NL : ℕ := S.lowerThreshold δ hδ
  let NU : ℕ := S.upperThreshold δ hδ
  let NP : ℕ := S.primePowerThreshold δ hδ
  let X0 : ℕ := max S.H0 (max NL (max NU NP))
  refine ⟨X0, ?_⟩
  intro X hX
  have hH0 : S.H0 ≤ X := by
    dsimp [X0] at hX
    omega
  have hNL : NL ≤ X := by
    dsimp [X0] at hX
    omega
  have hNU : NU ≤ X := by
    dsimp [X0] at hX
    omega
  have hNP : NP ≤ X := by
    dsimp [X0] at hX
    omega
  have hH : 0 < H X := S.H_pos X hH0
  have hLower : (cLower - δ) * H X ≤ A3 X :=
    S.lower_asymptotic δ hδ X hNL
  have hUpper : E X ≤ (cUpper + δ) * H X :=
    S.upper_asymptotic δ hδ X hNU
  have hPP : Rpp X ≤ δ * H X :=
    S.prime_power_asymptotic δ hδ X hNP
  have hCoeff : cUpper + δ + δ < cLower - δ := by
    dsimp [δ]
    exact coefficient_margin_after_three_errors
  have hScaled :
      (cUpper + δ) * H X + δ * H X < (cLower - δ) * H X := by
    nlinarith
  rw [S.genuine_identity X, S.weighted_identity X]
  nlinarith

/-- Current final capstone: the exact source-level statements used by the
revised manuscript imply the Twin Prime Conjecture, with the prime-power
subtraction represented explicitly. -/
theorem current_source_implies_tpc
    {H A3 E W Rpp T : ℕ → ℝ}
    (S : FinalAnalyticSourceCurrent H A3 E W Rpp T) :
    TwinPrimeConjecture := by
  rcases current_source_eventually_positive S with ⟨X0, hPos⟩
  intro B
  let X : ℕ := max X0 (B + 1)
  have hX0 : X0 ≤ X := by
    dsimp [X]
    omega
  have hBX : B < X := by
    dsimp [X]
    omega
  have hTX : 0 < T X := hPos X hX0
  rcases S.support X hTX with ⟨p, hXp, hp, hp2⟩
  exact ⟨p, lt_of_lt_of_le hBX hXp, hp, hp2⟩

#check Turn397KloostermanData
#check PublishedPrimeKloostermanWeil
#check AuditedTurn397KernelBound
#check two_normalized_weil_bounds_give_kernel_four
#check published_weil_to_turn397_kernel_bound
#check FinalAnalyticSourceCurrent
#check current_source_eventually_positive
#check current_source_implies_tpc

#print axioms TwinPrimeCurrentCertification.two_normalized_weil_bounds_give_kernel_four
#print axioms TwinPrimeCurrentCertification.published_weil_to_turn397_kernel_bound
#print axioms TwinPrimeCurrentCertification.coeffGap_pos
#print axioms TwinPrimeCurrentCertification.coefficient_margin_after_three_errors
#print axioms TwinPrimeCurrentCertification.current_source_eventually_positive
#print axioms TwinPrimeCurrentCertification.current_source_implies_tpc

end
end TwinPrimeCurrentCertification


/-! ## TP127 independent adjudication layer ##
The preceding source is copied byte-for-byte from the v9 submission.
The following layer is new; the manuscript source above has not been changed.
-/

namespace TP127V9
open TwinPrimeCurrentCertification

/-- The literal twin-prime claim, not a substitute or weakened predicate. -/
def ActualTwinPrimeClaim : Prop :=
  ∀ B : ℕ, ∃ p : ℕ, B < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-- Check that the final manuscript Lean statement means actual TPC. -/
theorem target_definitional_agreement :
    ActualTwinPrimeClaim ↔ TwinPrimeConjecture := Iff.rfl

/-- An existence proof of the entire source packet is the missing formal input.
    This requires constructing all the manuscript-specific asymptotic, identity
    and genuine-prime-support proofs from formal theorems; not merely a record
    with assumed proof fields. -/
def CompleteSourceCertificate : Prop :=
  ∃ (H A3 E W Rpp T : ℕ → ℝ),
    FinalAnalyticSourceCurrent H A3 E W Rpp T

/-- A checked deduction. Notice the premise is visible in the type. -/
theorem existing_final_deduction
    (source : CompleteSourceCertificate) :
    ActualTwinPrimeClaim := by
  rcases source with ⟨H, A3, E, W, Rpp, T, S⟩
  exact TwinPrimeCurrentCertification.current_source_implies_tpc S

#check @TwinPrimeCurrentCertification.current_source_implies_tpc
#check @TwinPrimeCurrentCertification.FinalAnalyticSourceCurrent.mk
#print TwinPrimeCurrentCertification.current_source_implies_tpc
#check TP127V9.CompleteSourceCertificate
#check TP127V9.existing_final_deduction
#print axioms TP127V9.target_definitional_agreement
#print axioms TP127V9.existing_final_deduction

end TP127V9
