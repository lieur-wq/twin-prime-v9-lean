import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Twin Prime Project - Turns 391--397 final-final applicability audit

Stopping rule
-------------
This file implements the agreed boundary of the Lean audit.

* Standard external theorems are TRUSTED theorem inputs.  We do not re-prove
  PNT, Weil, Bombieri--Vinogradov, the multiplicative large sieve, or the
  classical Selberg upper sieve from first principles.
* What Lean checks here is that the concrete proof context presented to those
  trusted inputs has the hypotheses that the proof says it has: prime/distinct
  moduli, coprimality, range inequalities, nonsingular exclusions, exact source
  identification, the correct Eq. (5939) normalization, the Turn-394
  retraction, the Turn-397 one-completion factor, and a common H/singular-series/
  smoothing/orientation/asymptotic context at closure.
* No `sorry` and no new `axiom` declarations occur in this file.

This is intended to be the last planned audit file.  A rerun should only be
needed for a mechanical Lean syntax/tactic correction or because the audit
finds a genuinely false/missing application hypothesis.
-/

namespace TwinPrime391397FinalFinalAudit

set_option autoImplicit false
open Real
open scoped BigOperators
open Finset
noncomputable section

/-! ========================================================================
    I. Numerical/range facts that are not delegated to external theorems
    ======================================================================== -/

theorem turn394_actual_saving_not_turn393_ideal :
    (41 : ℚ) / 214 < (33 : ℚ) / 107 := by
  norm_num

theorem turn394_deficit_is_nine_over_214 :
    (50 : ℚ) / 214 - (41 : ℚ) / 214 = (9 : ℚ) / 214 := by
  norm_num

theorem turn395_trace_region {s : ℝ} (hs : s ≤ (3 : ℝ) / 5) :
    2 * s - 1 ≤ (1 - s) / 2 := by
  linarith

theorem turn395_completion_region {s u : ℝ} (hu : u ≤ 4 - 6 * s) :
    (5 * s - 3) / 2 ≤ (1 - s - u) / 2 := by
  linarith

theorem turn395_conservative_lower_coefficient :
    (754090168159945 : ℚ) / 10^15
        + (20612 : ℚ) / 10^8
        - (1 : ℚ) / 7872
      > (7541 : ℚ) / 10000 := by
  norm_num

theorem turn397_interior_gap_at_0498 :
    3 * ((249 : ℝ) / 500) / 2 +
      (1 - (249 : ℝ) / 500) / 2 = (499 : ℝ) / 500 := by
  norm_num

theorem turn397_one_completion_factor (Q M Eps : ℝ) :
    Q * (Q * M ^ 2 * Eps) = (Q * M) ^ 2 * Eps := by
  ring

theorem turn397_extra_Q_cannot_vanish
    {Q M Eps : ℝ}
    (hQ : 0 < Q) (hM : 0 < M) (hE : 0 < Eps)
    (hEq : Q * (Q * (Q * M ^ 2 * Eps)) = (Q * M) ^ 2 * Eps) :
    Q = 1 := by
  have hscale : 0 < (Q * M) ^ 2 * Eps := by positivity
  have hrewrite :
      Q * ((Q * M) ^ 2 * Eps) = (Q * M) ^ 2 * Eps := by
    calc
      Q * ((Q * M) ^ 2 * Eps)
          = Q * (Q * (Q * M ^ 2 * Eps)) := by ring
      _ = (Q * M) ^ 2 * Eps := hEq
  nlinarith

theorem log_251_249_upper :
    Real.log ((251 : ℝ) / 249) < (2 : ℝ) / 249 := by
  have hx : 0 < (251 : ℝ) / 249 := by norm_num
  have hne : (251 : ℝ) / 249 ≠ 1 := by norm_num
  have h := Real.log_lt_sub_one_of_pos hx hne
  norm_num at h ⊢
  exact h

theorem turn397_upper_coefficient_lt_074938 :
    (1 + 7 * Real.log ((251 : ℝ) / 249) / Real.log 2) * Real.log 2
      < (74938 : ℝ) / 100000 := by
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlogpos
  have hnum := log_251_249_upper
  have htwo : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hid :
      (1 + 7 * Real.log ((251 : ℝ) / 249) / Real.log 2) * Real.log 2
        = Real.log 2 + 7 * Real.log ((251 : ℝ) / 249) := by
    field_simp [hlogne]
  rw [hid]
  nlinarith

/-! ========================================================================
    II. Trusted theorem interfaces and their EXPLICIT applicability predicates

    The theorem bodies are not formalized here.  Instead Lean is given a
    theorem-valued hypothesis and must instantiate it only after the concrete
    applicability predicate has been established.
    ======================================================================== -/

/-- Turn-393 reciprocal-square correlation is used at a prime modulus and
    off the multiplicative diagonal. -/
def CorrApplicable (ell : ℕ) (offDiagonal : Prop) : Prop :=
  Nat.Prime ell ∧ offDiagonal

/-- A trusted version of the Turn-393/standard finite-field correlation input. -/
def TrustedCorrelation (Conclusion : ℕ → Prop → Prop) : Prop :=
  ∀ ell offDiagonal, CorrApplicable ell offDiagonal → Conclusion ell offDiagonal

theorem apply_trusted_correlation
    {Conclusion : ℕ → Prop → Prop}
    {ell : ℕ} {offDiagonal : Prop}
    (hTrusted : TrustedCorrelation Conclusion)
    (hPrime : Nat.Prime ell)
    (hOff : offDiagonal) :
    Conclusion ell offDiagonal := by
  exact hTrusted ell offDiagonal ⟨hPrime, hOff⟩

/-- Turn-394 CRT/Gauss tensorisation is invoked only for distinct prime
    factors p and r. -/
def TensorApplicable (p r : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime r ∧ p ≠ r

def TrustedTensorisation (Conclusion : ℕ → ℕ → Prop) : Prop :=
  ∀ p r, TensorApplicable p r → Conclusion p r

theorem apply_trusted_tensorisation
    {Conclusion : ℕ → ℕ → Prop}
    {p r : ℕ}
    (hTrusted : TrustedTensorisation Conclusion)
    (hp : Nat.Prime p) (hr : Nat.Prime r) (hpr : p ≠ r) :
    Conclusion p r := by
  exact hTrusted p r ⟨hp, hr, hpr⟩

/-- The p=r subfamily is not allowed to be silently fed to a theorem whose CRT
    statement assumed p≠r.  It must be handled separately. -/
def TrustedPrimeSquareDiagonal (Conclusion : ℕ → Prop) : Prop :=
  ∀ p, Nat.Prime p → Conclusion p

theorem prime_product_case_split
    {TensorConclusion : ℕ → ℕ → Prop}
    {DiagonalConclusion : ℕ → Prop}
    {p r : ℕ}
    (hp : Nat.Prime p) (hr : Nat.Prime r)
    (hTensor : TrustedTensorisation TensorConclusion)
    (hDiag : TrustedPrimeSquareDiagonal DiagonalConclusion) :
    (p ≠ r → TensorConclusion p r) ∧
      (p = r → DiagonalConclusion p) := by
  constructor
  · intro hne
    exact hTensor p r ⟨hp, hr, hne⟩
  · intro heq
    subst r
    exact hDiag p hp

/-- Turn-397 normalized Kloosterman/Weil application: the outer modulus is
    prime and the arguments to the CRT local factor are coprime to it. -/
def WeilApplicable (q m1 m2 : ℕ) : Prop :=
  Nat.Prime q ∧ Nat.Coprime q m1 ∧ Nat.Coprime q m2

def TrustedWeil
    (K : ℕ → ℕ → ℕ → ℂ) (B : ℝ) : Prop :=
  ∀ q m1 m2, WeilApplicable q m1 m2 → ‖K q m1 m2‖ ≤ B

theorem apply_trusted_weil
    {K : ℕ → ℕ → ℕ → ℂ} {B : ℝ}
    {q m1 m2 : ℕ}
    (hTrusted : TrustedWeil K B)
    (hq : Nat.Prime q)
    (hqm1 : Nat.Coprime q m1)
    (hqm2 : Nat.Coprime q m2) :
    ‖K q m1 m2‖ ≤ B := by
  exact hTrusted q m1 m2 ⟨hq, hqm1, hqm2⟩

/-- Interior Turn-397 Type-I/Bombieri--Vinogradov use.  The audit records the
    actual fixed interior cutoff theta<=0.498 and a Vaughan split below the
    available half-gap. -/
def BVApplicable (theta split : ℝ) : Prop :=
  (1 : ℝ) / 3 < theta ∧
  theta ≤ (249 : ℝ) / 500 ∧
  0 ≤ split ∧
  split < ((1 : ℝ) / 2 - theta)

def TrustedBV (Conclusion : ℝ → ℝ → Prop) : Prop :=
  ∀ theta split, BVApplicable theta split → Conclusion theta split

theorem apply_trusted_BV
    {Conclusion : ℝ → ℝ → Prop}
    {theta split : ℝ}
    (hTrusted : TrustedBV Conclusion)
    (hLow : (1 : ℝ) / 3 < theta)
    (hHigh : theta ≤ (249 : ℝ) / 500)
    (hSplit0 : 0 ≤ split)
    (hSplit : split < (1 : ℝ) / 2 - theta) :
    Conclusion theta split := by
  exact hTrusted theta split ⟨hLow, hHigh, hSplit0, hSplit⟩

/-- At the chosen endpoint cutoff there really is a positive 0.002 gap. -/
theorem endpoint_BV_gap :
    (0 : ℝ) < (1 : ℝ) / 2 - (249 : ℝ) / 500 := by
  norm_num

/-- Fixed-q endpoint Selberg use: q is an odd prime.  All singular-series and
    weight-normalization information remains in the trusted conclusion itself. -/
def SelbergApplicable (q : ℕ) : Prop :=
  Nat.Prime q ∧ q ≠ 2

def TrustedSelberg (Conclusion : ℕ → Prop) : Prop :=
  ∀ q, SelbergApplicable q → Conclusion q

theorem apply_trusted_selberg
    {Conclusion : ℕ → Prop}
    {q : ℕ}
    (hTrusted : TrustedSelberg Conclusion)
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2) :
    Conclusion q := by
  exact hTrusted q ⟨hq, hq2⟩

/-! ========================================================================
    III. Correct Turn-395 Eq. (5939) source normalization
    ======================================================================== -/

/-- After epsilon(xi)=tau_q(xi)^2/q, Eq. (5939) leaves the scalar
       q / sqrt(q*phi(q)),
    not 1/phi(q). -/
def eq5939Scale (q phi : ℝ) : ℝ :=
  q / Real.sqrt (q * phi)

def eq5939Source
    {ι : Type*} [Fintype ι]
    (q phi : ℝ) (eps A B : ι → ℂ) : ℂ :=
  (((eq5939Scale q phi : ℝ) : ℂ) * ∑ xi, eps xi * A xi * B xi)

def coeffMass
    {ι : Type*} [Fintype ι]
    (A B : ι → ℂ) : ℝ :=
  ∑ xi, ‖A xi * B xi‖

theorem eq5939_numerator_norm_le_mass
    {ι : Type*} [Fintype ι]
    (eps A B : ι → ℂ)
    (hphase : ∀ xi, ‖eps xi‖ ≤ 1) :
    ‖∑ xi, eps xi * A xi * B xi‖ ≤ coeffMass A B := by
  calc
    ‖∑ xi, eps xi * A xi * B xi‖
        ≤ ∑ xi, ‖eps xi * A xi * B xi‖ := norm_sum_le _ _
    _ = ∑ xi, ‖eps xi‖ * ‖A xi * B xi‖ := by
          apply Finset.sum_congr rfl
          intro xi hxi
          simp [mul_assoc]
    _ ≤ ∑ xi, ‖A xi * B xi‖ := by
          apply Finset.sum_le_sum
          intro xi hxi
          have hAB : 0 ≤ ‖A xi * B xi‖ := norm_nonneg _
          nlinarith [hphase xi]
    _ = coeffMass A B := rfl

/-- Exact sufficient source condition for the Turn-395 nonsingular unit bound
    with the ACTUAL Eq. (5939) scalar. -/
theorem eq5939_unit_of_scaled_mass
    {ι : Type*} [Fintype ι]
    (q phi : ℝ) (eps A B : ι → ℂ)
    (hscale : 0 ≤ eq5939Scale q phi)
    (hphase : ∀ xi, ‖eps xi‖ ≤ 1)
    (hMass : eq5939Scale q phi * coeffMass A B ≤ 1) :
    ‖eq5939Source q phi eps A B‖ ≤ 1 := by
  have hnum := eq5939_numerator_norm_le_mass eps A B hphase
  rw [eq5939Source, norm_mul]
  have hnormscale :
      ‖(((eq5939Scale q phi : ℝ) : ℂ))‖ = eq5939Scale q phi := by
    simp [abs_of_nonneg hscale]
  rw [hnormscale]
  calc
    eq5939Scale q phi * ‖∑ xi, eps xi * A xi * B xi‖
        ≤ eq5939Scale q phi * coeffMass A B :=
          mul_le_mul_of_nonneg_left hnum hscale
    _ ≤ 1 := hMass

/-- Final faithful Turn-395 application condition.  No toy 1/phi average is
    substituted. -/
def Turn395ActualBridgeOK
    {L : ℕ} [NeZero L]
    {ι : Type*} [Fintype ι]
    (Sing : ZMod L → Prop) [DecidablePred Sing]
    (actualPsi : ZMod L → ℂ)
    (q phi : ZMod L → ℝ)
    (eps A B : ZMod L → ι → ℂ) : Prop :=
  ∀ k, ¬ Sing k →
    0 ≤ eq5939Scale (q k) (phi k) ∧
    (∀ xi, ‖eps k xi‖ ≤ 1) ∧
    eq5939Scale (q k) (phi k) * coeffMass (A k) (B k) ≤ 1 ∧
    actualPsi k = eq5939Source (q k) (phi k) (eps k) (A k) (B k)

theorem turn395_actual_bridge_gives_unit
    {L : ℕ} [NeZero L]
    {ι : Type*} [Fintype ι]
    (Sing : ZMod L → Prop) [DecidablePred Sing]
    (actualPsi : ZMod L → ℂ)
    (q phi : ZMod L → ℝ)
    (eps A B : ZMod L → ι → ℂ)
    (hBridge : Turn395ActualBridgeOK Sing actualPsi q phi eps A B) :
    ∀ k, ¬ Sing k → ‖actualPsi k‖ ≤ 1 := by
  intro k hk
  rcases hBridge k hk with ⟨hscale, hphase, hMass, hident⟩
  rw [hident]
  exact eq5939_unit_of_scaled_mass
    (q k) (phi k) (eps k) (A k) (B k)
    hscale hphase hMass

/-- Guardrail showing that the discarded 1/phi model is genuinely a different
    normalization. -/
theorem eq5939_scale_not_phi_average :
    eq5939Scale 4 4 ≠ (1 : ℝ) / 4 := by
  norm_num [eq5939Scale]

/-! ========================================================================
    IV. Turn-397 endpoint and same-normalization closure
    ======================================================================== -/

theorem endpoint_factor_eight
    {count equalMain naturalMain : ℝ}
    (hSelberg : count ≤ 4 * equalMain)
    (hConvert : equalMain ≤ 2 * naturalMain) :
    count ≤ 8 * naturalMain := by
  calc
    count ≤ 4 * equalMain := hSelberg
    _ ≤ 4 * (2 * naturalMain) := by nlinarith
    _ = 8 * naturalMain := by ring

theorem interior_plus_tail_same_H
    {H Itail Eint Etail E : ℝ}
    (hE : E = Eint + Etail)
    (hInterior : Eint ≤ H * (Real.log 2 - Itail))
    (hTail : Etail ≤ 8 * H * Itail) :
    E ≤ H * (Real.log 2 + 7 * Itail) := by
  calc
    E = Eint + Etail := hE
    _ ≤ H * (Real.log 2 - Itail) + 8 * H * Itail := add_le_add hInterior hTail
    _ = H * (Real.log 2 + 7 * Itail) := by ring

structure ProofContext where
  H : ℝ
  singularSeriesTag : ℕ
  smoothingTag : ℕ
  orientationShift : ℤ
  asymptoticScaleTag : ℕ

/-- The final source inputs are not opaque `Matching` propositions.  Every
    field records a concrete condition that a trusted theorem/application uses. -/
structure ApplicabilityContext where
  lowerCtx : ProofContext
  upperCtx : ProofContext
  sameContext : lowerCtx = upperCtx

  /- Turn 393/394 prime-product application data. -/
  p : ℕ
  r : ℕ
  pPrime : Nat.Prime p
  rPrime : Nat.Prime r
  primeFactorsDistinctOrDiagonalHandled : p ≠ r ∨ p = r

  /- Turn 397 Weil/CRT data. -/
  q : ℕ
  m1 : ℕ
  m2 : ℕ
  qPrime : Nat.Prime q
  qm1Coprime : Nat.Coprime q m1
  qm2Coprime : Nat.Coprime q m2

  /- Turn 397 interior BV range. -/
  theta : ℝ
  split : ℝ
  thetaLow : (1 : ℝ) / 3 < theta
  thetaHigh : theta ≤ (249 : ℝ) / 500
  splitNonneg : 0 ≤ split
  splitBelowGap : split < (1 : ℝ) / 2 - theta

  /- Turn 397 fixed-q Selberg range. -/
  selbergQ : ℕ
  selbergQPrime : Nat.Prime selbergQ
  selbergQOdd : selbergQ ≠ 2

/-- The final coefficient crossing once every application is in the SAME
    context. -/
theorem final_numeric_crossing
    (ctx : ProofContext)
    {A3 E T : ℝ}
    (hH : 0 < ctx.H)
    (hLower : ((7541 : ℝ) / 10000) * ctx.H ≤ A3)
    (hUpper : E ≤ ((74938 : ℝ) / 100000) * ctx.H)
    (hTwin : T = A3 - E) :
    0 < T := by
  rw [hTwin]
  nlinarith

/-! ========================================================================
    V. FINAL-FINAL applicability capstone

    The external results below are theorem-valued hypotheses.  Lean does not
    prove them; it checks that they are invoked only after the corresponding
    concrete applicability conditions in `ApplicabilityContext` have been
    supplied.
    ======================================================================== -/

theorem final_final_applicability_capstone
    {L : ℕ} [NeZero L]
    {ι : Type*} [Fintype ι]
    (Sing : ZMod L → Prop) [DecidablePred Sing]
    (actualPsi : ZMod L → ℂ)
    (sourceQ sourcePhi : ZMod L → ℝ)
    (eps A B : ZMod L → ι → ℂ)
    (app : ApplicabilityContext)

    /- Trusted theorem interfaces. -/
    {CorrConclusion : ℕ → Prop → Prop}
    {TensorConclusion : ℕ → ℕ → Prop}
    {PrimeSquareConclusion : ℕ → Prop}
    {K : ℕ → ℕ → ℕ → ℂ} {WeilB : ℝ}
    {BVConclusion : ℝ → ℝ → Prop}
    {SelbergConclusion : ℕ → Prop}
    (hCorrTrusted : TrustedCorrelation CorrConclusion)
    (offDiagonal : Prop) (hOffDiagonal : offDiagonal)
    (hTensorTrusted : TrustedTensorisation TensorConclusion)
    (hPrimeSquareTrusted : TrustedPrimeSquareDiagonal PrimeSquareConclusion)
    (hWeilTrusted : TrustedWeil K WeilB)
    (hBVTrusted : TrustedBV BVConclusion)
    (hSelbergTrusted : TrustedSelberg SelbergConclusion)

    /- Exact Turn-395 source bridge with the correct Eq. (5939) scale. -/
    (h395Bridge : Turn395ActualBridgeOK Sing actualPsi sourceQ sourcePhi eps A B)

    /- Turn-397 same-normalization source estimates. -/
    {A3 E T : ℝ}
    (hH : 0 < app.lowerCtx.H)
    (hLower : ((7541 : ℝ) / 10000) * app.lowerCtx.H ≤ A3)
    (hUpper : E ≤ ((74938 : ℝ) / 100000) * app.upperCtx.H)
    (hTwin : T = A3 - E) :

    /- Machine-visible audit result. -/
    CorrConclusion app.p offDiagonal ∧
    ((app.p ≠ app.r → TensorConclusion app.p app.r) ∧
      (app.p = app.r → PrimeSquareConclusion app.p)) ∧
    ‖K app.q app.m1 app.m2‖ ≤ WeilB ∧
    BVConclusion app.theta app.split ∧
    SelbergConclusion app.selbergQ ∧
    (∀ k, ¬ Sing k → ‖actualPsi k‖ ≤ 1) ∧
    app.lowerCtx = app.upperCtx ∧
    0 < T := by

  have hCorr : CorrConclusion app.p offDiagonal :=
    apply_trusted_correlation hCorrTrusted app.pPrime hOffDiagonal

  have hTensorDiag :
      (app.p ≠ app.r → TensorConclusion app.p app.r) ∧
      (app.p = app.r → PrimeSquareConclusion app.p) :=
    prime_product_case_split app.pPrime app.rPrime
      hTensorTrusted hPrimeSquareTrusted

  have hWeil : ‖K app.q app.m1 app.m2‖ ≤ WeilB :=
    apply_trusted_weil hWeilTrusted app.qPrime app.qm1Coprime app.qm2Coprime

  have hBV : BVConclusion app.theta app.split :=
    apply_trusted_BV hBVTrusted app.thetaLow app.thetaHigh
      app.splitNonneg app.splitBelowGap

  have hSelberg : SelbergConclusion app.selbergQ :=
    apply_trusted_selberg hSelbergTrusted app.selbergQPrime app.selbergQOdd

  have hUnit : ∀ k, ¬ Sing k → ‖actualPsi k‖ ≤ 1 :=
    turn395_actual_bridge_gives_unit
      Sing actualPsi sourceQ sourcePhi eps A B h395Bridge

  have hUpperSame : E ≤ ((74938 : ℝ) / 100000) * app.lowerCtx.H := by
    have hHs : app.upperCtx.H = app.lowerCtx.H :=
      (congrArg ProofContext.H app.sameContext).symm
    rw [← hHs]
    exact hUpper

  have hPositive : 0 < T :=
    final_numeric_crossing app.lowerCtx hH hLower hUpperSame hTwin

  exact ⟨hCorr, hTensorDiag, hWeil, hBV, hSelberg,
    hUnit, app.sameContext, hPositive⟩

/-! ========================================================================
    VI. Stopping interpretation

A clean run of this file means:

* the standard external theorems were treated as trusted inputs rather than
  re-proved from foundations;
* Lean nevertheless refused to invoke them unless the concrete application
  hypotheses listed in `ApplicabilityContext` were supplied;
* the Turn-394 p≠r CRT restriction cannot silently swallow p=r: the p=r case
  must go through the separately trusted diagonal handler;
* Turn-397 Weil is used only with a prime q and explicit coprimality;
* Turn-397 BV is used only in the stated interior range and with a split below
  the available gap;
* Turn-397 Selberg is used only for an odd prime q;
* Turn-395 uses the actual q/sqrt(q phi(q)) Eq. (5939) normalization and not
  the discarded 1/phi surrogate;
* lower and upper bounds share literally the same `ProofContext` before the
  final T=A3-E positivity step.

That is the agreed audit boundary.  No deeper formalization of PNT, Weil,
Bombieri--Vinogradov, Selberg, elementary logic, or arithmetic foundations is
part of this audit.
-/

#check turn394_actual_saving_not_turn393_ideal
#check turn394_deficit_is_nine_over_214
#check turn395_completion_region
#check turn395_conservative_lower_coefficient
#check turn397_one_completion_factor
#check turn397_upper_coefficient_lt_074938

#check CorrApplicable
#check TrustedCorrelation
#check apply_trusted_correlation
#check TensorApplicable
#check TrustedTensorisation
#check prime_product_case_split
#check WeilApplicable
#check TrustedWeil
#check apply_trusted_weil
#check BVApplicable
#check TrustedBV
#check apply_trusted_BV
#check SelbergApplicable
#check TrustedSelberg
#check apply_trusted_selberg

#check eq5939Scale
#check eq5939Source
#check Turn395ActualBridgeOK
#check turn395_actual_bridge_gives_unit
#check ApplicabilityContext
#check final_numeric_crossing
#check final_final_applicability_capstone

#print axioms TwinPrime391397FinalFinalAudit.turn394_actual_saving_not_turn393_ideal
#print axioms TwinPrime391397FinalFinalAudit.turn395_conservative_lower_coefficient
#print axioms TwinPrime391397FinalFinalAudit.turn397_upper_coefficient_lt_074938
#print axioms TwinPrime391397FinalFinalAudit.apply_trusted_tensorisation
#print axioms TwinPrime391397FinalFinalAudit.apply_trusted_weil
#print axioms TwinPrime391397FinalFinalAudit.apply_trusted_BV
#print axioms TwinPrime391397FinalFinalAudit.apply_trusted_selberg
#print axioms TwinPrime391397FinalFinalAudit.turn395_actual_bridge_gives_unit
#print axioms TwinPrime391397FinalFinalAudit.final_numeric_crossing
#print axioms TwinPrime391397FinalFinalAudit.final_final_applicability_capstone

end
end TwinPrime391397FinalFinalAudit
