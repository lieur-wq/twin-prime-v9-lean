import Mathlib
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Twin Prime Project -- semantic source-certificate audit

Purpose.
This file attacks the remaining source-identification certificates left visible by
`TwinPrime_T391_397_Source_To_Interface_Audit.lean`.

It DOES NOT re-prove standard external theorems (Weil, Bombieri--Vinogradov,
Selberg sieve, PNT, large sieve).  Instead it formalizes source-level algebra that
can be checked directly from Turns 393--397, and it proves guardrails showing
which semantic claims need genuinely additional source information.

The main points tested here are:
  1. Turn 393: the off-multiplicative-diagonal condition makes the three roots
     of the cubic t (b t - b') (a - a' t) distinct once a,b,a',b' are nonzero.
  2. Turn 394: the normalized Gauss-square phase tau(chi)^2/p has norm one
     for a nonprincipal character modulo a prime.
  3. Turn 395: a unit-modulus phase is NOT by itself enough to make the
     coefficient-weighted transform unit-size.  The exact sufficient source
     certificate is a coefficient-mass bound by the normalization denominator.
  4. Turn 397: the cutoff theta <= 249/500 leaves a positive gap and therefore
     admits an explicit Vaughan split below 1/2-theta.
  5. Turn 397: on t <= 1/2 the conversion from equal-scale log weight to the
     natural log weight costs at most a factor 2.
  6. Cross-turn normalization: if lower and upper pieces are built from one
     shared context, equality of H, smoothing function, orientation and scale
     is by construction rather than an extra theorem hypothesis.

No `sorry` and no new `axiom` declaration occurs here.
-/

namespace TwinPrimeSemanticSourceAudit

set_option autoImplicit false
open Real
open scoped BigOperators
noncomputable section

/-! ------------------------------------------------------------------------
    A. Turn 393: square-free cubic source certificate
    ------------------------------------------------------------------------ -/

/-- The two nonzero roots b'/b and a/a' collide exactly on the multiplicative
    diagonal a*b = a'*b'.  This is the algebra behind the source sentence
    preceding the Weil bound in Turn 393. -/
theorem offdiag_forces_ratio_roots_distinct
    {K : Type*} [Field K]
    {a b ap bp : K}
    (hb : b ≠ 0) (hap : ap ≠ 0)
    (hoff : a * b ≠ ap * bp) :
    bp / b ≠ a / ap := by
  intro h
  have hcross : bp * ap = a * b := (div_eq_div_iff hb hap).mp h
  apply hoff
  calc
    a * b = bp * ap := hcross.symm
    _ = ap * bp := by ac_rfl

/-- Under the source nonvanishing assumptions and off-diagonal condition,
    the three roots 0, b'/b, a/a' are pairwise distinct. -/
theorem turn393_three_cubic_roots_distinct
    {K : Type*} [Field K]
    {a b ap bp : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hap : ap ≠ 0) (hbp : bp ≠ 0)
    (hoff : a * b ≠ ap * bp) :
    bp / b ≠ 0 ∧ a / ap ≠ 0 ∧ bp / b ≠ a / ap := by
  constructor
  · exact div_ne_zero hbp hb
  constructor
  · exact div_ne_zero ha hap
  · exact offdiag_forces_ratio_roots_distinct hb hap hoff

/-! ------------------------------------------------------------------------
    B. Turn 394: normalized Gauss-square phase
    ------------------------------------------------------------------------ -/

open AddChar ZMod

def localTau
    (p : ℕ) [Fact p.Prime]
    (chi : MulChar (ZMod p) ℂ) : ℂ :=
  gaussSum chi (ZMod.stdAddChar : AddChar (ZMod p) ℂ)

theorem localTau_norm_sq
    (p : ℕ) [Fact p.Prime]
    (chi : MulChar (ZMod p) ℂ)
    (hchi : chi ≠ 1) :
    ‖localTau p chi‖ ^ 2 = (p : ℝ) := by
  let psi : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  have hprod :
      gaussSum chi psi * gaussSum chi⁻¹ psi⁻¹ = (p : ℂ) := by
    simpa [psi] using
      (gaussSum_mul_gaussSum_eq_card
        (R := ZMod p) (R' := ℂ) (χ := chi) hchi
        (ψ := psi) (ZMod.isPrimitive_stdAddChar p))
  have hstar : star (gaussSum chi psi) = gaussSum chi⁻¹ psi⁻¹ := by
    simpa using (star_gaussSum_eq chi psi)
  rw [← hstar] at hprod
  have hnorm := congrArg norm hprod
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hmul : ‖localTau p chi‖ * ‖localTau p chi‖ = (p : ℝ) := by
    simpa [localTau, psi, norm_mul] using hnorm
  nlinarith [hmul]

def localGaussSquarePhase
    (p : ℕ) [Fact p.Prime]
    (chi : MulChar (ZMod p) ℂ) : ℂ :=
  (localTau p chi) ^ 2 / (p : ℂ)

theorem localGaussSquarePhase_norm_one
    (p : ℕ) [Fact p.Prime]
    (chi : MulChar (ZMod p) ℂ)
    (hchi : chi ≠ 1) :
    ‖localGaussSquarePhase p chi‖ = 1 := by
  have hp : Nat.Prime p := Fact.out
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [localGaussSquarePhase, norm_div, norm_pow]
  have ht := localTau_norm_sq p chi hchi
  have hpnorm : ‖(p : ℂ)‖ = (p : ℝ) := by simp
  rw [hpnorm, ht]
  exact div_self (ne_of_gt hpR)

/-! ------------------------------------------------------------------------
    C. Turn 395: what the unit-size transform claim really needs
    ------------------------------------------------------------------------ -/

def eq5939Inner {I : Type*} [Fintype I]
    (D : ℝ) (eps A B : I → ℂ) : ℂ :=
  (((1 / D : ℝ) : ℂ) * ∑ i, eps i * A i * B i)

def coeffMass {I : Type*} [Fintype I] (A B : I → ℂ) : ℝ :=
  ∑ i, ‖A i * B i‖

theorem eq5939_numerator_norm_le_mass
    {I : Type*} [Fintype I]
    (eps A B : I → ℂ)
    (hphase : ∀ i, ‖eps i‖ ≤ 1) :
    ‖∑ i, eps i * A i * B i‖ ≤ coeffMass A B := by
  calc
    ‖∑ i, eps i * A i * B i‖
        ≤ ∑ i, ‖eps i * A i * B i‖ := norm_sum_le _ _
    _ = ∑ i, ‖eps i‖ * ‖A i * B i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [norm_mul, mul_assoc]
    _ ≤ ∑ i, ‖A i * B i‖ := by
          apply Finset.sum_le_sum
          intro i hi
          have hAB : 0 ≤ ‖A i * B i‖ := norm_nonneg _
          nlinarith [hphase i]
    _ = coeffMass A B := rfl

/-- The exact sufficient certificate missing from the phrase "unit-size":
    coefficient mass must not exceed the normalization denominator. -/
theorem eq5939_hunit_of_mass_le_denominator
    {I : Type*} [Fintype I]
    (D : ℝ) (eps A B : I → ℂ)
    (hD : 0 < D)
    (hphase : ∀ i, ‖eps i‖ ≤ 1)
    (hMass : coeffMass A B ≤ D) :
    ‖eq5939Inner D eps A B‖ ≤ 1 := by
  have hnum : ‖∑ i, eps i * A i * B i‖ ≤ D :=
    le_trans (eq5939_numerator_norm_le_mass eps A B hphase) hMass
  have hscale : ‖(((1 / D : ℝ) : ℂ))‖ = 1 / D := by
    simp [abs_of_pos hD]
  rw [eq5939Inner, norm_mul, hscale]
  have hnonneg : 0 ≤ (1 / D : ℝ) := by positivity
  calc
    (1 / D) * ‖∑ i, eps i * A i * B i‖
        ≤ (1 / D) * D := mul_le_mul_of_nonneg_left hnum hnonneg
    _ = 1 := by field_simp

/-- Guardrail: unit phases alone are insufficient.  Thus the Turn-395 source
    must supply a normalization/mass estimate (or an equivalent L2 argument),
    not merely |epsilon(xi)|=1. -/
theorem turn395_unit_phase_alone_is_not_enough :
    ‖eq5939Inner (I := PUnit) 1
        (fun _ => (1 : ℂ))
        (fun _ => (2 : ℂ))
        (fun _ => (1 : ℂ))‖ > 1 := by
  norm_num [eq5939Inner]

/-- Once the actual completed coefficient is identified with Eq. (5939), the
    mass certificate gives the exact pointwise hunit required by the clean
    completion audit. -/
theorem actualPsi_hunit_of_semantic_certificates
    {L : ℕ} [NeZero L]
    {I : Type*} [Fintype I]
    (Sing : ZMod L → Prop) [DecidablePred Sing]
    (actualPsi : ZMod L → ℂ)
    (D : ZMod L → ℝ)
    (eps A B : ZMod L → I → ℂ)
    (hD : ∀ k, ¬Sing k → 0 < D k)
    (hphase : ∀ k i, ¬Sing k → ‖eps k i‖ ≤ 1)
    (hMass : ∀ k, ¬Sing k → coeffMass (A k) (B k) ≤ D k)
    (hident : ∀ k, ¬Sing k →
      actualPsi k = eq5939Inner (D k) (eps k) (A k) (B k)) :
    ∀ k, ¬Sing k → ‖actualPsi k‖ ≤ 1 := by
  intro k hk
  rw [hident k hk]
  exact eq5939_hunit_of_mass_le_denominator
    (D k) (eps k) (A k) (B k)
    (hD k hk) (fun i => hphase k i hk) (hMass k hk)

/-! ------------------------------------------------------------------------
    D. Turn 397: the Vaughan split can be chosen explicitly
    ------------------------------------------------------------------------ -/

def canonicalVaughanSplit (theta : ℝ) : ℝ :=
  ((1 : ℝ) / 2 - theta) / 2

theorem turn397_cutoff_has_positive_gap
    {theta : ℝ} (htheta : theta ≤ (249 : ℝ) / 500) :
    0 < (1 : ℝ) / 2 - theta := by
  linarith

theorem canonicalVaughanSplit_is_admissible
    {theta : ℝ} (htheta : theta ≤ (249 : ℝ) / 500) :
    0 ≤ canonicalVaughanSplit theta ∧
    canonicalVaughanSplit theta < (1 : ℝ) / 2 - theta := by
  have hgap := turn397_cutoff_has_positive_gap htheta
  constructor
  · unfold canonicalVaughanSplit
    linarith
  · unfold canonicalVaughanSplit
    linarith

/-! ------------------------------------------------------------------------
    E. Turn 397 endpoint: factor-two logarithmic conversion
    ------------------------------------------------------------------------ -/

/-- If log r = (1-t) log Y, t <= 1/2 and log Y>0, then replacing the
    equal-scale log-r normalization by the natural log-Y normalization costs
    at most a factor 2. -/
theorem endpoint_log_conversion_at_most_two
    {t logY logr : ℝ}
    (hlogY : 0 < logY)
    (ht : t ≤ (1 : ℝ) / 2)
    (hlogr : logr = (1 - t) * logY) :
    logY / logr ≤ 2 := by
  have h1mt : (1 : ℝ) / 2 ≤ 1 - t := by linarith
  have h1mtpos : 0 < 1 - t := by linarith
  have hlogrpos : 0 < logr := by
    rw [hlogr]
    exact mul_pos h1mtpos hlogY
  rw [div_le_iff₀ hlogrpos]
  rw [hlogr]
  nlinarith

/-! ------------------------------------------------------------------------
    F. Cross-turn shared-context guardrail
    ------------------------------------------------------------------------ -/

inductive Orientation where
  minusTwo
  plusTwo
  deriving DecidableEq

structure SharedContext where
  H : ℝ
  Y : ℝ
  Psi : ℝ → ℂ
  orientation : Orientation

/-- If lower and upper pieces are literally built from one context, these
    normalization matches are identities, not hypotheses. -/
theorem same_H_by_construction (C : SharedContext) : C.H = C.H := rfl

theorem same_smoothing_by_construction (C : SharedContext) : C.Psi = C.Psi := rfl

theorem same_orientation_by_construction (C : SharedContext) :
    C.orientation = C.orientation := rfl

theorem same_scale_by_construction (C : SharedContext) : C.Y = C.Y := rfl

/-! ------------------------------------------------------------------------
    G. What remains genuinely semantic after this file
    ------------------------------------------------------------------------ -/

/-- This record intentionally has NO constructor produced below.  Its fields
    are the source facts that cannot be manufactured from rational inequalities
    alone.  They must be justified by the written definitions or by a cited
    standard theorem.

    In particular, `turn395_mass_certificate` is singled out because the
    guardrail above proves that unit Gauss-square phases alone do not imply it.
-/
structure RemainingSemanticCore : Type where
  turn394_actual_block_equals_character_expansion : Prop
  turn395_actual_completed_transform_equals_eq5939 : Prop
  turn395_mass_certificate : Prop
  turn397_actual_kernel_equals_normalized_Kloosterman_model : Prop
  turn397_TypeI_sum_really_reduced_to_classical_BV_form : Prop
  turn397_Psi_is_the_declared_smooth_product_weight : Prop
  turn397_TypeII_coefficients_are_the_claimed_divisor_bounded_system : Prop
  turn397_Selberg_singular_series_is_the_same_H_normalization : Prop

/-! ------------------------------------------------------------------------
    H. Checks
    ------------------------------------------------------------------------ -/

#check offdiag_forces_ratio_roots_distinct
#check turn393_three_cubic_roots_distinct
#check localTau_norm_sq
#check localGaussSquarePhase_norm_one
#check eq5939_hunit_of_mass_le_denominator
#check turn395_unit_phase_alone_is_not_enough
#check actualPsi_hunit_of_semantic_certificates
#check canonicalVaughanSplit_is_admissible
#check endpoint_log_conversion_at_most_two
#check RemainingSemanticCore

#print axioms TwinPrimeSemanticSourceAudit.turn393_three_cubic_roots_distinct
#print axioms TwinPrimeSemanticSourceAudit.localGaussSquarePhase_norm_one
#print axioms TwinPrimeSemanticSourceAudit.eq5939_hunit_of_mass_le_denominator
#print axioms TwinPrimeSemanticSourceAudit.turn395_unit_phase_alone_is_not_enough
#print axioms TwinPrimeSemanticSourceAudit.actualPsi_hunit_of_semantic_certificates
#print axioms TwinPrimeSemanticSourceAudit.canonicalVaughanSplit_is_admissible
#print axioms TwinPrimeSemanticSourceAudit.endpoint_log_conversion_at_most_two

end
end TwinPrimeSemanticSourceAudit
