import Mathlib

/-!
# Twin Prime certification Run 10b
## Turn-418 Heath--Brown interior variance target (historical item 13)

Purpose
-------
Run 10 v2 cleanly certified a local finite Type-II coefficient package, but the later
Turn-418 audit shows that historical item 13 cannot be closed by that generic package.
The actual missing upper-side statement is Turn 418, Eq. (6635): after the exact
Heath--Brown branch recombination and the primitive Gauss-pair cancellation of Turn 415,
the coefficient-specific interior variance must satisfy

    limsup_{Y -> infinity} V_HB,int(Y) < (0.0067)^2 = 4.489e-5.

This file does NOT assume or prove that number-theoretic estimate.  Instead it does three
things without `sorry` or a project axiom:

1. gives a Lean source-facing schema for the already-recombined primitive block Z_q^HB and
   the normalized interior finite second moment written schematically in Turn 418, Eq. (6631);
2. states the literal limsup target of Eq. (6635);
3. proves that an eventual finite mean-square certificate with any fixed constant strictly
   below 4.489e-5 implies the literal limsup target, and proves the downstream numerical
   implication to the Lean-safe interior coefficient 1.0067.

Thus a clean run certifies the RETARGETING and the dependency arrows around item 13.  It
must not be described as closing item 13.  Item 13 closes only when the finite mean-square
certificate below is proved for the actual Turn-415/418 Heath--Brown coefficient.

Anti-loop rule
--------------
`ZHB` below is intended to be instantiated by the exact recombined coefficient after the
Turn-415 branch sum and Gauss-pair cancellation.  No theorem in this file replaces that
coefficient by an arbitrary factorable vector, inserts absolute values inside the HB branch
sum, or performs Cauchy before the arithmetic cancellation.
-/

namespace TwinPrimeRun10b

set_option autoImplicit false
open scoped BigOperators
open Filter

noncomputable section

/-- Turn 418's allowed square-root variance margin: 0.0067. -/
def turn418Delta : ℝ := (67 : ℝ) / 10000

/-- Turn 418, Eq. (6633): (0.0067)^2 = 4.489e-5. -/
def turn418VarianceThreshold : ℝ := turn418Delta ^ 2

/-- Turn 418, Eq. (6615): the Lean-safe interior relative coefficient. -/
def turn418SafeK : ℝ := 1 + turn418Delta

/--
Source-facing data for Turn 418, Eq. (6631).

* `interiorModuli Y` is the actual finite q-family on the Turn-397 interior band.
* `ZHB q` is the actual RECOMBINED primitive HB block of Turn 418, Eq. (6630), after
  the Turn-415 Gauss-pair cancellation and after the already-separated singular and
  conductor-drop pieces have been handled in the source decomposition.
* `normalisation Y` is the positive Turn-397 normalisation N(Y).

The purpose of this structure is not to enlarge the coefficient class.  A certification
instance must be filled with the source-defined objects.
-/
structure HBInteriorData where
  interiorModuli : ℕ → Finset ℕ
  ZHB : ℕ → ℂ
  normalisation : ℕ → ℝ
  normalisation_pos : ∀ Y : ℕ, 0 < normalisation Y

/-- A source-facing finite second-moment schema matching Turn 418, Eq. (6631). -/
def HBInteriorData.variance (D : HBInteriorData) (Y : ℕ) : ℝ :=
  (D.interiorModuli Y).sum (fun q => ‖D.ZHB q‖ ^ 2) / D.normalisation Y

/-- The literal Turn-418 analytic target, Eq. (6635). -/
def Turn418HBInteriorTarget (D : HBInteriorData) : Prop :=
  Filter.limsup D.variance Filter.atTop < turn418VarianceThreshold

/--
A finite-Y version of the missing number-theoretic theorem.

This asks for a fixed margin `c < 4.489e-5` such that, for all sufficiently large Y,
the ACTUAL recombined HB second moment is at most `c * N(Y)`.
Proving this certificate for the source-defined data is genuine new analytic work.
-/
def Turn418FiniteMeanSquareCertificate (D : HBInteriorData) : Prop :=
  ∃ c : ℝ,
    c < turn418VarianceThreshold ∧
      ∀ᶠ Y : ℕ in Filter.atTop,
        (D.interiorModuli Y).sum (fun q => ‖D.ZHB q‖ ^ 2)
          ≤ c * D.normalisation Y

/-- The source variance is nonnegative at every finite Y. -/
theorem hbInteriorVariance_nonneg (D : HBInteriorData) (Y : ℕ) :
    0 ≤ D.variance Y := by
  unfold HBInteriorData.variance
  have hsum :
      0 ≤ (D.interiorModuli Y).sum (fun q => ‖D.ZHB q‖ ^ 2) := by
    apply Finset.sum_nonneg
    intro q hq
    exact sq_nonneg ‖D.ZHB q‖
  exact div_nonneg hsum (le_of_lt (D.normalisation_pos Y))

/-- Exact rational value of Turn 418's variance threshold. -/
theorem turn418VarianceThreshold_exact :
    turn418VarianceThreshold = (4489 : ℝ) / 100000000 := by
  norm_num [turn418VarianceThreshold, turn418Delta]

/-- Exact rational value of the Lean-safe coefficient 1.0067. -/
theorem turn418SafeK_exact :
    turn418SafeK = (10067 : ℝ) / 10000 := by
  norm_num [turn418SafeK, turn418Delta]

/--
The finite mean-square certificate implies the literal limsup statement (6635).
This is the exact bridge we want before attempting the hard arithmetic estimate.
-/
theorem finiteMeanSquareCertificate_implies_Turn418_target
    (D : HBInteriorData)
    (hcert : Turn418FiniteMeanSquareCertificate D) :
    Turn418HBInteriorTarget D := by
  rcases hcert with ⟨c, hc, hmean⟩
  have hvar : ∀ᶠ Y : ℕ in Filter.atTop, D.variance Y ≤ c := by
    filter_upwards [hmean] with Y hY
    unfold HBInteriorData.variance
    exact (div_le_iff₀ (D.normalisation_pos Y)).2 hY
  have hcob :
      Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y)
        Filter.atTop D.variance := by
    exact Filter.isCoboundedUnder_le_of_le Filter.atTop
      (fun Y => hbInteriorVariance_nonneg D Y)
  have hlim : Filter.limsup D.variance Filter.atTop ≤ c :=
    Filter.limsup_le_of_le hcob hvar
  exact lt_of_le_of_lt hlim hc

/--
Turn 418, Eqs. (6632)--(6633): once the coefficient-specific limsup variance is below
(0.0067)^2, the variance-to-coefficient implication gives K_int < 1.0067.

`hK` is the already-audited Turn-397 variance implication.  The only analytic input here is
`hTarget`, the literal Turn-418 target.
-/
theorem Turn418_target_implies_safe_interior_coefficient
    (D : HBInteriorData)
    {Kint : ℝ}
    (hlim_nonneg : 0 ≤ Filter.limsup D.variance Filter.atTop)
    (hK : Kint ≤ 1 + Real.sqrt (Filter.limsup D.variance Filter.atTop))
    (hTarget : Turn418HBInteriorTarget D) :
    Kint < turn418SafeK := by
  have hdelta : 0 < turn418Delta := by
    norm_num [turn418Delta]
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (Filter.limsup D.variance Filter.atTop) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      (Real.sqrt (Filter.limsup D.variance Filter.atTop)) ^ 2 =
        Filter.limsup D.variance Filter.atTop :=
    Real.sq_sqrt hlim_nonneg
  have hvar :
      Filter.limsup D.variance Filter.atTop < turn418Delta ^ 2 := by
    simpa [Turn418HBInteriorTarget, turn418VarianceThreshold] using hTarget
  have hsqrt_lt :
      Real.sqrt (Filter.limsup D.variance Filter.atTop) < turn418Delta := by
    nlinarith
  unfold turn418SafeK
  nlinarith

/--
Run-10b dependency capstone: a source-faithful finite HB mean-square certificate is enough
for the Turn-418 limsup target and, through the existing Turn-397 variance implication, for
the safe coefficient threshold.

This theorem is deliberately conditional on the finite HB mean-square certificate.  Therefore
a clean axiom report for this capstone DOES NOT close item 13 by itself.
-/
theorem run10b_dependency_capstone
    (D : HBInteriorData)
    {Kint : ℝ}
    (hcert : Turn418FiniteMeanSquareCertificate D)
    (hlim_nonneg : 0 ≤ Filter.limsup D.variance Filter.atTop)
    (hK : Kint ≤ 1 + Real.sqrt (Filter.limsup D.variance Filter.atTop)) :
    Turn418HBInteriorTarget D ∧ Kint < turn418SafeK := by
  have hTarget := finiteMeanSquareCertificate_implies_Turn418_target D hcert
  exact ⟨hTarget,
    Turn418_target_implies_safe_interior_coefficient D hlim_nonneg hK hTarget⟩

-- Source/target visibility checks.
#check HBInteriorData.variance
#check Turn418HBInteriorTarget
#check Turn418FiniteMeanSquareCertificate
#check finiteMeanSquareCertificate_implies_Turn418_target
#check Turn418_target_implies_safe_interior_coefficient
#check run10b_dependency_capstone

-- Decisive axiom audit.  A clean run should contain no `sorryAx` and no project axiom.
#print axioms hbInteriorVariance_nonneg
#print axioms turn418VarianceThreshold_exact
#print axioms turn418SafeK_exact
#print axioms finiteMeanSquareCertificate_implies_Turn418_target
#print axioms Turn418_target_implies_safe_interior_coefficient
#print axioms run10b_dependency_capstone

end
end TwinPrimeRun10b
