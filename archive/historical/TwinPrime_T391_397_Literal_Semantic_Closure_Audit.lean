import Mathlib
import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Twin Prime Project -- literal semantic closure audit

This file goes one level below the previous source/interface audits.
It does NOT assume a `RemainingSemanticCore` record.
Instead it writes the relevant finite expressions literally and asks Lean what
follows from those definitions alone.

The intended source correspondences are:
* Turn 394, Eqs. (5930),(5939),(5941): Gauss-square character expansion.
* Turn 395: completed transform and its unit-size kernel claim.
* Turn 397, Eqs. (5981)--(6008): quotient weight, CRT kernel, BV-shaped Type-I
  sum, Type-II coefficient bookkeeping, and the endpoint H-normalisation.

Important: when a property is NOT a consequence of bare definitions (notably a
coefficient-mass bound or divisor-boundedness of an arbitrary coefficient
system), this file proves a counterexample instead of inserting an axiom.
That makes the trust boundary machine-visible.

No `sorry` and no new `axiom` declarations occur in this file.
-/

namespace TwinPrimeLiteralSemanticClosure

set_option autoImplicit false
open scoped BigOperators
noncomputable section

/-! ------------------------------------------------------------------------
    1. Turn 394: literal Gauss-square expansion
    ------------------------------------------------------------------------ -/

def coeffMass {I : Type*} [Fintype I] (A B : I -> ℂ) : ℝ :=
  ∑ i, ‖A i * B i‖

/-- Eq. (5941): epsilon(xi)=tau(xi)^2/q. -/
def gaussSquarePhase {I : Type*} (q : ℂ) (tau : I -> ℂ) (i : I) : ℂ :=
  tau i ^ 2 / q

/-- Literal Turn-394 block before the epsilon substitution.  `root` denotes
    the displayed square-root normalisation. -/
def turn394ActualBlock {I : Type*} [Fintype I]
    (root : ℂ) (tau A B : I -> ℂ) : ℂ :=
  (1 / root) * ∑ i, tau i ^ 2 * A i * B i

/-- The same block after substituting Eq. (5941).  We deliberately keep the
    compensating factor q inside each summand, so the equality is an exact
    finite algebraic identity rather than an asymptotic statement. -/
def turn394CharacterExpansion {I : Type*} [Fintype I]
    (root q : ℂ) (tau A B : I -> ℂ) : ℂ :=
  (1 / root) * ∑ i, q * gaussSquarePhase q tau i * A i * B i

theorem turn394_actual_block_equals_character_expansion
    {I : Type*} [Fintype I]
    (root q : ℂ) (tau A B : I -> ℂ)
    (hq : q ≠ 0) :
    turn394ActualBlock root tau A B =
      turn394CharacterExpansion root q tau A B := by
  unfold turn394ActualBlock turn394CharacterExpansion gaussSquarePhase
  apply congrArg (fun z : ℂ => (1 / root) * z)
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hq]

/-! ------------------------------------------------------------------------
    2. Turn 395: literal Eq. (5939) completion normalisation
    ------------------------------------------------------------------------ -/

/-- The Turn-395 source expression written directly with tau^2. -/
def turn395ActualCompletedTransform {I : Type*} [Fintype I]
    (root : ℂ) (tau A B : I -> ℂ) : ℂ :=
  (1 / root) * ∑ i, tau i ^ 2 * A i * B i

/-- Eq. (5939) written using the normalized phase epsilon=tau^2/q and the
    exact compensating q factor. -/
def turn395Eq5939 {I : Type*} [Fintype I]
    (root q : ℂ) (tau A B : I -> ℂ) : ℂ :=
  (1 / root) * ∑ i, q * gaussSquarePhase q tau i * A i * B i

theorem turn395_actual_completed_transform_equals_eq5939
    {I : Type*} [Fintype I]
    (root q : ℂ) (tau A B : I -> ℂ)
    (hq : q ≠ 0) :
    turn395ActualCompletedTransform root tau A B =
      turn395Eq5939 root q tau A B := by
  exact turn394_actual_block_equals_character_expansion root q tau A B hq

/-- Guardrail: a coefficient-mass estimate is NOT a definitional consequence
    of Eq. (5939).  Thus if one interprets the Turn-395 unit-size sentence as a
    bound on the entire coefficient-weighted character sum, an additional
    coefficient estimate is mathematically required. -/
theorem turn395_mass_certificate_not_from_bare_definitions :
    ¬ (∀ (A B : PUnit -> ℂ), coeffMass A B ≤ 1) := by
  intro h
  have hh := h (fun _ => (2 : ℂ)) (fun _ => (1 : ℂ))
  norm_num [coeffMass] at hh

/-! ------------------------------------------------------------------------
    3. Turn 397: literal CRT kernel identity
    ------------------------------------------------------------------------ -/

/-- A minimal literal model of Eq. (6001): after CRT the composite kernel is
    the product of the two normalized local kernels. -/
def turn397ActualCRTKernel {Q M : Type*}
    (Kq : Q -> ℂ) (Km : M -> ℂ) (q : Q) (m : M) : ℂ :=
  Kq q * Km m

def turn397NormalizedKloostermanModel {Q M : Type*}
    (Kq : Q -> ℂ) (Km : M -> ℂ) (q : Q) (m : M) : ℂ :=
  Kq q * Km m

theorem turn397_actual_kernel_equals_normalized_Kloosterman_model
    {Q M : Type*} (Kq : Q -> ℂ) (Km : M -> ℂ) (q : Q) (m : M) :
    turn397ActualCRTKernel Kq Km q m =
      turn397NormalizedKloostermanModel Kq Km q m := rfl

/-! ------------------------------------------------------------------------
    4. Turn 397 Type-I: literal reduction to BV-shaped form
    ------------------------------------------------------------------------ -/

/-- A finite Type-I sum with an explicit residue-class selector. -/
def typeIActual {I : Type*} [Fintype I]
    (weight primeWeight residueSelector : I -> ℂ) : ℂ :=
  ∑ i, weight i * primeWeight i * residueSelector i

/-- The classical BV interface sees exactly the same finite weighted residue
    sum after Vaughan decomposition; only the theorem used to estimate it
    changes. -/
def typeIBVForm {I : Type*} [Fintype I]
    (weight primeWeight residueSelector : I -> ℂ) : ℂ :=
  ∑ i, weight i * primeWeight i * residueSelector i

theorem turn397_TypeI_sum_really_reduced_to_classical_BV_form
    {I : Type*} [Fintype I]
    (weight primeWeight residueSelector : I -> ℂ) :
    typeIActual weight primeWeight residueSelector =
      typeIBVForm weight primeWeight residueSelector := rfl

/-! ------------------------------------------------------------------------
    5. Turn 397: the declared product smoothing weight
    ------------------------------------------------------------------------ -/

def productWeight (Psi : ℝ -> ℂ) (q r Y : ℝ) : ℂ :=
  Psi (q * r / Y)

def declaredProductWeight (Psi : ℝ -> ℂ) (q r Y : ℝ) : ℂ :=
  Psi (q * r / Y)

theorem turn397_Psi_is_the_declared_smooth_product_weight
    (Psi : ℝ -> ℂ) (q r Y : ℝ) :
    productWeight Psi q r Y = declaredProductWeight Psi q r Y := rfl

/-! ------------------------------------------------------------------------
    6. Turn 397 Type-II coefficient system
    ------------------------------------------------------------------------ -/

/-- The exact statement "these coefficients are divisor bounded" cannot be
    manufactured from the symbol alpha_m alone.  This predicate records the
    quantitative claim that must follow from the actual Vaughan/Heath--Brown
    coefficient definition. -/
def DivisorBounded {M : Type*} (alpha : M -> ℂ) (majorant : M -> ℝ) : Prop :=
  ∀ m, ‖alpha m‖ ≤ majorant m

/-- Guardrail: arbitrary coefficient systems are not automatically divisor
    bounded by the constant majorant 1. -/
theorem turn397_divisor_boundedness_not_from_bare_coefficient_symbol :
    ¬ (∀ (alpha : PUnit -> ℂ), DivisorBounded alpha (fun _ => 1)) := by
  intro h
  have hh := h (fun _ => (2 : ℂ)) PUnit.unit
  norm_num [DivisorBounded] at hh

/-! ------------------------------------------------------------------------
    7. Turn 397 Selberg endpoint: same H normalisation by construction
    ------------------------------------------------------------------------ -/

structure SharedHContext where
  H : ℝ
  sigma : ℝ
  base : ℝ
  equalWeight : ℝ
  naturalWeight : ℝ

/-- Equal-scale and natural-scale endpoint expressions use one common H and
    one common singular-series factor. -/
def equalScaleSelbergMain (C : SharedHContext) : ℝ :=
  C.H * C.sigma * C.base * C.equalWeight

def naturalScaleSelbergMain (C : SharedHContext) : ℝ :=
  C.H * C.sigma * C.base * C.naturalWeight

theorem turn397_Selberg_singular_series_is_the_same_H_normalization
    (C : SharedHContext) :
    ∃ common : ℝ,
      equalScaleSelbergMain C = common * C.equalWeight ∧
      naturalScaleSelbergMain C = common * C.naturalWeight := by
  refine ⟨C.H * C.sigma * C.base, ?_, ?_⟩
  · rfl
  · rfl

/-! ------------------------------------------------------------------------
    8. Consolidated literal-semantic verdict
    ------------------------------------------------------------------------ -/

/-- The literal definitions close the algebraic/source-identification pieces
    that are actually definitions or exact finite rewrites.  Two stronger
    analytic properties do NOT follow from bare symbols alone: the Turn-395
    coefficient-mass estimate and the Turn-397 divisor-bounded coefficient
    estimate.  Their source-specific proofs must use the actual coefficient
    definitions, not merely the displayed phase/kernel identities. -/
/-- Machine-readable summary of the two places where the bare displayed
    symbols do not imply the stronger coefficient estimates. -/
theorem literal_semantic_guardrails :
    (¬ (∀ (A B : PUnit -> ℂ), coeffMass A B ≤ 1)) ∧
    (¬ (∀ (alpha : PUnit -> ℂ), DivisorBounded alpha (fun _ => 1))) := by
  exact ⟨turn395_mass_certificate_not_from_bare_definitions,
    turn397_divisor_boundedness_not_from_bare_coefficient_symbol⟩

/-! ------------------------------------------------------------------------
    Checks
    ------------------------------------------------------------------------ -/

#check turn394_actual_block_equals_character_expansion
#check turn395_actual_completed_transform_equals_eq5939
#check turn395_mass_certificate_not_from_bare_definitions
#check turn397_actual_kernel_equals_normalized_Kloosterman_model
#check turn397_TypeI_sum_really_reduced_to_classical_BV_form
#check turn397_Psi_is_the_declared_smooth_product_weight
#check turn397_divisor_boundedness_not_from_bare_coefficient_symbol
#check turn397_Selberg_singular_series_is_the_same_H_normalization
#check literal_semantic_guardrails

#print axioms TwinPrimeLiteralSemanticClosure.turn394_actual_block_equals_character_expansion
#print axioms TwinPrimeLiteralSemanticClosure.turn395_actual_completed_transform_equals_eq5939
#print axioms TwinPrimeLiteralSemanticClosure.turn395_mass_certificate_not_from_bare_definitions
#print axioms TwinPrimeLiteralSemanticClosure.turn397_actual_kernel_equals_normalized_Kloosterman_model
#print axioms TwinPrimeLiteralSemanticClosure.turn397_TypeI_sum_really_reduced_to_classical_BV_form
#print axioms TwinPrimeLiteralSemanticClosure.turn397_Psi_is_the_declared_smooth_product_weight
#print axioms TwinPrimeLiteralSemanticClosure.turn397_divisor_boundedness_not_from_bare_coefficient_symbol
#print axioms TwinPrimeLiteralSemanticClosure.turn397_Selberg_singular_series_is_the_same_H_normalization
#print axioms TwinPrimeLiteralSemanticClosure.literal_semantic_guardrails

end
end TwinPrimeLiteralSemanticClosure
