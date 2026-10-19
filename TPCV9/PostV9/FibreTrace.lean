import Mathlib

/-!
# TP120: audit the particular completed fibre, not arbitrary hypothetical fibres

This file makes the *actual source-to-trace claim* into a proof obligation.
The finite Gram opening is proved below. The required equality from the
source-defined completion to the proposed normalized CRT kernel is NOT asserted
by `rfl`, an opaque structure field, or a fresh axiom.

To turn this into a certification of the paper, instantiate Source with the
literal q,m,h,k arithmetic, including the Heath--Brown weights, the complete
Kloosterman sum, the singular mask, and the normalized paired trace. Then
prove the named predicates at the bottom for that specific instantiation.

No theorem in this file establishes the missing analytic estimates.
No `sorry`, `admit`, or project-specific axiom is present.
-/

namespace TP120ActualFibre

set_option autoImplicit false
open scoped BigOperators
noncomputable section

section FiniteGram
variable {Q M : Type*} [Fintype Q] [Fintype M]

/-- The exact finite Hermitian moment. -/
def moment (Z : Q -> M -> ℂ) : ℂ :=
  ∑ q, (∑ m, Z q m) * (∑ m, star (Z q m))

/-- The opened pair moment with no Cauchy inequality. -/
def opened (Z : Q -> M -> ℂ) : ℂ :=
  ∑ q, ∑ m1, ∑ m2, Z q m1 * star (Z q m2)

theorem moment_eq_opened (Z : Q -> M -> ℂ) :
    moment Z = opened Z := by
  unfold moment opened
  apply Finset.sum_congr rfl
  intro q hq
  calc
    (∑ m, Z q m) * (∑ m, star (Z q m))
        = ∑ m1, Z q m1 * (∑ m2, star (Z q m2)) := by
            rw [Finset.sum_mul]
    _ = ∑ m1, ∑ m2, Z q m1 * star (Z q m2) := by
            apply Finset.sum_congr rfl
            intro m1 hm1
            rw [Finset.mul_sum]

end FiniteGram

section LiteralCompletedSource
/-- All raw data needed to reconstruct the particular completed source.
    These fields are *functions*, not asserted theorems. -/
structure Source (Q M H K : Type*) where
  alpha : M -> ℂ
  c : Q -> M -> ℂ
  S : Q -> M -> H -> K -> ℂ
  C : Q -> M -> H -> K -> ℂ
  regular : Q -> M -> H -> K -> Bool
  lambda : Q -> ℂ
  dyadicQ : ℂ
  normalizedPairKernel : Q -> M -> M -> ℂ

variable {Q M H K : Type*}
variable [Fintype Q] [Fintype M] [Fintype H] [Fintype K]

/-- Literal `c^{-2} sum_{h,k} S(h,k;c) C(h,k)` fibre. -/
def rawFibre (D : Source Q M H K)
    (q : Q) (m : M) : ℂ :=
  ((D.c q m)⁻¹) ^ 2 *
    ∑ h, ∑ k, D.S q m h k * D.C q m h k

/-- Same literal completion after explicitly retaining a regular-frequency mask. -/
def regularFibre (D : Source Q M H K)
    (q : Q) (m : M) : ℂ :=
  ((D.c q m)⁻¹) ^ 2 *
    ∑ h, ∑ k,
      if D.regular q m h k then D.S q m h k * D.C q m h k else 0

/-- Source-defined total moment. -/
def rawMoment (D : Source Q M H K) : ℂ :=
  moment (fun q m => D.alpha m * rawFibre D q m)

/-- Regular-only moment: exceptional/mixed contributions are kept separate. -/
def regularMoment
    (D : Source Q M H K) : ℂ :=
  moment (fun q m => D.alpha m * regularFibre D q m)

/-- An exact ledger for everything excluded from the regular moment,
    including mixed regular/singular products. -/
def excludedMoment
    (D : Source Q M H K) : ℂ :=
  rawMoment D - regularMoment D

theorem rawMoment_exact_split
    (D : Source Q M H K) :
    rawMoment D = regularMoment D + excludedMoment D := by
  unfold excludedMoment
  ring

theorem rawMoment_opens_without_Cauchy
    (D : Source Q M H K) :
    rawMoment D = opened (fun q m => D.alpha m * rawFibre D q m) :=
  moment_eq_opened _

/-- Precisely the RHS asserted in manuscript v9, Section 10. -/
def proposedTrace
    (D : Source Q M H K) : ℂ :=
  ∑ m1, ∑ m2,
    (D.alpha m1 * star (D.alpha m2)) *
      (∑ q, D.lambda q * D.normalizedPairKernel q m1 m2)

/-- PENDING, source-specific exact trace identity.
    This is NOT an identity for all possible Source instances. -/
def RequiredActualTraceIdentity
    (D : Source Q M H K) : Prop :=
  regularMoment D = D.dyadicQ * proposedTrace D

/-- PENDING, the actual *paired* kernel bound, not the individual-fibre Weil
    bound. One must derive this from the source and CRT arithmetic. -/
def RequiredPairedKernelBound
    (D : Source Q M H K)
    (B : ℝ) : Prop :=
  ∀ q m1 m2, ‖D.normalizedPairKernel q m1 m2‖ ≤ B

/-- PENDING, required smallness of the entire exceptional/mixed ledger. -/
def RequiredExceptionalBound
    (D : Source Q M H K)
    (E : ℝ) : Prop :=
  ‖excludedMoment D‖ ≤ E

/-- A valid bridge can be applied once an ACTUAL proof has been supplied.
    Deliberately neither hTrace nor its proof is manufactured in this file. -/
theorem trace_identity_if_proved
    (D : Source Q M H K)
    (hTrace : RequiredActualTraceIdentity D) :
    rawMoment D = D.dyadicQ * proposedTrace D + excludedMoment D := by
  rw [rawMoment_exact_split, hTrace]

#check rawMoment_exact_split
#check rawMoment_opens_without_Cauchy
#check RequiredActualTraceIdentity
#check RequiredPairedKernelBound
#check RequiredExceptionalBound
#check trace_identity_if_proved
#print axioms rawMoment_exact_split
#print axioms rawMoment_opens_without_Cauchy
#print axioms trace_identity_if_proved

end LiteralCompletedSource
end
end TP120ActualFibre
