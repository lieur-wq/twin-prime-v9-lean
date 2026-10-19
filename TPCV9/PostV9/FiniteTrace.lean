import Mathlib

/-!
# Turn 128 -- manuscript v9, Section 7, finite trace audit

This is a MANUSCRIPT-SPECIFIC replacement for the unfair Turn-127
`exact?` attempt at proving all of TPC.  It tests only the exact
algebra and coefficient majorant between equations (Vtrace), (Tkernel)
and (Tbound) of the submitted v9 source.

The completed Z-fibres, q-weights, coefficient family and normalized paired
kernel are passed as actual mathematical functions, not arbitrary Prop fields.
The real analytic inputs are displayed as explicit inequalities:
  * the bound on the specific normalized paired kernel (Kbound);
  * the q-prime weight mass;
  * the coefficient L2 energy.
Their applicability to the source-defined completed arithmetic kernel must
be justified using the manuscript's CRT/Weil/Heath--Brown argument; this file
does NOT claim to check that identification or the full TPC proof.

No external theorem is re-proved, no opaque ``TPC source packet'' is assumed,
no theorem-search tactic is asked to prove TPC, and there is no `sorry` or `axiom`.
An error in this file is not, by itself, a counterexample to the manuscript.
-/

namespace TP128V9Section7

set_option autoImplicit false
open scoped BigOperators
noncomputable section

variable {QIdx MIdx : Type*} [Fintype QIdx] [Fintype MIdx]

/-- Actual algebraic shape of the SECOND MOMENT before opening in m1,m2. -/
def closedPairedMoment
    (alpha : MIdx -> Complex) (Z : QIdx -> MIdx -> Complex) : Complex :=
  ∑ q, (∑ m, alpha m * Z q m) *
    (∑ m, star (alpha m * Z q m))

/-- The same finite second moment with the m1,m2 sum opened BEFORE Cauchy. -/
def openPairedMoment
    (alpha : MIdx -> Complex) (Z : QIdx -> MIdx -> Complex) : Complex :=
  ∑ q, ∑ m1, ∑ m2,
    (alpha m1 * Z q m1) * star (alpha m2 * Z q m2)

/-- Exact Gram opening. Nothing is bounded fibrewise in this step. -/
theorem closed_eq_opened
    (alpha : MIdx -> Complex) (Z : QIdx -> MIdx -> Complex) :
    closedPairedMoment alpha Z = openPairedMoment alpha Z := by
  unfold closedPairedMoment openPairedMoment
  apply Finset.sum_congr rfl
  intro q hq
  calc
    (∑ m, alpha m * Z q m) * (∑ m, star (alpha m * Z q m))
        = ∑ m1, (alpha m1 * Z q m1) *
            (∑ m2, star (alpha m2 * Z q m2)) := by
              rw [Finset.sum_mul]
    _ = ∑ m1, ∑ m2,
          (alpha m1 * Z q m1) * star (alpha m2 * Z q m2) := by
            apply Finset.sum_congr rfl
            intro m1 hm1
            rw [Finset.mul_sum]

/-- The orientation alpha(m1) * conjugate(alpha(m2)) in v9 is literal. -/
theorem open_eq_coefficients_times_paired_fibres
    (alpha : MIdx -> Complex) (Z : QIdx -> MIdx -> Complex) :
    openPairedMoment alpha Z =
      ∑ q, ∑ m1, ∑ m2,
        alpha m1 * star (alpha m2) *
          (Z q m1 * star (Z q m2)) := by
  unfold openPairedMoment
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro m1 hm1
  apply Finset.sum_congr rfl
  intro m2 hm2
  rw [star_mul']
  ring

/-- The exact finite trace object in v9 (Tkernel).
    K is specifically the normalized OPENED correlation kernel, not a fibre. -/
def traceT
    (lambda : QIdx -> Complex)
    (alpha : MIdx -> Complex)
    (K : QIdx -> MIdx -> MIdx -> Complex) : Complex :=
  ∑ q, lambda q *
    (∑ m1, ∑ m2, alpha m1 * star (alpha m2) * K q m1 m2)

/-- The finite coefficient Cauchy inequality used AFTER the paired trace bound. -/
theorem finite_cauchy_for_alpha
    (alpha : MIdx -> Complex) :
    (∑ m, ‖alpha m‖) ^ 2 ≤
      (Fintype.card MIdx : Real) * ∑ m, ‖alpha m‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq
    (s := Finset.univ)
    (fun _m : MIdx => (1 : Real))
    (fun m : MIdx => ‖alpha m‖)
  simpa using h

/-- This is the precise one-q triangle inequality using the claimed (Kbound). -/
theorem one_q_trace_bound
    (alpha : MIdx -> Complex) (K : MIdx -> MIdx -> Complex)
    (B : Real) (hK : ∀ m1 m2, ‖K m1 m2‖ ≤ B) :
    ‖∑ m1, ∑ m2, alpha m1 * star (alpha m2) * K m1 m2‖ ≤
      B * (∑ m, ‖alpha m‖) ^ 2 := by
  classical
  calc
    ‖∑ m1, ∑ m2, alpha m1 * star (alpha m2) * K m1 m2‖
        ≤ ∑ m1, ‖∑ m2, alpha m1 * star (alpha m2) * K m1 m2‖ :=
          norm_sum_le _ _
    _ ≤ ∑ m1, ∑ m2, ‖alpha m1 * star (alpha m2) * K m1 m2‖ := by
          apply Finset.sum_le_sum
          intro m1 hm1
          exact norm_sum_le _ _
    _ = ∑ m1, ∑ m2,
          ‖alpha m1‖ * ‖alpha m2‖ * ‖K m1 m2‖ := by
            apply Finset.sum_congr rfl
            intro m1 hm1
            apply Finset.sum_congr rfl
            intro m2 hm2
            simp [norm_mul, norm_star, mul_assoc]
    _ ≤ ∑ m1, ∑ m2, ‖alpha m1‖ * ‖alpha m2‖ * B := by
          apply Finset.sum_le_sum
          intro m1 hm1
          apply Finset.sum_le_sum
          intro m2 hm2
          exact mul_le_mul_of_nonneg_left (hK m1 m2)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = B * (∑ m, ‖alpha m‖) ^ 2 := by
          have hinner (m1 : MIdx) :
              (∑ m2 : MIdx, ‖alpha m1‖ * ‖alpha m2‖ * B) =
                ‖alpha m1‖ * (∑ m2 : MIdx, ‖alpha m2‖) * B := by
            rw [← Finset.sum_mul]
            rw [← Finset.mul_sum]
          simp_rw [hinner]
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          ring

/-- Exactly the q-weighted triangle step preceding v9 (Tbound). -/
theorem trace_bound_before_coefficient_cauchy
    (lambda : QIdx -> Complex) (alpha : MIdx -> Complex)
    (K : QIdx -> MIdx -> MIdx -> Complex)
    (B : Real) (hK : ∀ q m1 m2, ‖K q m1 m2‖ ≤ B) :
    ‖traceT lambda alpha K‖ ≤
      (∑ q, ‖lambda q‖) * B * (∑ m, ‖alpha m‖) ^ 2 := by
  classical
  unfold traceT
  calc
    ‖∑ q, lambda q *
        (∑ m1, ∑ m2, alpha m1 * star (alpha m2) * K q m1 m2)‖
        ≤ ∑ q, ‖lambda q *
          (∑ m1, ∑ m2, alpha m1 * star (alpha m2) * K q m1 m2)‖ :=
            norm_sum_le _ _
    _ = ∑ q, ‖lambda q‖ *
          ‖∑ m1, ∑ m2, alpha m1 * star (alpha m2) * K q m1 m2‖ := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [norm_mul]
    _ ≤ ∑ q, ‖lambda q‖ *
          (B * (∑ m, ‖alpha m‖) ^ 2) := by
              apply Finset.sum_le_sum
              intro q hq
              exact mul_le_mul_of_nonneg_left
                (one_q_trace_bound alpha (K q) B (hK q))
                (norm_nonneg _)
    _ = (∑ q, ‖lambda q‖) * B * (∑ m, ‖alpha m‖) ^ 2 := by
          rw [← Finset.sum_mul]
          ring

/-- Finite (Tbound) consequence, with THREE displayed analytic inputs.
    Every input has exactly its mathematical content; no opaque proposition
    stands for a conclusion to be proved. -/
theorem finite_Tbound_v9
    (lambda : QIdx -> Complex) (alpha : MIdx -> Complex)
    (K : QIdx -> MIdx -> MIdx -> Complex)
    (B LambdaMass L2 : Real)
    (hB : 0 ≤ B) (hLambda : 0 ≤ LambdaMass)
    (hKernel : ∀ q m1 m2, ‖K q m1 m2‖ ≤ B)
    (hQMass : (∑ q, ‖lambda q‖) ≤ LambdaMass)
    (hCoeffEnergy : (∑ m, ‖alpha m‖ ^ 2) ≤ L2) :
    ‖traceT lambda alpha K‖ ≤
      LambdaMass * B * ((Fintype.card MIdx : Real) * L2) := by
  have hcard : 0 ≤ (Fintype.card MIdx : Real) := by positivity
  have hL1 : (∑ m, ‖alpha m‖) ^ 2 ≤
      (Fintype.card MIdx : Real) * L2 := by
    calc
      (∑ m, ‖alpha m‖) ^ 2
          ≤ (Fintype.card MIdx : Real) * ∑ m, ‖alpha m‖ ^ 2 :=
            finite_cauchy_for_alpha alpha
      _ ≤ (Fintype.card MIdx : Real) * L2 :=
          mul_le_mul_of_nonneg_left hCoeffEnergy hcard
  have hTrace := trace_bound_before_coefficient_cauchy
    lambda alpha K B hKernel
  calc
    ‖traceT lambda alpha K‖
        ≤ (∑ q, ‖lambda q‖) * B * (∑ m, ‖alpha m‖) ^ 2 := hTrace
    _ ≤ LambdaMass * B * (∑ m, ‖alpha m‖) ^ 2 := by
          have hQB : (∑ q, ‖lambda q‖) * B ≤ LambdaMass * B :=
            mul_le_mul_of_nonneg_right hQMass hB
          have hsq : 0 ≤ (∑ m, ‖alpha m‖) ^ 2 := sq_nonneg _
          exact mul_le_mul_of_nonneg_right hQB hsq
    _ ≤ LambdaMass * B * ((Fintype.card MIdx : Real) * L2) := by
          have hLB : 0 ≤ LambdaMass * B := mul_nonneg hLambda hB
          exact mul_le_mul_of_nonneg_left hL1 hLB

#check closed_eq_opened
#check open_eq_coefficients_times_paired_fibres
#check traceT
#check finite_Tbound_v9

#print axioms TP128V9Section7.closed_eq_opened
#print axioms TP128V9Section7.open_eq_coefficients_times_paired_fibres
#print axioms TP128V9Section7.finite_Tbound_v9

end
end TP128V9Section7
