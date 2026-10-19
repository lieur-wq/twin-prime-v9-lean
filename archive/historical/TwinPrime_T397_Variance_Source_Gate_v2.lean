import Mathlib
import Mathlib.Analysis.Fourier.ZMod

namespace TwinPrimeT397VarianceSource

set_option autoImplicit false
open scoped BigOperators
open Finset AddChar ZMod
noncomputable section

/-!
Turn 397 source-level VARIANCE gate.

This file targets the step behind Eqs. (5999)--(6004), not merely the
algebra after one has postulated V <= Q*T + diagonal + singular.

It checks four structural facts which are easy to lose in prose:

  1. completion with the ZMod Fourier normalization contributes exactly ONE
     modulus factor (Parseval is proved directly below);
  2. singular and nonsingular Fourier frequencies form an exact energy
     partition -- no frequency term disappears;
  3. diagonal / singular-off-diagonal / nonsingular-off-diagonal pair terms
     form an exact three-way finite partition;
  4. the schematic nonsingular T in (5999) obeys the exact finite triangle
     majorant underlying (6002), and Cauchy converts the l1 coefficient norm
     to the stated cardinality times l2 norm.

The genuinely number-theoretic source inputs are deliberately left visible:
pointwise Weil for the normalized Kloosterman kernel, the prime-weight mass
bound, the divisor-bound/l2 estimate for the Type-II coefficients, and the
identification of the actual completed block with the finite Fourier model.
No axiom declarations and no `sorry` occur in this file.
-/

/-! ## A. Exact Fourier completion factor -/

/-- Additive-character orthogonality in the normalization used by ZMod.dft. -/
theorem stdAddChar_orthogonality
    {L : ℕ} [NeZero L] (t : ZMod L) :
    (∑ k : ZMod L, ZMod.stdAddChar (t * k)) =
      if t = 0 then (L : ℂ) else 0 := by
  split_ifs with ht
  · simp only [ht, zero_mul, map_zero_eq_one, sum_const, card_univ, ZMod.card,
      nsmul_eq_mul, mul_one]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L ht)

/-- Conjugating the negative standard character reverses the sign. -/
theorem star_stdAddChar_neg
    {L : ℕ} [NeZero L] (a : ZMod L) :
    (starRingEnd ℂ) (ZMod.stdAddChar (-a)) = ZMod.stdAddChar a := by
  simp only [ZMod.stdAddChar_apply]
  rw [← Circle.coe_inv_eq_conj]
  rw [AddChar.map_neg_eq_inv]
  simp

/-- Rotate a finite triple sum. -/
theorem sum_rotate3
    {α β γ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid R]
    (F : α → β → γ → R) :
    (∑ a : α, ∑ b : β, ∑ c : γ, F a b c) =
      ∑ b : β, ∑ c : γ, ∑ a : α, F a b c := by
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [sum_comm]

/-- Exact sesquilinear Parseval identity for the unnormalised ZMod DFT. -/
theorem dft_sesq_parseval
    {L : ℕ} [NeZero L] (f g : ZMod L → ℂ) :
    (∑ k : ZMod L,
        (starRingEnd ℂ) (ZMod.dft f k) * ZMod.dft g k) =
      (L : ℂ) *
        ∑ x : ZMod L, (starRingEnd ℂ) (f x) * g x := by
  classical
  have hterm (x y k : ZMod L) :
      (ZMod.stdAddChar (x * k) * (starRingEnd ℂ) (f x)) *
          (ZMod.stdAddChar (-(y * k)) * g y) =
        ((starRingEnd ℂ) (f x) * g y) *
          ZMod.stdAddChar ((x - y) * k) := by
    calc
      (ZMod.stdAddChar (x * k) * (starRingEnd ℂ) (f x)) *
          (ZMod.stdAddChar (-(y * k)) * g y)
          = ((starRingEnd ℂ) (f x) * g y) *
              (ZMod.stdAddChar (x * k) * ZMod.stdAddChar (-(y * k))) := by
                ring
      _ = ((starRingEnd ℂ) (f x) * g y) *
              ZMod.stdAddChar (x * k + -(y * k)) := by
                rw [← map_add_eq_mul]
      _ = ((starRingEnd ℂ) (f x) * g y) *
              ZMod.stdAddChar ((x - y) * k) := by
                congr 2
                ring

  simp only [ZMod.dft_apply, smul_eq_mul]
  simp_rw [map_sum, map_mul, star_stdAddChar_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [sum_rotate3]
  simp_rw [hterm]
  simp_rw [← Finset.mul_sum]
  simp_rw [stdAddChar_orthogonality]
  simp [sub_eq_zero, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Norm-squared Parseval for the unnormalised DFT. -/
theorem dft_energy_parseval
    {L : ℕ} [NeZero L] (Phi : ZMod L → ℂ) :
    (∑ k : ZMod L, ‖ZMod.dft Phi k‖ ^ 2) =
      (L : ℝ) * ∑ x : ZMod L, ‖Phi x‖ ^ 2 := by
  have hs := dft_sesq_parseval Phi Phi
  have hs' :
      (∑ k : ZMod L, ((‖ZMod.dft Phi k‖ ^ 2 : ℝ) : ℂ)) =
        (L : ℂ) *
          ∑ x : ZMod L, ((‖Phi x‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.sq_norm, Complex.normSq_eq_conj_mul_self] using hs
  have hcast :
      (((∑ k : ZMod L, ‖ZMod.dft Phi k‖ ^ 2) : ℝ) : ℂ) =
        ((((L : ℝ) * ∑ x : ZMod L, ‖Phi x‖ ^ 2) : ℝ) : ℂ) := by
    simpa using hs'
  exact_mod_cast hcast

/-- Exact inverse-DFT energy identity.  This is the rigorous meaning of
    "restoring the completion factor": there is exactly one factor L. -/
theorem invDFT_energy_parseval
    {L : ℕ} [NeZero L] (Psi : ZMod L → ℂ) :
    (∑ k : ZMod L, ‖Psi k‖ ^ 2) =
      (L : ℝ) * ∑ x : ZMod L, ‖ZMod.dft.symm Psi x‖ ^ 2 := by
  simpa using (dft_energy_parseval (Phi := ZMod.dft.symm Psi))

/-- A second completion factor cannot be hidden in this convention. -/
theorem one_completion_factor_only
    {L : ℕ} [NeZero L] (Psi : ZMod L → ℂ) :
    (∑ k : ZMod L, ‖Psi k‖ ^ 2) =
      (L : ℝ) * ∑ x : ZMod L, ‖ZMod.dft.symm Psi x‖ ^ 2 :=
  invDFT_energy_parseval Psi

/-! ## B. Singular-frequency energy is accounted for exactly -/

def nonsingularPart
    {L : ℕ} [NeZero L]
    (Sing : ZMod L → Prop) [DecidablePred Sing]
    (Psi : ZMod L → ℂ) : ZMod L → ℂ :=
  fun k => if Sing k then 0 else Psi k

def singularPart
    {L : ℕ} [NeZero L]
    (Sing : ZMod L → Prop) [DecidablePred Sing]
    (Psi : ZMod L → ℂ) : ZMod L → ℂ :=
  fun k => if Sing k then Psi k else 0

/-- Frequency masking is an exact partition of the original transform. -/
theorem frequency_partition_pointwise
    {L : ℕ} [NeZero L]
    (Sing : ZMod L → Prop) [DecidablePred Sing]
    (Psi : ZMod L → ℂ) (k : ZMod L) :
    Psi k = nonsingularPart Sing Psi k + singularPart Sing Psi k := by
  by_cases hk : Sing k <;> simp [nonsingularPart, singularPart, hk]

/-- Because the two masks are disjoint, their energies add exactly. -/
theorem frequency_energy_partition
    {L : ℕ} [NeZero L]
    (Sing : ZMod L → Prop) [DecidablePred Sing]
    (Psi : ZMod L → ℂ) :
    (∑ k : ZMod L, ‖Psi k‖ ^ 2) =
      (∑ k : ZMod L, ‖nonsingularPart Sing Psi k‖ ^ 2) +
      (∑ k : ZMod L, ‖singularPart Sing Psi k‖ ^ 2) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hs : Sing k <;> simp [nonsingularPart, singularPart, hs]

/-! ## C. True diagonal / singular off-diagonal / nonsingular off-diagonal -/

/-- Pure finite ledger: every pair contribution belongs to exactly one of
    the three Turn-397 classes.  This prevents a diagonal or singular term
    from disappearing during the schematic passage to (5999). -/
theorem three_way_pair_partition
    {ι : Type*} [Fintype ι]
    (Diag Sing : ι → Prop) [DecidablePred Diag] [DecidablePred Sing]
    (F : ι → ℝ) :
    (∑ i, F i) =
      (∑ i, if Diag i then F i else 0) +
      (∑ i, if ¬ Diag i ∧ Sing i then F i else 0) +
      (∑ i, if ¬ Diag i ∧ ¬ Sing i then F i else 0) := by
  classical
  calc
    (∑ i, F i) =
        ∑ i, ((if Diag i then F i else 0) +
          (if ¬ Diag i ∧ Sing i then F i else 0) +
          (if ¬ Diag i ∧ ¬ Sing i then F i else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hd : Diag i <;> by_cases hs : Sing i <;> simp [hd, hs]
    _ = (∑ i, if Diag i then F i else 0) +
        (∑ i, if ¬ Diag i ∧ Sing i then F i else 0) +
        (∑ i, if ¬ Diag i ∧ ¬ Sing i then F i else 0) := by
          simp only [Finset.sum_add_distrib]

/-! ## D. Exact finite majorant behind Eq. (6002) -/

/-- Finite Cauchy-Schwarz in the real form needed for the coefficient l1/l2
    conversion. -/
theorem finite_cauchy_squared
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤
      (∑ i, a i ^ 2) * ∑ i, b i ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) a b

/-- (sum |alpha_m|)^2 <= #M * sum |alpha_m|^2. -/
theorem l1_sq_le_card_mul_l2
    {ι : Type*} [Fintype ι] (alpha : ι → ℂ) :
    (∑ i, ‖alpha i‖) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, ‖alpha i‖ ^ 2 := by
  have h := finite_cauchy_squared
    (fun _i : ι => (1 : ℝ)) (fun i : ι => ‖alpha i‖)
  simpa using h

/-- For one modulus q, pointwise |K_{m1,m2}(q)| <= B gives exactly the
    double-coefficient triangle majorant used in (6002). -/
theorem one_modulus_kernel_majorant
    {ι : Type*} [Fintype ι]
    (alpha : ι → ℂ) (K : ι → ι → ℂ)
    (B : ℝ)
    (hK : ∀ m1 m2, ‖K m1 m2‖ ≤ B) :
    ‖∑ m1, ∑ m2,
        (starRingEnd ℂ) (alpha m1) * alpha m2 * K m1 m2‖
      ≤ B * (∑ m, ‖alpha m‖) ^ 2 := by
  classical
  calc
    ‖∑ m1, ∑ m2,
        (starRingEnd ℂ) (alpha m1) * alpha m2 * K m1 m2‖
        ≤ ∑ m1, ‖∑ m2,
            (starRingEnd ℂ) (alpha m1) * alpha m2 * K m1 m2‖ :=
              norm_sum_le _ _
    _ ≤ ∑ m1, ∑ m2,
            ‖(starRingEnd ℂ) (alpha m1) * alpha m2 * K m1 m2‖ := by
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
    _ ≤ ∑ m1, ∑ m2,
          ‖alpha m1‖ * ‖alpha m2‖ * B := by
            apply Finset.sum_le_sum
            intro m1 hm1
            apply Finset.sum_le_sum
            intro m2 hm2
            exact mul_le_mul_of_nonneg_left (hK m1 m2)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = B * (∑ m, ‖alpha m‖) ^ 2 := by
          have hinner (m1 : ι) :
              (∑ m2 : ι, ‖alpha m1‖ * ‖alpha m2‖ * B) =
                ‖alpha m1‖ * (∑ m2 : ι, ‖alpha m2‖) * B := by
            rw [← Finset.sum_mul]
            rw [← Finset.mul_sum]
          simp_rw [hinner]
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          ring

/-- The full q-weighted finite sum.  No cancellation between distinct q
    fibres is used: this is the literal triangle-inequality mechanism in
    Turn 397. -/
theorem weighted_kernel_majorant
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (lambda : κ → ℂ) (alpha : ι → ℂ)
    (K : κ → ι → ι → ℂ)
    (B : ℝ)
    (hK : ∀ q m1 m2, ‖K q m1 m2‖ ≤ B) :
    ‖∑ q, lambda q *
        (∑ m1, ∑ m2,
          (starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2)‖
      ≤ (∑ q, ‖lambda q‖) * B * (∑ m, ‖alpha m‖) ^ 2 := by
  classical
  calc
    ‖∑ q, lambda q *
        (∑ m1, ∑ m2,
          (starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2)‖
        ≤ ∑ q, ‖lambda q *
          (∑ m1, ∑ m2,
            (starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2)‖ :=
              norm_sum_le _ _
    _ = ∑ q, ‖lambda q‖ *
          ‖∑ m1, ∑ m2,
            (starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2‖ := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [norm_mul]
    _ ≤ ∑ q, ‖lambda q‖ *
          (B * (∑ m, ‖alpha m‖) ^ 2) := by
              apply Finset.sum_le_sum
              intro q hq
              exact mul_le_mul_of_nonneg_left
                (one_modulus_kernel_majorant alpha (K q) B (hK q))
                (norm_nonneg _)
    _ = (∑ q, ‖lambda q‖) * B * (∑ m, ‖alpha m‖) ^ 2 := by
          rw [← Finset.sum_mul]
          ring

/-- Combining the previous two lemmas gives the exact finite analogue of
    the two inequalities in (6002): q-weight mass x kernel bound x M x l2. -/
theorem eq6002_finite_form
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (lambda : κ → ℂ) (alpha : ι → ℂ)
    (K : κ → ι → ι → ℂ)
    (B LambdaMass L2 : ℝ)
    (hB : 0 ≤ B) (hLambda : 0 ≤ LambdaMass)
    (hK : ∀ q m1 m2, ‖K q m1 m2‖ ≤ B)
    (hLam : (∑ q, ‖lambda q‖) ≤ LambdaMass)
    (hAlpha : (∑ m, ‖alpha m‖ ^ 2) ≤ L2) :
    ‖∑ q, lambda q *
        (∑ m1, ∑ m2,
          (starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2)‖
      ≤ LambdaMass * B * ((Fintype.card ι : ℝ) * L2) := by
  have hcard0 : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hl1 := l1_sq_le_card_mul_l2 alpha
  have hl1' : (∑ m, ‖alpha m‖) ^ 2 ≤ (Fintype.card ι : ℝ) * L2 := by
    calc
      (∑ m, ‖alpha m‖) ^ 2
          ≤ (Fintype.card ι : ℝ) * ∑ m, ‖alpha m‖ ^ 2 := hl1
      _ ≤ (Fintype.card ι : ℝ) * L2 :=
          mul_le_mul_of_nonneg_left hAlpha hcard0
  have hmain := weighted_kernel_majorant lambda alpha K B hK
  calc
    ‖∑ q, lambda q *
        (∑ m1, ∑ m2,
          (starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2)‖
        ≤ (∑ q, ‖lambda q‖) * B * (∑ m, ‖alpha m‖) ^ 2 := hmain
    _ ≤ LambdaMass * B * (∑ m, ‖alpha m‖) ^ 2 := by
          have hLamB : (∑ q, ‖lambda q‖) * B ≤ LambdaMass * B :=
            mul_le_mul_of_nonneg_right hLam hB
          have hsq : 0 ≤ (∑ m, ‖alpha m‖) ^ 2 := sq_nonneg _
          exact mul_le_mul_of_nonneg_right hLamB hsq
    _ ≤ LambdaMass * B * ((Fintype.card ι : ℝ) * L2) := by
          have hLB : 0 ≤ LambdaMass * B := mul_nonneg hLambda hB
          exact mul_le_mul_of_nonneg_left hl1' hLB

/-! ## E. q versus dyadic scale Q -/

/-- In a dyadic interval q <= 2Q, restoring the exact modulus factor q costs
    at most a fixed factor 2 relative to the scale Q.  It cannot create an
    additional power of Q. -/
theorem dyadic_completion_factor_bound
    {q Q T : ℝ} (hT : 0 ≤ T) (hq : q ≤ 2 * Q) :
    q * T ≤ 2 * Q * T := by
  exact mul_le_mul_of_nonneg_right hq hT

/-- Guardrail: replacing an exact factor q by Q is not an identity unless
    q=Q.  Turn 397's Q is a dyadic scale, so this replacement belongs in a
    Vinogradov/O(1) bound, not in an exact equality. -/
theorem q_to_Q_is_not_exact_without_equality
    {q Q T : ℝ} (hT : 0 < T) (hEq : q * T = Q * T) : q = Q := by
  nlinarith

/-!
AUDIT INTERPRETATION.

A clean run certifies the finite mechanics of the Turn-397 variance passage:
Parseval supplies exactly one completion-modulus factor; singular frequencies
and the true diagonal can be kept in explicit ledgers; the nonsingular sum
satisfies the exact triangle/Cauchy majorant asserted in (6002); and replacing
an actual q by the dyadic scale Q costs only a fixed factor when q ~ Q.

It does NOT prove the remaining external/source contracts:
  * the actual normalized Kloosterman kernel satisfies the stated Weil bound;
  * the prime weight has the required total mass;
  * the Type-II coefficient system has the stated l2 divisor bound;
  * the actual completed variance is identified with this DFT/pair-kernel
    model, with the diagonal and singular sets exactly as claimed.
Those are now isolated rather than hidden.
-/

#check invDFT_energy_parseval
#check frequency_energy_partition
#check three_way_pair_partition
#check one_modulus_kernel_majorant
#check weighted_kernel_majorant
#check l1_sq_le_card_mul_l2
#check eq6002_finite_form
#check dyadic_completion_factor_bound
#check q_to_Q_is_not_exact_without_equality

#print axioms TwinPrimeT397VarianceSource.invDFT_energy_parseval
#print axioms TwinPrimeT397VarianceSource.frequency_energy_partition
#print axioms TwinPrimeT397VarianceSource.three_way_pair_partition
#print axioms TwinPrimeT397VarianceSource.one_modulus_kernel_majorant
#print axioms TwinPrimeT397VarianceSource.weighted_kernel_majorant
#print axioms TwinPrimeT397VarianceSource.eq6002_finite_form
#print axioms TwinPrimeT397VarianceSource.dyadic_completion_factor_bound

end
end TwinPrimeT397VarianceSource
