import Mathlib

namespace TwinPrimeT397AnalyticInputs

set_option autoImplicit false
open scoped BigOperators
open Finset
noncomputable section

/-!
Turn 397: ANALYTIC-INPUT bridge for Eqs. (5999)--(6004).

This file is intentionally source-faithful about what Lean can and cannot
currently discharge from Mathlib alone.

What is proved here, with no `axiom` declarations and no `sorry`:

  * the product of two normalized local Kloosterman factors has no hidden
    power of the modulus (only the product of the two local constants);
  * the prime-weighted finite kernel sum in (5999) obeys the exact
    triangle/Cauchy majorant used in (6002);
  * a dyadic prime-weight mass, a divisor-bounded Type-II L2 estimate, and
    a normalized Weil bound combine with the expected powers Q and M;
  * the usual epsilon-renaming step is made explicit: two half-epsilon
    losses are absorbed by Ehalf^2 <= Efull;
  * one completion factor and explicit diagonal/singular ledgers give the
    natural C^2-scale variance bound with no hidden extra factor of Q.

The genuinely external analytic statements are NOT smuggled in as axioms.
They remain visible as hypotheses of the capstone theorem:

  hPrimeMass : sum_q |lambda_q| <= C_lambda Q
  hWeil      : |K_q(m1,m2)| <= C_K Ehalf
  hCard      : #M <= C_card M
  hTypeIIL2  : sum_m |alpha_m|^2 <= C_alpha M Ehalf
  hSource    : the actual completed variance is bounded by exactly one
               completion factor times the nonsingular kernel sum, plus the
               separately retained diagonal and singular contributions
  hDiag, hSing : those retained pieces are at natural scale.

A clean run therefore checks that THESE exact source contracts are sufficient
and that their normalization is internally consistent. It does not by itself
formalize Weil's theorem, the prime number theorem/Chebyshev bound, or the
Heath--Brown/Vaughan coefficient construction.
-/

/-! ## 1. Finite kernel appearing in Eq. (5999) -/

def kernelSum
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (lambda : κ → ℂ) (alpha : ι → ℂ)
    (K : κ → ι → ι → ℂ) : ℂ :=
  ∑ q, lambda q *
    (∑ m1, ∑ m2,
      (starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2)

/-! ## 2. CRT product of normalized local factors -/

def crtProductKernel
    {κ ι : Type*}
    (K1 K2 : κ → ι → ι → ℂ) : κ → ι → ι → ℂ :=
  fun q m1 m2 => K1 q m1 m2 * K2 q m1 m2

/-- If the two normalized CRT factors satisfy local Weil-type bounds C1 and
    C2, their product costs C1*C2 and NO power of q. -/
theorem crtProductKernel_norm_bound
    {κ ι : Type*}
    (K1 K2 : κ → ι → ι → ℂ)
    (C1 C2 : ℝ)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : ∀ q m1 m2, ‖K1 q m1 m2‖ ≤ C1)
    (h2 : ∀ q m1 m2, ‖K2 q m1 m2‖ ≤ C2) :
    ∀ q m1 m2, ‖crtProductKernel K1 K2 q m1 m2‖ ≤ C1 * C2 := by
  intro q m1 m2
  simp only [crtProductKernel, norm_mul]
  exact mul_le_mul (h1 q m1 m2) (h2 q m1 m2)
    (norm_nonneg _) hC1

/-- The common Turn-397 specialization: two local normalized Weil constants
    at most 2 give a product constant at most 4. -/
theorem two_local_constants_give_four
    {κ ι : Type*}
    (K1 K2 : κ → ι → ι → ℂ)
    (h1 : ∀ q m1 m2, ‖K1 q m1 m2‖ ≤ 2)
    (h2 : ∀ q m1 m2, ‖K2 q m1 m2‖ ≤ 2) :
    ∀ q m1 m2, ‖crtProductKernel K1 K2 q m1 m2‖ ≤ 4 := by
  intro q m1 m2
  have h := crtProductKernel_norm_bound K1 K2 2 2 (by norm_num) (by norm_num) h1 h2 q m1 m2
  norm_num at h ⊢
  exact h

/-! ## 3. Exact finite inequalities behind Eq. (6002) -/

/-- (sum |alpha_m|)^2 <= #M * sum |alpha_m|^2. -/
theorem l1_sq_le_card_mul_l2
    {ι : Type*} [Fintype ι] (alpha : ι → ℂ) :
    (∑ i, ‖alpha i‖) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, ‖alpha i‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (fun _i : ι => (1 : ℝ)) (fun i : ι => ‖alpha i‖)
  simpa using h

/-- Literal triangle majorant for the q-weighted double coefficient sum. -/
theorem weighted_kernel_majorant
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (lambda : κ → ℂ) (alpha : ι → ℂ)
    (K : κ → ι → ι → ℂ)
    (B : ℝ)
    (hK : ∀ q m1 m2, ‖K q m1 m2‖ ≤ B) :
    ‖kernelSum lambda alpha K‖ ≤
      (∑ q, ‖lambda q‖) * B * (∑ m, ‖alpha m‖) ^ 2 := by
  classical
  unfold kernelSum
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
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              calc
                ‖∑ m1, ∑ m2,
                    (starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2‖
                    ≤ ∑ m1, ∑ m2,
                      ‖(starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2‖ := by
                        calc
                          _ ≤ ∑ m1,
                              ‖∑ m2,
                                (starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2‖ :=
                                  norm_sum_le _ _
                          _ ≤ ∑ m1, ∑ m2,
                              ‖(starRingEnd ℂ) (alpha m1) * alpha m2 * K q m1 m2‖ := by
                                apply Finset.sum_le_sum
                                intro m1 hm1
                                exact norm_sum_le _ _
                _ = ∑ m1, ∑ m2,
                      ‖alpha m1‖ * ‖alpha m2‖ * ‖K q m1 m2‖ := by
                        apply Finset.sum_congr rfl
                        intro m1 hm1
                        apply Finset.sum_congr rfl
                        intro m2 hm2
                        simp [mul_assoc]
                _ ≤ ∑ m1, ∑ m2,
                      ‖alpha m1‖ * ‖alpha m2‖ * B := by
                        apply Finset.sum_le_sum
                        intro m1 hm1
                        apply Finset.sum_le_sum
                        intro m2 hm2
                        exact mul_le_mul_of_nonneg_left (hK q m1 m2)
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
    _ = (∑ q, ‖lambda q‖) * B * (∑ m, ‖alpha m‖) ^ 2 := by
          rw [← Finset.sum_mul]
          ring

/-! ## 4. Feed in the four analytic scale inputs -/

/-- This is the exact Turn-397 source-input combination behind (6002)--(6003).

Ehalf is the conventional Y^(epsilon/2)-type slack.  Writing the proof this
way makes the epsilon-renaming step explicit rather than silently replacing
Y^(2 epsilon) by Y^epsilon. -/
theorem source_inputs_bound_T
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (lambda : κ → ℂ) (alpha : ι → ℂ)
    (K : κ → ι → ι → ℂ)
    (Q M Ehalf Efull : ℝ)
    (C_lambda C_K C_card C_alpha : ℝ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hEh : 0 ≤ Ehalf)
    (hCl : 0 ≤ C_lambda) (hCK : 0 ≤ C_K)
    (hCc : 0 ≤ C_card) (hCa : 0 ≤ C_alpha)
    (hPrimeMass : (∑ q, ‖lambda q‖) ≤ C_lambda * Q)
    (hWeil : ∀ q m1 m2, ‖K q m1 m2‖ ≤ C_K * Ehalf)
    (hCard : (Fintype.card ι : ℝ) ≤ C_card * M)
    (hTypeIIL2 : (∑ m, ‖alpha m‖ ^ 2) ≤ C_alpha * M * Ehalf)
    (hEpsAbsorb : Ehalf ^ 2 ≤ Efull) :
    ‖kernelSum lambda alpha K‖ ≤
      (C_lambda * C_K * C_card * C_alpha) *
        (Q * M ^ 2 * Efull) := by
  have hB0 : 0 ≤ C_K * Ehalf := mul_nonneg hCK hEh
  have hcard0 : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hL20 : 0 ≤ ∑ m, ‖alpha m‖ ^ 2 := by positivity
  have hL1 := l1_sq_le_card_mul_l2 alpha
  have hL1source :
      (∑ m, ‖alpha m‖) ^ 2 ≤
        (C_card * M) * (C_alpha * M * Ehalf) := by
    calc
      (∑ m, ‖alpha m‖) ^ 2
          ≤ (Fintype.card ι : ℝ) * ∑ m, ‖alpha m‖ ^ 2 := hL1
      _ ≤ (C_card * M) * ∑ m, ‖alpha m‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hCard hL20
      _ ≤ (C_card * M) * (C_alpha * M * Ehalf) := by
            have hCM : 0 ≤ C_card * M := mul_nonneg hCc hM
            exact mul_le_mul_of_nonneg_left hTypeIIL2 hCM
  have hMain := weighted_kernel_majorant lambda alpha K (C_K * Ehalf) hWeil
  have hMassB :
      (∑ q, ‖lambda q‖) * (C_K * Ehalf) ≤
        (C_lambda * Q) * (C_K * Ehalf) := by
    exact mul_le_mul_of_nonneg_right hPrimeMass hB0
  have hstep :
      ‖kernelSum lambda alpha K‖ ≤
        (C_lambda * Q) * (C_K * Ehalf) *
          ((C_card * M) * (C_alpha * M * Ehalf)) := by
    calc
      ‖kernelSum lambda alpha K‖
          ≤ (∑ q, ‖lambda q‖) * (C_K * Ehalf) *
              (∑ m, ‖alpha m‖) ^ 2 := hMain
      _ ≤ (C_lambda * Q) * (C_K * Ehalf) *
              (∑ m, ‖alpha m‖) ^ 2 := by
            exact mul_le_mul_of_nonneg_right hMassB (sq_nonneg _)
      _ ≤ (C_lambda * Q) * (C_K * Ehalf) *
              ((C_card * M) * (C_alpha * M * Ehalf)) := by
            have hfront : 0 ≤ (C_lambda * Q) * (C_K * Ehalf) :=
              mul_nonneg (mul_nonneg hCl hQ) hB0
            exact mul_le_mul_of_nonneg_left hL1source hfront
  calc
    ‖kernelSum lambda alpha K‖
        ≤ (C_lambda * Q) * (C_K * Ehalf) *
            ((C_card * M) * (C_alpha * M * Ehalf)) := hstep
    _ = (C_lambda * C_K * C_card * C_alpha) *
          (Q * M ^ 2 * (Ehalf ^ 2)) := by ring
    _ ≤ (C_lambda * C_K * C_card * C_alpha) *
          (Q * M ^ 2 * Efull) := by
        have hconst :
            0 ≤ (C_lambda * C_K * C_card * C_alpha) * (Q * M ^ 2) := by
          positivity
        have hmul := mul_le_mul_of_nonneg_left hEpsAbsorb hconst
        calc
          (C_lambda * C_K * C_card * C_alpha) *
              (Q * M ^ 2 * (Ehalf ^ 2))
              = ((C_lambda * C_K * C_card * C_alpha) * (Q * M ^ 2)) *
                  (Ehalf ^ 2) := by ring
          _ ≤ ((C_lambda * C_K * C_card * C_alpha) * (Q * M ^ 2)) *
                  Efull := hmul
          _ = (C_lambda * C_K * C_card * C_alpha) *
              (Q * M ^ 2 * Efull) := by ring

/-! ## 5. Source-identification / variance ledger -/

/-- Once the actual completed variance is identified with ONE completion
    factor times the nonsingular kernel sum plus explicit diagonal and
    singular ledgers, the Turn-397 natural-scale bound follows with an
    explicit constant.  This is the exact contract that must be matched to
    the source derivation; nothing is discarded silently. -/
theorem actual_variance_from_source_contracts
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (lambda : κ → ℂ) (alpha : ι → ℂ)
    (K : κ → ι → ι → ℂ)
    (Q M Ehalf Efull : ℝ)
    (C_lambda C_K C_card C_alpha C_comp C_diag C_sing : ℝ)
    (completion V diag sing : ℝ)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hEh : 0 ≤ Ehalf)
    (hEf : 0 ≤ Efull)
    (hCl : 0 ≤ C_lambda) (hCK : 0 ≤ C_K)
    (hCc : 0 ≤ C_card) (hCa : 0 ≤ C_alpha)
    (hCcomp : 0 ≤ C_comp) (hCdiag : 0 ≤ C_diag) (hCsing : 0 ≤ C_sing)
    (hCompletion0 : 0 ≤ completion)
    (hPrimeMass : (∑ q, ‖lambda q‖) ≤ C_lambda * Q)
    (hWeil : ∀ q m1 m2, ‖K q m1 m2‖ ≤ C_K * Ehalf)
    (hCard : (Fintype.card ι : ℝ) ≤ C_card * M)
    (hTypeIIL2 : (∑ m, ‖alpha m‖ ^ 2) ≤ C_alpha * M * Ehalf)
    (hEpsAbsorb : Ehalf ^ 2 ≤ Efull)
    (hCompletion : completion ≤ C_comp * Q)
    (hDiag : diag ≤ C_diag * ((Q * M) ^ 2 * Efull))
    (hSing : sing ≤ C_sing * ((Q * M) ^ 2 * Efull))
    (hSource : V ≤ completion * ‖kernelSum lambda alpha K‖ + diag + sing) :
    V ≤
      (C_comp * (C_lambda * C_K * C_card * C_alpha) + C_diag + C_sing) *
        ((Q * M) ^ 2 * Efull) := by
  let CT : ℝ := C_lambda * C_K * C_card * C_alpha
  have hT :
      ‖kernelSum lambda alpha K‖ ≤ CT * (Q * M ^ 2 * Efull) := by
    dsimp [CT]
    exact source_inputs_bound_T lambda alpha K Q M Ehalf Efull
      C_lambda C_K C_card C_alpha hQ hM hEh hCl hCK hCc hCa
      hPrimeMass hWeil hCard hTypeIIL2 hEpsAbsorb
  have hT0 : 0 ≤ ‖kernelSum lambda alpha K‖ := norm_nonneg _
  have hScale0 : 0 ≤ (Q * M) ^ 2 * Efull := by positivity
  have hCompT :
      completion * ‖kernelSum lambda alpha K‖ ≤
        (C_comp * CT) * ((Q * M) ^ 2 * Efull) := by
    calc
      completion * ‖kernelSum lambda alpha K‖
          ≤ (C_comp * Q) * ‖kernelSum lambda alpha K‖ := by
            exact mul_le_mul_of_nonneg_right hCompletion hT0
      _ ≤ (C_comp * Q) * (CT * (Q * M ^ 2 * Efull)) := by
            have hCQ : 0 ≤ C_comp * Q := mul_nonneg hCcomp hQ
            exact mul_le_mul_of_nonneg_left hT hCQ
      _ = (C_comp * CT) * ((Q * M) ^ 2 * Efull) := by ring
  calc
    V ≤ completion * ‖kernelSum lambda alpha K‖ + diag + sing := hSource
    _ ≤ (C_comp * CT) * ((Q * M) ^ 2 * Efull) +
          C_diag * ((Q * M) ^ 2 * Efull) +
          C_sing * ((Q * M) ^ 2 * Efull) := by
        linarith
    _ = (C_comp * CT + C_diag + C_sing) *
          ((Q * M) ^ 2 * Efull) := by ring
    _ = (C_comp * (C_lambda * C_K * C_card * C_alpha) + C_diag + C_sing) *
          ((Q * M) ^ 2 * Efull) := by simp [CT]

/-! ## 6. Guardrails -/

/-- If an extra full power of Q appeared in the completion factor, the result
    would no longer be a fixed-constant natural-scale estimate for unbounded Q.
    This elementary identity keeps that danger visible. -/
theorem extra_Q_changes_power
    (Q M E : ℝ) :
    Q ^ 2 * (Q * M ^ 2 * E) = Q * ((Q * M) ^ 2 * E) := by
  ring

/-!
AUDIT INTERPRETATION

A clean run proves that Turn 397's four analytic inputs, with their exact
Q/M/epsilon scalings, really imply the natural C^2-scale variance estimate,
and that one completion contributes one Q-power rather than two.

The file is intentionally NOT a fake unconditional formalization of classical
analytic number theory.  The capstone theorem still displays the source
contracts hPrimeMass, hWeil, hTypeIIL2, hCompletion, hDiag, hSing, and hSource.
Those are the statements to discharge from the actual Turn-397 analytic
reduction (or from cited standard theorems) before claiming a fully
kernel-checked proof.
-/

#check crtProductKernel_norm_bound
#check two_local_constants_give_four
#check l1_sq_le_card_mul_l2
#check weighted_kernel_majorant
#check source_inputs_bound_T
#check actual_variance_from_source_contracts
#check extra_Q_changes_power

#print axioms TwinPrimeT397AnalyticInputs.crtProductKernel_norm_bound
#print axioms TwinPrimeT397AnalyticInputs.two_local_constants_give_four
#print axioms TwinPrimeT397AnalyticInputs.l1_sq_le_card_mul_l2
#print axioms TwinPrimeT397AnalyticInputs.weighted_kernel_majorant
#print axioms TwinPrimeT397AnalyticInputs.source_inputs_bound_T
#print axioms TwinPrimeT397AnalyticInputs.actual_variance_from_source_contracts
#print axioms TwinPrimeT397AnalyticInputs.extra_Q_changes_power

end
end TwinPrimeT397AnalyticInputs
