import Mathlib

/-!
Turn 132: Auditing applicability of published range theorems in manuscript v9.
Targets: Sections 7 and 8, equations (expinterior), (cutoff), (Eint).

The manuscript's Type-II variables are exponent parameters:
  1/3 < theta <= 249/500, 0 <= mu <= (1-theta)/2.
The test checks the EXACT rational exponent saving and a valid Vaughan-split
choice below the 1/500 endpoint gap.

The script then gives a finite rational witness showing that the same bounds
DO NOT imply theta + mu <= 1/2. Therefore the ordinary Bombieri-Vinogradov
theorem cannot be invoked blindly for a PRODUCT modulus of size Q*M; one
must check the actual Type-I modulus, which the manuscript treats separately.

This is not an assertion that v9 uses Q*M as its BV modulus. It is a
condition-checking guard against one specific possible theorem misuse.

Pascadi's theorem additionally requires its specified factorability class;
Motohashi's induction principle additionally requires its analytic function
hypotheses. Those are not finite rational inequalities and are NOT certified
by this script. They must be matched with the actual source coefficients.

No custom axiom or unproved proof hole is used. This file has not been compiled.
-/

namespace TP132V9BVRange

set_option autoImplicit false
noncomputable section

/-- v9 Section 7's literal 0.498 cutoff is 1/500 below 1/2. -/
theorem v9_fixed_interior_gap :
    (1 : ℝ) / 2 - (249 : ℝ) / 500 = 1 / 500 := by
  norm_num

/-- An explicit, valid small Vaughan split on all of v9's interior band. -/
theorem v9_vaughan_split_below_gap
    {theta : ℝ} (htheta : theta ≤ (249 : ℝ) / 500) :
    (1 : ℝ) / 1000 < 1 / 2 - theta := by
  linarith

/-- Exponents in the stated Type-II range force mu < theta.
    On scales Y > 1 this is the exponent-level reason M < Q,
    which is required if one uses prime-q coprimality via m < q. -/
theorem v9_coefficient_exponent_below_prime_modulus_exponent
    {theta mu : ℝ}
    (htheta : (1 : ℝ) / 3 < theta)
    (hmu : mu ≤ (1 - theta) / 2) :
    mu < theta := by
  linarith

/-- The claimed Type-II first-moment exponent stays <= 0.998. -/
theorem v9_typeII_exponent_bound
    {theta mu : ℝ}
    (htheta : theta ≤ (249 : ℝ) / 500)
    (hmu : mu ≤ (1 - theta) / 2) :
    3 * theta / 2 + mu ≤ (499 : ℝ) / 500 := by
  linarith

/-- Therefore, under exactly the preceding exponent assumptions, the Type-II
    first moment enjoys a strict exponent saving over Y^1. -/
theorem v9_typeII_exponent_strictly_sublinear
    {theta mu : ℝ}
    (htheta : theta ≤ (249 : ℝ) / 500)
    (hmu : mu ≤ (1 - theta) / 2) :
    3 * theta / 2 + mu < 1 := by
  have h := v9_typeII_exponent_bound htheta hmu
  linarith

/-- Concrete admissible exponent endpoint theta = 249/500, mu = 251/1000.
    Their sum is 749/1000, i.e. ABOVE 1/2. -/
theorem v9_product_modulus_exponent_witness :
    ((1 : ℝ) / 3 < 249 / 500) ∧
    ((249 : ℝ) / 500 ≤ 249 / 500) ∧
    ((251 : ℝ) / 1000 ≤ (1 - 249 / 500) / 2) ∧
    ((249 : ℝ) / 500 + 251 / 1000 > 1 / 2) := by
  norm_num

/-- A blanket implication 'the v9 Type-II band forces theta+mu <= 1/2' is
    mathematically FALSE.  This only matters if the BV modulus were Q*M;
    the manuscript has to justify the ACTUAL Type-I modulus separately. -/
theorem cannot_apply_classical_BV_to_arbitrary_QM_from_band_alone :
    ¬ (∀ theta mu : ℝ,
      (1 : ℝ) / 3 < theta →
      theta ≤ (249 : ℝ) / 500 →
      0 ≤ mu →
      mu ≤ (1 - theta) / 2 →
      theta + mu ≤ (1 : ℝ) / 2) := by
  intro h
  have hbad := h (249 / 500 : ℝ) (251 / 1000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad

#check v9_fixed_interior_gap
#check v9_vaughan_split_below_gap
#check v9_coefficient_exponent_below_prime_modulus_exponent
#check v9_typeII_exponent_bound
#check v9_typeII_exponent_strictly_sublinear
#check v9_product_modulus_exponent_witness
#check cannot_apply_classical_BV_to_arbitrary_QM_from_band_alone

#print axioms v9_typeII_exponent_bound
#print axioms v9_typeII_exponent_strictly_sublinear
#print axioms cannot_apply_classical_BV_to_arbitrary_QM_from_band_alone

end
end TP132V9BVRange
