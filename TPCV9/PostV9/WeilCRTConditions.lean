import Mathlib

/-!
Turn 132: Auditing theorem applicability in the submitted v9 manuscript.
Target: Section 7, displayed equations (KCRT) and (Kbound).

This is an ADVERSARIAL APPLICATION TEST, not an attempt to prove TPC.
It checks conditions that must hold when invoking CRT and prime-modulus
Kloosterman-Weil estimates. The manuscript says it separates singular
frequencies: the test exhibits why that separation is indispensable.

Part A derives coprimality from prime q and the actual requirement 0 < m < q.
Part B applies Mathlib's actual ZMod Chinese remainder equivalence to an
exactly factorable completed kernel (not to a generic, unidentified kernel).
Part C proves that the zero-frequency sector is not covered by a blanket
2 sqrt(q) estimate; this is NOT a counterexample to the v9 proof, which
explicitly claims to exclude singular frequencies.

Passing this script does not establish that the source-defined, completed
Heath-Brown/Kloosterman kernel is the particular product used in Part B.
That identification is a separate analytic step in v9.

No custom axioms, unproved proof holes or new abstract input propositions are used.
This new file has not been compiled in the author's Lean Web environment.
-/

namespace TP132V9WeilCRT

set_option autoImplicit false
open scoped BigOperators
noncomputable section

/-- q prime, 0 < m < q are sufficient for CRT's coprimality condition. -/
theorem prime_q_coprime_coefficient_modulus
    {q m : ℕ} (hq : Nat.Prime q) (hmpos : 0 < m) (hmlt : m < q) :
    q.Coprime m := by
  apply (hq.coprime_iff_not_dvd).2
  intro hdiv
  have hle : q ≤ m := Nat.le_of_dvd hmpos hdiv
  omega

/-- Both coefficient indices m1,m2 meet the q-coprimality condition. -/
theorem paired_moduli_coprime
    {q m1 m2 : ℕ} (hq : Nat.Prime q)
    (hm1pos : 0 < m1) (hm2pos : 0 < m2)
    (hm1lt : m1 < q) (hm2lt : m2 < q) :
    q.Coprime m1 ∧ q.Coprime m2 := by
  exact ⟨prime_q_coprime_coefficient_modulus hq hm1pos hm1lt,
         prime_q_coprime_coefficient_modulus hq hm2pos hm2lt⟩

/-- This is the EXACT Mathlib CRT summation step, conditional on literal
    factorisation of the summand and on coprime nonzero moduli. -/
theorem exact_crt_factorization_at_v9_prime_modulus
    {q m : ℕ} [NeZero q] [NeZero m]
    (hq : Nat.Prime q) (hmpos : 0 < m) (hmlt : m < q)
    (u : ZMod q → ℂ) (v : ZMod m → ℂ) :
    (∑ x : ZMod (q * m),
       u ((ZMod.chineseRemainder
         (prime_q_coprime_coefficient_modulus hq hmpos hmlt)) x).1 *
       v ((ZMod.chineseRemainder
         (prime_q_coprime_coefficient_modulus hq hmpos hmlt)) x).2)
       = (∑ a : ZMod q, u a) * (∑ b : ZMod m, v b) := by
  let hcop : q.Coprime m :=
    prime_q_coprime_coefficient_modulus hq hmpos hmlt
  let e : ZMod (q * m) ≃ ZMod q × ZMod m :=
    (ZMod.chineseRemainder hcop).toEquiv
  change (∑ x : ZMod (q * m), u (e x).1 * v (e x).2) =
    (∑ a : ZMod q, u a) * (∑ b : ZMod m, v b)
  calc
    (∑ x : ZMod (q * m), u (e x).1 * v (e x).2)
        = ∑ ab : ZMod q × ZMod m, u ab.1 * v ab.2 := by
            simpa using (Equiv.sum_comp e
              (fun ab : ZMod q × ZMod m => u ab.1 * v ab.2))
    _ = ∑ a : ZMod q, ∑ b : ZMod m, u a * v b := by
          simpa using (Fintype.sum_prod_type'
            (fun a : ZMod q => fun b : ZMod m => u a * v b))
    _ = ∑ a : ZMod q, u a * (∑ b : ZMod m, v b) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mul_sum]
    _ = (∑ a : ZMod q, u a) * (∑ b : ZMod m, v b) := by
          rw [Finset.sum_mul]

/-- A concrete zero-frequency arithmetic obstruction: at prime modulus 11,
    the unnormalised zero/zero Kloosterman sum has 10 unit summands, whereas
    the generic nondegenerate Weil right side is 2 sqrt(11) < 10.
    This DOES NOT refute v9, which states that zero/singular modes are removed.
-/
theorem zero_zero_frequency_needs_exceptional_treatment :
    ¬ ((10 : ℝ) ≤ 2 * Real.sqrt (11 : ℝ)) := by
  intro h
  have hs : (Real.sqrt (11 : ℝ)) ^ 2 = (11 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt (11 : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- Coprime q and m do NOT, by themselves, exclude simultaneous zero
    frequency inputs; the additional singular-mode separation is substantive. -/
theorem singular_frequency_despite_coprime_moduli :
    Nat.Prime 11 ∧ (11 : ℕ).Coprime 2 ∧
    (11 : ℕ) ∣ 0 ∧ (11 : ℕ) ∣ 2 * 0 := by
  norm_num

#check ZMod.chineseRemainder
#check prime_q_coprime_coefficient_modulus
#check paired_moduli_coprime
#check exact_crt_factorization_at_v9_prime_modulus
#check zero_zero_frequency_needs_exceptional_treatment
#check singular_frequency_despite_coprime_moduli

#print axioms prime_q_coprime_coefficient_modulus
#print axioms exact_crt_factorization_at_v9_prime_modulus
#print axioms zero_zero_frequency_needs_exceptional_treatment

end
end TP132V9WeilCRT
