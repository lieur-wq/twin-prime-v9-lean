import Mathlib

/-!
# Twin Prime project - Run 10m v2
## Exact ZMod CRT factorisation of finite sums and local Gram channels

Purpose
-------
Run 10l certified the exact Hermitian opening of the q,m second moment and
made the admissible CRT-trace estimate an explicit gate.

Run 10m v1 exposed two formalisation defects:
1. `ZMod n` is finite only for nonzero modulus n, so the specialization must
   state nonzero moduli explicitly;
2. `ZMod.chineseRemainder hcop` is a ring equivalence, while the generic
   summation lemma expects its underlying plain equivalence.

This v2 repairs those points without changing the intended prime-modulus
mathematics.  It proves, using Mathlib's actual `ZMod.chineseRemainder`, that
any finite kernel which genuinely factorises into a q-part and an m-part under
CRT has an exactly factorised complete sum.  It also records the corresponding
Hermitian local-correlation factorisation.

What this file DOES NOT prove
-----------------------------
It does not assert that the actual completed Kloosterman/HB kernel already
has the required factorised form.  The additive character, unit restriction,
inverse variable, zero modes, and conductor-drop sectors still have to be
matched to local q- and m-kernels.  That is the next gate.

Thus a clean Run 10m v2 is an algebraic CRT PASS, not a proof of G3b.
-/

open scoped BigOperators

namespace TwinPrimeRun10m

section GenericCRT

variable {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]

/-- Summation is invariant under an equivalence from X to a product A x B. -/
theorem sum_over_crt_equiv
    (e : X ≃ A × B) (F : A → B → Complex) :
    (∑ x : X, F (e x).1 (e x).2) = ∑ a : A, ∑ b : B, F a b := by
  calc
    (∑ x : X, F (e x).1 (e x).2)
        = ∑ y : A × B, F y.1 y.2 := by
            simpa using (Equiv.sum_comp e (fun y : A × B => F y.1 y.2))
    _ = ∑ a : A, ∑ b : B, F a b := by
            simpa using (Fintype.sum_prod_type' F)

/-- If the CRT kernel is a product of two local kernels, its complete sum factors exactly. -/
theorem factorized_sum_over_crt_equiv
    (e : X ≃ A × B) (u : A → Complex) (v : B → Complex) :
    (∑ x : X, u (e x).1 * v (e x).2)
      = (∑ a : A, u a) * (∑ b : B, v b) := by
  calc
    (∑ x : X, u (e x).1 * v (e x).2)
        = ∑ a : A, ∑ b : B, u a * v b := by
            exact sum_over_crt_equiv e (fun a b => u a * v b)
    _ = ∑ a : A, u a * (∑ b : B, v b) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
    _ = (∑ a : A, u a) * (∑ b : B, v b) := by
            rw [Finset.sum_mul]

end GenericCRT

section ZModCRT

/--
Exact specialization to Mathlib's Chinese-remainder equivalence for coprime,
nonzero moduli.  The `NeZero` hypotheses are automatic in the intended
prime-modulus application and are necessary because `ZMod 0` is infinite.
-/
theorem zmod_crt_factorized_sum
    {q m : ℕ} [NeZero q] [NeZero m]
    (hcop : q.Coprime m)
    (u : ZMod q → Complex) (v : ZMod m → Complex) :
    (∑ x : ZMod (q * m),
        u ((ZMod.chineseRemainder hcop) x).1 *
        v ((ZMod.chineseRemainder hcop) x).2)
      = (∑ a : ZMod q, u a) * (∑ b : ZMod m, v b) := by
  exact factorized_sum_over_crt_equiv
    (ZMod.chineseRemainder hcop).toEquiv u v

/--
The Hermitian local-correlation channel also factorises exactly under CRT.
This is the shape needed after an opened second moment, once the actual global
kernel has been identified with the product of its local q- and m-kernels.
-/
theorem zmod_crt_hermitian_channel
    {q m : ℕ} [NeZero q] [NeZero m]
    (hcop : q.Coprime m)
    (uq1 uq2 : ZMod q → Complex)
    (um1 um2 : ZMod m → Complex) :
    (∑ x : ZMod (q * m),
        (uq1 ((ZMod.chineseRemainder hcop) x).1 *
          um1 ((ZMod.chineseRemainder hcop) x).2) *
        star (uq2 ((ZMod.chineseRemainder hcop) x).1 *
          um2 ((ZMod.chineseRemainder hcop) x).2))
      =
      (∑ a : ZMod q, uq1 a * star (uq2 a)) *
      (∑ b : ZMod m, um1 b * star (um2 b)) := by
  have hfac := zmod_crt_factorized_sum hcop
    (fun a : ZMod q => uq1 a * star (uq2 a))
    (fun b : ZMod m => um1 b * star (um2 b))
  calc
    (∑ x : ZMod (q * m),
        (uq1 ((ZMod.chineseRemainder hcop) x).1 *
          um1 ((ZMod.chineseRemainder hcop) x).2) *
        star (uq2 ((ZMod.chineseRemainder hcop) x).1 *
          um2 ((ZMod.chineseRemainder hcop) x).2))
      =
      ∑ x : ZMod (q * m),
        (uq1 ((ZMod.chineseRemainder hcop) x).1 *
          star (uq2 ((ZMod.chineseRemainder hcop) x).1)) *
        (um1 ((ZMod.chineseRemainder hcop) x).2 *
          star (um2 ((ZMod.chineseRemainder hcop) x).2)) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [star_mul']
            ring
    _ =
      (∑ a : ZMod q, uq1 a * star (uq2 a)) *
      (∑ b : ZMod m, um1 b * star (um2 b)) := hfac

end ZModCRT

#check sum_over_crt_equiv
#check factorized_sum_over_crt_equiv
#check zmod_crt_factorized_sum
#check zmod_crt_hermitian_channel

#print axioms sum_over_crt_equiv
#print axioms factorized_sum_over_crt_equiv
#print axioms zmod_crt_factorized_sum
#print axioms zmod_crt_hermitian_channel

end TwinPrimeRun10m
