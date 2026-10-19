import Mathlib

/-!
# TP120: terminal source-to-actual-primes bridge, no opaque final packet

Here the final quantities are literal real functions of the dyadic parameter.
The result checks the numerical crossing and genuine twin-support implication.
All lower / upper / prime-power bounds remain written as explicit theorem
hypotheses in the actual parameter Y; they are not smuggled in as Mathlib
lemmas or as `Prop` + `_holds` record fields.

The source of those estimates must still be supplied by a correct application of
the relevant external number-theoretic theorems to the actual sums.
-/

namespace TP120Terminal

set_option autoImplicit false
noncomputable section

structure Source where
  H : ℕ -> ℝ
  A3 : ℕ -> ℝ
  E : ℕ -> ℝ
  W : ℕ -> ℝ
  Rpp : ℕ -> ℝ
  T : ℕ -> ℝ

/-- Actual twin-prime infinitude, not an abstract positivity predicate. -/
def TwinPrimeConjecture : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-- Exactly the numerical implication needed once the original prime-number
    source has established its lower and upper bounds. -/
theorem signed_crossing
    (D : Source) (Y : ℕ)
    (hH : 0 < D.H Y)
    (hA : ((7541 : ℝ) / 10000) * D.H Y ≤ D.A3 Y)
    (hE : D.E Y ≤ ((74938 : ℝ) / 100000) * D.H Y)
    (hPP : D.Rpp Y ≤ ((1 : ℝ) / 1000) * D.H Y)
    (hW : D.W Y = D.A3 Y - D.E Y)
    (hT : D.T Y = D.W Y - D.Rpp Y) :
    0 < D.T Y := by
  rw [hT, hW]
  nlinarith

/-- The hypotheses explicitly require the required asymptotic conclusions
    for the actual source, at unbounded parameters. Nothing is inferred from
    a manually declared empty ledger. -/
def SourceEventuallyCrosses (D : Source) : Prop :=
  ∀ N : ℕ, ∃ Y : ℕ,
    N ≤ Y ∧
    0 < D.H Y ∧
    ((7541 : ℝ) / 10000) * D.H Y ≤ D.A3 Y ∧
    D.E Y ≤ ((74938 : ℝ) / 100000) * D.H Y ∧
    D.Rpp Y ≤ ((1 : ℝ) / 1000) * D.H Y ∧
    D.W Y = D.A3 Y - D.E Y ∧
    D.T Y = D.W Y - D.Rpp Y

/-- A separate source-support obligation. Positive actual weighted twin count
    must imply a genuinely prime pair rather than a prime-power surrogate. -/
def HasGenuineTwinSupport (D : Source) : Prop :=
  ∀ Y : ℕ, 0 < D.T Y ->
    ∃ p : ℕ, Y ≤ 2 * p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-- All deductions *after* the six explicit arithmetic prerequisites are
    formal. Neither prerequisite is proved by this theorem. -/
theorem actual_source_closure
    (D : Source)
    (hCross : SourceEventuallyCrosses D)
    (hTwinSupport : HasGenuineTwinSupport D) :
    TwinPrimeConjecture := by
  intro N
  obtain ⟨Y, h2NY, hH, hA, hE, hPP, hW, hT⟩ := hCross (2 * N)
  have hPositive : 0 < D.T Y :=
    signed_crossing D Y hH hA hE hPP hW hT
  obtain ⟨p, hYp, hp, hp2⟩ := hTwinSupport Y hPositive
  have h2Np : 2 * N ≤ 2 * p := le_trans h2NY hYp
  have hN : N ≤ p := by omega
  exact ⟨p, hN, hp, hp2⟩

#check signed_crossing
#check SourceEventuallyCrosses
#check HasGenuineTwinSupport
#check actual_source_closure
#print axioms signed_crossing
#print axioms actual_source_closure

end
end TP120Terminal
