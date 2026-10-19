import Mathlib

/-!
# Twin Prime project - Run 10l
## Opened second moment and admissible CRT-trace gate

Purpose
-------
This file does two things only.

(1) It certifies the exact finite algebraic opening of the q,m second moment,
    with the complex conjugate kept visibly in the cross term.

(2) It certifies the elementary implication
        admissible CRT trace normal form + natural trace scale
        => natural C^2 variance scale.

Crucially, this file DOES NOT construct the admissible CRT trace normal form
from completion, Heath--Brown coefficients, Kloosterman sums, or any analytic
estimate.  That bridge is intentionally an explicit hypothesis of the final
lemma.  A clean Lean run therefore cannot be described as proving G3b.
-/

open scoped BigOperators

namespace TwinPrimeRun10l

section ExactGramOpening

variable {QIdx MIdx : Type*} [Fintype QIdx] [Fintype MIdx]

/-- The finite q,m coefficient family after all preceding exact reductions. -/
def closedSecondMoment (Z : QIdx -> MIdx -> Complex) : Complex :=
  ∑ q, (∑ m, Z q m) * (∑ m, star (Z q m))

/-- The same object with the m1,m2 Gram pair opened explicitly. -/
def openedGram (Z : QIdx -> MIdx -> Complex) : Complex :=
  ∑ q, ∑ m1, ∑ m2, Z q m1 * star (Z q m2)

/-- Exact second-moment opening.  No inequality and no analytic input occur here. -/
theorem closedSecondMoment_eq_openedGram
    (Z : QIdx -> MIdx -> Complex) :
    closedSecondMoment Z = openedGram Z := by
  unfold closedSecondMoment openedGram
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

end ExactGramOpening

section CRTTraceGate

/-- The natural C^2 scale, with C = Q M and an abstract Y^epsilon factor `Ye`. -/
def c2Scale (Q M Ye : ℝ) : ℝ := Q^2 * M^2 * Ye

/--
The semantic gate that must be supplied by the number theory.

`V = Q*T + Esep` is the normalized CRT-trace form.
`T <= Q*M^2*Ye` is the natural trace bound.
`Esep <= Ksep*C^2*Ye` records the already-separated exceptional sectors.

Nothing in this structure asserts that such data arise from the actual
Heath--Brown/Kloosterman block; constructing them is precisely the open bridge.
-/
structure AdmissibleCRTTraceData where
  Q : ℝ
  M : ℝ
  Ye : ℝ
  V : ℝ
  T : ℝ
  Esep : ℝ
  Ksep : ℝ
  hQ : 0 ≤ Q
  hDecomp : V = Q * T + Esep
  hTrace : T ≤ Q * M^2 * Ye
  hSep : Esep ≤ Ksep * c2Scale Q M Ye

/--
Once the admissible normal form and its natural trace bound are genuinely
available, the C^2 variance estimate is elementary bookkeeping.
-/
theorem admissibleCRTTraceData_implies_c2
    (d : AdmissibleCRTTraceData) :
    d.V ≤ (1 + d.Ksep) * c2Scale d.Q d.M d.Ye := by
  have hQT : d.Q * d.T ≤ d.Q * (d.Q * d.M^2 * d.Ye) :=
    mul_le_mul_of_nonneg_left d.hTrace d.hQ
  rw [d.hDecomp]
  calc
    d.Q * d.T + d.Esep
        ≤ d.Q * (d.Q * d.M^2 * d.Ye) + d.Ksep * c2Scale d.Q d.M d.Ye :=
          add_le_add hQT d.hSep
    _ = (1 + d.Ksep) * c2Scale d.Q d.M d.Ye := by
          unfold c2Scale
          ring

end CRTTraceGate

#check closedSecondMoment_eq_openedGram
#check admissibleCRTTraceData_implies_c2

#print axioms closedSecondMoment_eq_openedGram
#print axioms admissibleCRTTraceData_implies_c2

end TwinPrimeRun10l
