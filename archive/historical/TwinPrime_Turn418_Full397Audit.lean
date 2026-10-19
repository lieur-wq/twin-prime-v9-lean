import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Twin Prime Project -- Turn 418
Lean audit of the finite/logical ledger behind Turn 397.

IMPORTANT:
* This file contains no `axiom`, `sorry`, or `admit`.
* It does NOT assert the missing analytic Heath--Brown interior estimate.
  That estimate appears only as an explicit hypothesis of theorems below.
* It also does not formalize the full sieve theorem producing the lower
  coefficient.  Instead it uses the deliberately weaker safe coefficient
  cSafe = 0.754 in the final algebraic crossing lemma.
* No Q^(-1/132) hypothesis occurs anywhere: Turn 397 bought the endpoint
  with a crude constant on a short strip.
-/

namespace TwinPrimeTurn418

noncomputable section

/-- A deliberately conservative lower coefficient.  This avoids relying on
    the later Turn-395 P4 tightening 0.754169... . -/
def cSafe : ℝ := 377 / 500

/-- Turn 397 cuts the upper semiprime band at t = 0.498 = 249/500. -/
def t0 : ℝ := 249 / 500

/-- A Lean-friendly safe interior coefficient.  The exact numerical allowance
    from the Turn-397 mass ledger is about 1.00708 when cSafe = 0.754; 1.0067
    leaves a comfortable rational margin. -/
def kIntSafe : ℝ := 10067 / 10000

/-- The corresponding square-root/variance allowance. -/
def deltaSafe : ℝ := 67 / 10000

def varianceSafe : ℝ := deltaSafe ^ 2

/-- Full balanced-semiprime logarithmic mass. -/
def fullMass : ℝ := Real.log 2

/-- Mass of the final strip 249/500 < t <= 1/2. -/
def tailMass : ℝ := Real.log ((251 : ℝ) / 249)

/-- Mass of the interior band. -/
def interiorMass : ℝ := fullMass - tailMass

/-- Integrated upper coefficient when the interior relative coefficient is Kint
    and the endpoint strip is paid at relative constant 8. -/
def upperMass (Kint : ℝ) : ℝ :=
  Kint * interiorMass + 8 * tailMass

/-- Basic cutoff check. -/
theorem t0_lt_half : t0 < (1 : ℝ) / 2 := by
  norm_num [t0]

/-- Algebra behind the Turn-398 surviving endpoint estimate:
    if the Selberg stage supplies 4/(1-t), then t <= 1/2 makes it at most 8. -/
theorem tail_selberg_to_eight {t : ℝ} (ht : t ≤ (1 : ℝ) / 2) :
    4 / (1 - t) ≤ 8 := by
  have hp : 0 < 1 - t := by linarith
  rw [div_le_iff₀ hp]
  nlinarith

/-- Elementary rigorous upper bound for the tail logarithm.
    log x < x-1 for x>0, x != 1. -/
theorem tail_log_upper : tailMass < (2 : ℝ) / 249 := by
  dsimp [tailMass]
  have h := Real.log_lt_sub_one_of_pos
    (x := (251 : ℝ) / 249) (by norm_num) (by norm_num)
  convert h using 1 <;> norm_num

/-- The tail is genuinely smaller than the full log-2 mass. -/
theorem tail_lt_full : tailMass < fullMass := by
  dsimp [tailMass, fullMass]
  exact Real.log_lt_log (by norm_num : 0 < (251 : ℝ) / 249)
    (by norm_num : (251 : ℝ) / 249 < 2)

/-- Hence the interior mass is positive. -/
theorem interiorMass_pos : 0 < interiorMass := by
  dsimp [interiorMass]
  linarith [tail_lt_full]

/-- Pure algebraic form of the Turn-397 mass decomposition. -/
theorem upperMass_expand (Kint : ℝ) :
    upperMass Kint = Kint * fullMass + (8 - Kint) * tailMass := by
  dsimp [upperMass, interiorMass]
  ring

/-- Mathlib already contains a certified upper bound for log 2.  Together with
    tail_log_upper, the deliberately conservative Kint = 1.0067 stays below
    cSafe = 0.754. -/
theorem safe_upper_at_kIntSafe : upperMass kIntSafe < cSafe := by
  have h2 : Real.log (2 : ℝ) < 0.6931471808 := Real.log_two_lt_d9
  have ht : tailMass < (2 : ℝ) / 249 := tail_log_upper
  rw [upperMass_expand]
  dsimp [kIntSafe, fullMass, cSafe]
  nlinarith

/-- Any smaller interior coefficient also crosses. -/
theorem special_interior_implies_crossing {Kint : ℝ}
    (hK : Kint ≤ kIntSafe) : upperMass Kint < cSafe := by
  have hI : 0 < interiorMass := interiorMass_pos
  have hm : 0 ≤ (kIntSafe - Kint) * interiorMass :=
    mul_nonneg (sub_nonneg.mpr hK) (le_of_lt hI)
  have hmono : upperMass Kint ≤ upperMass kIntSafe := by
    dsimp [upperMass]
    nlinarith
  exact lt_of_le_of_lt hmono safe_upper_at_kIntSafe

/-- In particular, the original Turn-397 intended interior coefficient 1 would
    have been more than sufficient.  Lean therefore agrees with the diagnosis:
    the finite constant ledger of Turn 397 was not the bad step. -/
theorem original_turn397_ledger_if_interior_one :
    upperMass 1 < cSafe := by
  apply special_interior_implies_crossing
  norm_num [kIntSafe]

/-- Turn 398's generic Cauchy estimate is larger than the desired scale by an
    exact factor M.  This is only an algebraic scale identity; it does not say
    the same loss is forced for the actual HB coefficient. -/
theorem generic_cauchy_missing_factor_M (C Q M : ℝ) :
    C * Q^2 * M^3 = M * (C * Q^2 * M^2) := by
  ring

/-- Final one-sided crossing logic: if A3 = T + E, the lower rough count beats
    c*H and the semiprime upper contribution is at most c*H, then T>0. -/
theorem one_sided_crossing
    {A3 E T H c : ℝ}
    (hdecomp : A3 = T + E)
    (hlower : c * H < A3)
    (hupper : E ≤ c * H) :
    0 < T := by
  linarith

/-- The safe coefficient 1.0067 is exactly 1 + 0.0067. -/
theorem kIntSafe_eq : kIntSafe = 1 + deltaSafe := by
  norm_num [kIntSafe, deltaSafe]

/-- The squared variance allowance is 4.489e-5. -/
theorem varianceSafe_eq : varianceSafe = (4489 : ℝ) / 100000000 := by
  norm_num [varianceSafe, deltaSafe]

/-- Turn 397 used Kint <= 1 + sqrt(V).  Thus a coefficient-specific normalized
    variance below deltaSafe^2 forces Kint < 1.0067. -/
theorem variance_route_to_safe_interior
    {V Kint : ℝ}
    (hV0 : 0 ≤ V)
    (hK : Kint ≤ 1 + Real.sqrt V)
    (hV : V < varianceSafe) :
    Kint < kIntSafe := by
  have hd : 0 ≤ deltaSafe := by norm_num [deltaSafe]
  have hs0 : 0 ≤ Real.sqrt V := Real.sqrt_nonneg V
  have hs2 : (Real.sqrt V)^2 = V := by
    simpa using Real.sq_sqrt hV0
  have hs : Real.sqrt V < deltaSafe := by
    by_contra hnot
    have hge : deltaSafe ≤ Real.sqrt V := le_of_not_gt hnot
    have hmul :
        0 ≤ (Real.sqrt V - deltaSafe) * (Real.sqrt V + deltaSafe) :=
      mul_nonneg (sub_nonneg.mpr hge) (add_nonneg hs0 hd)
    dsimp [varianceSafe] at hV
    nlinarith
  rw [kIntSafe_eq]
  linarith

/-- Therefore the Turn-397 variance route is repaired as soon as the *actual
    special-arithmetic/HB* interior variance meets the explicit small bound.
    This theorem does not assume anything about arbitrary factorable vectors. -/
theorem special_variance_implies_crossing
    {V Kint : ℝ}
    (hV0 : 0 ≤ V)
    (hK : Kint ≤ 1 + Real.sqrt V)
    (hV : V < varianceSafe) :
    upperMass Kint < cSafe := by
  have hklt : Kint < kIntSafe :=
    variance_route_to_safe_interior hV0 hK hV
  exact special_interior_implies_crossing (le_of_lt hklt)

end

end TwinPrimeTurn418
