import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Run 10j: historical item 13 source/interface boundary

Purpose
-------
This file freezes the Turn-397 / Turn-418 dependency graph after the audit
correction that the final Q^(-1/132) endpoint power is NOT required for the
TPC crossing.

The only manuscript-specific analytic input represented here is the interior
Type-II coefficient bound on the band t <= 0.498.  The endpoint strip is paid
for by the already-audited fixed-q Selberg factor 8.

Accordingly:
* no Q^(-1/132) theorem is assumed;
* no endpoint power-saving proposition is a field of the item-13 interface;
* an arbitrary proposition standing for such an endpoint theorem is shown to
  be logically irrelevant to the finite crossing;
* the external/human-referee analytic trust boundary is kept explicit rather
  than silently replaced by a stronger theorem.

This file is self-contained for Lean Web and contains no axiom, sorry, or admit.
-/

namespace TwinPrimeRun10j

noncomputable section

/-- Conservative lower coefficient used in the Turn-418 audit. -/
def cSafe : ℝ := 377 / 500

/-- Turn-397 upper-band cutoff: 0.498 = 249/500. -/
def t0 : ℝ := 249 / 500

/-- Lean-safe interior relative coefficient from Turn 418. -/
def kIntSafe : ℝ := 10067 / 10000

/-- Full logarithmic mass of the balanced-semiprime band. -/
def fullMass : ℝ := Real.log 2

/-- Mass of the terminal strip 249/500 < t <= 1/2. -/
def tailMass : ℝ := Real.log ((251 : ℝ) / 249)

/-- Interior mass. -/
def interiorMass : ℝ := fullMass - tailMass

/-- Integrated upper coefficient: interior at Kint, terminal strip at 8. -/
def upperMass (Kint : ℝ) : ℝ :=
  Kint * interiorMass + 8 * tailMass

/-- The historical item-13 interface needed by the repaired Turn-397 crossing.
    It contains only the INTERIOR coefficient statement.  In particular, it
    has no field representing a Q^(-1/132) endpoint theorem. -/
structure Item13InteriorInput where
  Kint : ℝ
  interior_bound : Kint ≤ kIntSafe

/-- The cutoff really lies below the endpoint. -/
theorem t0_lt_half : t0 < (1 : ℝ) / 2 := by
  norm_num [t0]

/-- The audited Selberg endpoint conversion: 4/(1-t) <= 8 on t <= 1/2. -/
theorem tail_selberg_to_eight {t : ℝ} (ht : t ≤ (1 : ℝ) / 2) :
    4 / (1 - t) ≤ 8 := by
  have hp : 0 < 1 - t := by linarith
  rw [div_le_iff₀ hp]
  nlinarith

/-- Rigorous elementary tail-log bound. -/
theorem tail_log_upper : tailMass < (2 : ℝ) / 249 := by
  dsimp [tailMass]
  have h := Real.log_lt_sub_one_of_pos
    (x := (251 : ℝ) / 249) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The terminal strip is smaller than the full log-2 mass. -/
theorem tail_lt_full : tailMass < fullMass := by
  dsimp [tailMass, fullMass]
  exact Real.log_lt_log (by norm_num : 0 < (251 : ℝ) / 249)
    (by norm_num : (251 : ℝ) / 249 < 2)

/-- Positivity of the interior mass. -/
theorem interiorMass_pos : 0 < interiorMass := by
  dsimp [interiorMass]
  linarith [tail_lt_full]

/-- Algebraic form of the interior-plus-tail mass ledger. -/
theorem upperMass_expand (Kint : ℝ) :
    upperMass Kint = Kint * fullMass + (8 - Kint) * tailMass := by
  dsimp [upperMass, interiorMass]
  ring

/-- The conservative Turn-418 coefficient 1.0067 already crosses below 0.754.
    This is the numerical heart of the statement that no endpoint power theorem
    is needed once the final strip is paid at factor 8. -/
theorem safe_upper_at_kIntSafe : upperMass kIntSafe < cSafe := by
  have h2 : Real.log (2 : ℝ) < 0.6931471808 := Real.log_two_lt_d9
  have ht : tailMass < (2 : ℝ) / 249 := tail_log_upper
  rw [upperMass_expand]
  dsimp [kIntSafe, fullMass, cSafe]
  nlinarith

/-- Monotonicity in the interior coefficient on the positive interior mass. -/
theorem interior_bound_implies_crossing {Kint : ℝ}
    (hK : Kint ≤ kIntSafe) : upperMass Kint < cSafe := by
  have hI : 0 < interiorMass := interiorMass_pos
  have hmono : upperMass Kint ≤ upperMass kIntSafe := by
    dsimp [upperMass]
    nlinarith
  exact lt_of_le_of_lt hmono safe_upper_at_kIntSafe

/-- The exact source/interface boundary for historical item 13: once the
    interior input is supplied, the integrated Turn-397 upper ledger closes. -/
theorem item13_interior_input_implies_crossing (I : Item13InteriorInput) :
    upperMass I.Kint < cSafe := by
  exact interior_bound_implies_crossing I.interior_bound

/-- The original manuscript interior coefficient 1 is more than sufficient. -/
theorem manuscript_interior_one_closes_upper_ledger :
    upperMass 1 < cSafe := by
  apply interior_bound_implies_crossing
  norm_num [kIntSafe]

/-- Machine-level irrelevance statement.

    `EndpointPowerClaim` may stand for the proposed uniform Q^(-1/132)
    endpoint theorem, or for ANY other endpoint-power assertion.  The crossing
    follows both if that proposition is true and if it is false.  Therefore the
    finite Turn-397 crossing does not logically depend on that endpoint claim. -/
theorem item13_crossing_independent_of_endpoint_power
    (I : Item13InteriorInput) (EndpointPowerClaim : Prop) :
    (EndpointPowerClaim → upperMass I.Kint < cSafe) ∧
    (¬ EndpointPowerClaim → upperMass I.Kint < cSafe) := by
  constructor
  · intro _
    exact item13_interior_input_implies_crossing I
  · intro _
    exact item13_interior_input_implies_crossing I

/-- Final one-sided crossing logic on a common positive scale. -/
theorem item13_plus_audited_tail_implies_positive_count
    (I : Item13InteriorInput)
    {A3 E T H : ℝ}
    (hH : 0 < H)
    (hdecomp : A3 = T + E)
    (hlower : cSafe * H < A3)
    (hupper : E ≤ upperMass I.Kint * H) :
    0 < T := by
  have hcoeff : upperMass I.Kint < cSafe :=
    item13_interior_input_implies_crossing I
  have hmass : upperMass I.Kint * H < cSafe * H :=
    mul_lt_mul_of_pos_right hcoeff hH
  have hE : E < cSafe * H := lt_of_le_of_lt hupper hmass
  linarith

/-- Same final crossing, explicitly quantified over an arbitrary endpoint-power
    proposition, showing that the conclusion is independent of its truth value. -/
theorem positive_count_independent_of_endpoint_power
    (I : Item13InteriorInput)
    (EndpointPowerClaim : Prop)
    {A3 E T H : ℝ}
    (hH : 0 < H)
    (hdecomp : A3 = T + E)
    (hlower : cSafe * H < A3)
    (hupper : E ≤ upperMass I.Kint * H) :
    (EndpointPowerClaim → 0 < T) ∧ (¬ EndpointPowerClaim → 0 < T) := by
  have hT : 0 < T :=
    item13_plus_audited_tail_implies_positive_count I hH hdecomp hlower hupper
  exact ⟨fun _ => hT, fun _ => hT⟩

#check Item13InteriorInput
#check tail_selberg_to_eight
#check safe_upper_at_kIntSafe
#check item13_interior_input_implies_crossing
#check manuscript_interior_one_closes_upper_ledger
#check item13_crossing_independent_of_endpoint_power
#check item13_plus_audited_tail_implies_positive_count
#check positive_count_independent_of_endpoint_power

#print axioms tail_selberg_to_eight
#print axioms safe_upper_at_kIntSafe
#print axioms item13_interior_input_implies_crossing
#print axioms manuscript_interior_one_closes_upper_ledger
#print axioms item13_crossing_independent_of_endpoint_power
#print axioms item13_plus_audited_tail_implies_positive_count
#print axioms positive_count_independent_of_endpoint_power

end

end TwinPrimeRun10j
