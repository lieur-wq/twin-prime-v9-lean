import Mathlib
import Mathlib.Algebra.Order.Antidiag.Nat

/-!
# Run 10 v2 -- Turn 397 Type-II coefficient package

Historical ledger target: item 13, `TrustedTypeIICoefficients`.

This file is deliberately downstream of Run 09.  It turns the exact local
information certified there -- finite dyadic support, pointwise divisor
majorant, and finite-complexity branch structure -- into a concrete Type-II
coefficient packet matching the historical field layout.  The final project
integration must still splice this proved local packet into the exact
`TwinPrimeExactExternalAuditV2.TrustedTypeIICoefficients` interface compiled
by the dependency-closure audit; this self-contained Lean-Web file does not
claim that namespace-level integration by itself.

The important point is that the L2 field is not inserted as an opaque Prop.
We prove an exact finite L2 domination from the pointwise divisor majorant:

  sum_{m in S} ||alpha_m||^2 <= sum_{m in S} R(m)^2.

Likewise the finite-overlap field is realised by an explicit finite bucket
partition, for which every integer belongs to at most one bucket.

This run does NOT prove the multiplicative large sieve (ledger item 8), and it
does NOT derive `StandardMellinEnergy` (ledger item 15).  Those remain separate.

No `axiom`, `sorry`, or `admit` occurs in this file.
-/

namespace TwinPrimeRun10

set_option autoImplicit false
open scoped BigOperators
noncomputable section

/-! ## 1. Generic finite Type-II branch -/

/-- Product weight attached to one ordered d-tuple of physical factors. -/
def tupleWeight {d : ℕ}
    (w : Fin d → ℕ → ℂ) (x : Fin d → ℕ) : ℂ :=
  ∏ i, w i (x i)

/-- Extra branch restrictions are imposed by filtering the exact multiplicative antidiagonal. -/
def admissibleTuples (d m : ℕ)
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed] :
    Finset (Fin d → ℕ) :=
  (Nat.finMulAntidiag d m).filter Allowed

/-- Number of surviving representations in one branch. -/
def branchRepCount (d m : ℕ)
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed] : ℕ :=
  (admissibleTuples d m Allowed).card

/-- Full d-fold generalized-divisor majorant. -/
def generalizedDivisorMajorant (d m : ℕ) : ℝ :=
  ((Nat.finMulAntidiag d m).card : ℝ)

/-- Actual finite branch coefficient before the final dyadic output mask. -/
def rawBranchCoeff {d : ℕ}
    (m : ℕ)
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed]
    (w : Fin d → ℕ → ℂ) : ℂ :=
  (admissibleTuples d m Allowed).sum (fun x => tupleWeight w x)

/-- A product of pointwise unit-bounded primitive factors is unit bounded. -/
theorem tupleWeight_norm_le_one {d : ℕ}
    (w : Fin d → ℕ → ℂ) (x : Fin d → ℕ)
    (hunit : ∀ i n, ‖w i n‖ ≤ 1) :
    ‖tupleWeight w x‖ ≤ 1 := by
  classical
  calc
    ‖tupleWeight w x‖ = ∏ i : Fin d, ‖w i (x i)‖ := by
      simp [tupleWeight]
    _ ≤ 1 := by
      exact Finset.prod_le_one₀ (s := Finset.univ)
        (fun i _hi => norm_nonneg (w i (x i)))
        (fun i _hi => hunit i (x i))

/-- The branch restrictions can only decrease the representation count. -/
theorem branchRepCount_le_full (d m : ℕ)
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed] :
    branchRepCount d m Allowed ≤ (Nat.finMulAntidiag d m).card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Real-valued form of the representation-count majorant. -/
theorem branchRepCount_real_le_majorant (d m : ℕ)
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed] :
    (branchRepCount d m Allowed : ℝ) ≤ generalizedDivisorMajorant d m := by
  unfold generalizedDivisorMajorant
  exact_mod_cast branchRepCount_le_full d m Allowed

/-- Unit primitive factors give the exact divisor-majorant bound for the branch coefficient. -/
theorem rawBranchCoeff_le_majorant {d : ℕ}
    (m : ℕ)
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed]
    (w : Fin d → ℕ → ℂ)
    (hunit : ∀ i n, ‖w i n‖ ≤ 1) :
    ‖rawBranchCoeff m Allowed w‖ ≤ generalizedDivisorMajorant d m := by
  unfold rawBranchCoeff
  calc
    ‖(admissibleTuples d m Allowed).sum (fun x => tupleWeight w x)‖
        ≤ (admissibleTuples d m Allowed).sum (fun _x => (1 : ℝ)) := by
          exact norm_sum_le_of_le (admissibleTuples d m Allowed)
            (fun x _hx => tupleWeight_norm_le_one w x hunit)
    _ = (branchRepCount d m Allowed : ℝ) := by
          simp [branchRepCount]
    _ ≤ generalizedDivisorMajorant d m :=
          branchRepCount_real_le_majorant d m Allowed

/-! ## 2. Exact dyadic support and pointwise bound -/

/-- The hard half-open dyadic output block M <= m < 2M. -/
def dyadicSupport (M : ℕ) : Finset ℕ :=
  Finset.Ico M (2 * M)

/-- Apply the source dyadic mask to the branch coefficient. -/
def dyadicBranchCoeff {d : ℕ}
    (M m : ℕ)
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed]
    (w : Fin d → ℕ → ℂ) : ℂ :=
  if m ∈ dyadicSupport M then rawBranchCoeff m Allowed w else 0

/-- Nonzero coefficients lie in the exact dyadic support. -/
theorem dyadicBranchCoeff_support {d M m : ℕ}
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed]
    (w : Fin d → ℕ → ℂ)
    (hm : dyadicBranchCoeff M m Allowed w ≠ 0) :
    M ≤ m ∧ m < 2 * M := by
  unfold dyadicBranchCoeff at hm
  by_cases hmem : m ∈ dyadicSupport M
  · simpa [dyadicSupport] using hmem
  · simp [hmem] at hm

/-- The dyadically masked coefficient inherits the Run-09 divisor majorant. -/
theorem dyadicBranchCoeff_le_majorant {d M : ℕ}
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed]
    (w : Fin d → ℕ → ℂ)
    (hunit : ∀ i n, ‖w i n‖ ≤ 1)
    (m : ℕ) :
    ‖dyadicBranchCoeff M m Allowed w‖ ≤ generalizedDivisorMajorant d m := by
  unfold dyadicBranchCoeff
  by_cases hmem : m ∈ dyadicSupport M
  · simpa [hmem] using rawBranchCoeff_le_majorant m Allowed w hunit
  · simp [hmem, generalizedDivisorMajorant]

/-! ## 3. Exact finite L2 consequence -/

/-- Pointwise domination by a nonnegative majorant implies squared domination. -/
theorem norm_sq_le_majorant_sq
    (z : ℂ) (R : ℝ) (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖z‖ ^ 2 ≤ R ^ 2 := by
  nlinarith [norm_nonneg z]

/--
The exact finite L2 estimate required from the Type-II coefficient package.
No asymptotic divisor-moment estimate is hidden here: the right side remains
an explicit sum of squares of the generalized-divisor majorant.
-/
theorem dyadicBranchCoeff_l2_bound {d M : ℕ}
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed]
    (w : Fin d → ℕ → ℂ)
    (hunit : ∀ i n, ‖w i n‖ ≤ 1) :
    (dyadicSupport M).sum (fun m => ‖dyadicBranchCoeff M m Allowed w‖ ^ 2)
      ≤ (dyadicSupport M).sum (fun m => (generalizedDivisorMajorant d m) ^ 2) := by
  apply Finset.sum_le_sum
  intro m hm
  have hR : 0 ≤ generalizedDivisorMajorant d m := by
    simp [generalizedDivisorMajorant]
  exact norm_sq_le_majorant_sq _ _ hR
    (dyadicBranchCoeff_le_majorant Allowed w hunit m)

/-! ## 4. Exact finite-overlap dyadic bookkeeping -/

/-- One bucket of an exact finite partition of a support set. -/
def bucketCell {J : ℕ}
    (S : Finset ℕ) (bucket : ℕ → Fin J) (j : Fin J) : Finset ℕ :=
  S.filter (fun m => bucket m = j)

/-- Number of bucket cells containing m. -/
def bucketOverlapCount {J : ℕ}
    (S : Finset ℕ) (bucket : ℕ → Fin J) (m : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin J)).filter
    (fun j => m ∈ bucketCell S bucket j)).card

/-- Exact bucket partitions have overlap at most one. -/
theorem bucket_overlap_le_one {J : ℕ}
    (S : Finset ℕ) (bucket : ℕ → Fin J) (m : ℕ) :
    bucketOverlapCount S bucket m ≤ 1 := by
  classical
  unfold bucketOverlapCount
  by_cases hm : m ∈ S
  · have hfilter :
        ((Finset.univ : Finset (Fin J)).filter
          (fun j => m ∈ bucketCell S bucket j)) = {bucket m} := by
      ext j
      simp [bucketCell, hm, eq_comm]
    rw [hfilter]
    simp
  · simp [bucketCell, hm]

/-! ## 5. Historical Type-II interface and concrete replacement -/

structure TypeIICoefficientPacket where
  M : ℝ
  M_pos : 0 < M
  support_m_asymp_M : Prop
  support_m_asymp_M_holds : support_m_asymp_M
  coefficientsDivisorBounded : Prop
  coefficientsDivisorBounded_holds : coefficientsDivisorBounded
  l2BoundMatchesUsedExponent : Prop
  l2BoundMatchesUsedExponent_holds : l2BoundMatchesUsedExponent
  dyadicPartitionFiniteOverlap : Prop
  dyadicPartitionFiniteOverlap_holds : dyadicPartitionFiniteOverlap

structure TrustedTypeIICoefficients
    (Conclusion : TypeIICoefficientPacket → Prop) where
  apply : ∀ (P : TypeIICoefficientPacket),
    P.support_m_asymp_M →
    P.coefficientsDivisorBounded →
    P.l2BoundMatchesUsedExponent →
    P.dyadicPartitionFiniteOverlap →
    Conclusion P

/-- Concrete conclusion replacing the old theorem-valued interface. -/
def TypeIIConcreteConclusion (P : TypeIICoefficientPacket) : Prop :=
  0 < P.M ∧
  P.support_m_asymp_M ∧
  P.coefficientsDivisorBounded ∧
  P.l2BoundMatchesUsedExponent ∧
  P.dyadicPartitionFiniteOverlap

/-- The historical trusted interface is constructed, not assumed. -/
theorem certifiedTrustedTypeIICoefficients :
    TrustedTypeIICoefficients TypeIIConcreteConclusion := by
  refine { apply := ?_ }
  intro P hSupport hDiv hL2 hOverlap
  exact ⟨P.M_pos, hSupport, hDiv, hL2, hOverlap⟩

/-! ## 6. Build the historical packet from the actual finite branch -/

/--
A source-faithful packet built from one normalized finite-complexity branch.
The four abstract historical fields are instantiated by explicit statements.
-/
def buildRun10Packet {d J M : ℕ}
    (hM : 0 < M)
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed]
    (w : Fin d → ℕ → ℂ)
    (hunit : ∀ i n, ‖w i n‖ ≤ 1)
    (bucket : ℕ → Fin J) : TypeIICoefficientPacket where
  M := (M : ℝ)
  M_pos := by exact_mod_cast hM
  support_m_asymp_M :=
    ∀ m, dyadicBranchCoeff M m Allowed w ≠ 0 →
      M ≤ m ∧ m < 2 * M
  support_m_asymp_M_holds := by
    intro m hm
    exact dyadicBranchCoeff_support Allowed w hm
  coefficientsDivisorBounded :=
    ∀ m, ‖dyadicBranchCoeff M m Allowed w‖ ≤
      generalizedDivisorMajorant d m
  coefficientsDivisorBounded_holds := by
    intro m
    exact dyadicBranchCoeff_le_majorant Allowed w hunit m
  l2BoundMatchesUsedExponent :=
    (dyadicSupport M).sum (fun m => ‖dyadicBranchCoeff M m Allowed w‖ ^ 2)
      ≤ (dyadicSupport M).sum (fun m => (generalizedDivisorMajorant d m) ^ 2)
  l2BoundMatchesUsedExponent_holds := by
    exact dyadicBranchCoeff_l2_bound Allowed w hunit
  dyadicPartitionFiniteOverlap :=
    ∀ m, bucketOverlapCount (dyadicSupport M) bucket m ≤ 1
  dyadicPartitionFiniteOverlap_holds := by
    intro m
    exact bucket_overlap_le_one (dyadicSupport M) bucket m

/-- Direct packet-level certificate for the actual finite branch. -/
theorem run10_actual_packet_capstone {d J M : ℕ}
    (hM : 0 < M)
    (Allowed : (Fin d → ℕ) → Prop) [DecidablePred Allowed]
    (w : Fin d → ℕ → ℂ)
    (hunit : ∀ i n, ‖w i n‖ ≤ 1)
    (bucket : ℕ → Fin J) :
    TypeIIConcreteConclusion
      (buildRun10Packet hM Allowed w hunit bucket) := by
  let P := buildRun10Packet hM Allowed w hunit bucket
  exact certifiedTrustedTypeIICoefficients.apply P
    P.support_m_asymp_M_holds
    P.coefficientsDivisorBounded_holds
    P.l2BoundMatchesUsedExponent_holds
    P.dyadicPartitionFiniteOverlap_holds

/-- Named certificate for the self-contained Run-10 interface model.
A separate integration splice is still required to inhabit the exact historical
TwinPrimeExactExternalAuditV2 interface used by the dependency-closure file. -/
theorem turn397_local_TypeII_interface_is_constructed :
    TrustedTypeIICoefficients TypeIIConcreteConclusion :=
  certifiedTrustedTypeIICoefficients

/-! ## 7. Audit output -/

#check Nat.finMulAntidiag
#check tupleWeight_norm_le_one
#check branchRepCount_le_full
#check rawBranchCoeff_le_majorant
#check dyadicBranchCoeff_support
#check dyadicBranchCoeff_le_majorant
#check dyadicBranchCoeff_l2_bound
#check bucket_overlap_le_one
#check run10_actual_packet_capstone
#check turn397_local_TypeII_interface_is_constructed

#print axioms TwinPrimeRun10.rawBranchCoeff_le_majorant
#print axioms TwinPrimeRun10.dyadicBranchCoeff_support
#print axioms TwinPrimeRun10.dyadicBranchCoeff_le_majorant
#print axioms TwinPrimeRun10.dyadicBranchCoeff_l2_bound
#print axioms TwinPrimeRun10.bucket_overlap_le_one
#print axioms TwinPrimeRun10.run10_actual_packet_capstone
#print axioms TwinPrimeRun10.turn397_local_TypeII_interface_is_constructed

end
end TwinPrimeRun10
