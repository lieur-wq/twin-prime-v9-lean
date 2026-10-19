import TPCV9.V9.FinalCertification
import TPCV9.PostV9.WeilCRTConditions
import TPCV9.PostV9.BVRangeConditions

/-!
# Statement and axiom audit for the exact v9 source

The v9 source file is imported unaltered. These checks refer to the
actual Mathlib predicate Nat.Prime and the actual source theorem.
They do not silently assert that a source packet has been constructed.
-/

set_option autoImplicit false

namespace TPCV9StatementAudit

theorem actual_tpc_statement_matches_Nat_Prime :
    TwinPrimeCurrentCertification.TwinPrimeConjecture =
      (∀ B : ℕ, ∃ p : ℕ, B < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) := by
  rfl

-- This displays the true theorem type, including the source input.
#check @TwinPrimeCurrentCertification.current_source_implies_tpc
#print TwinPrimeCurrentCertification.TwinPrimeConjecture
#print TwinPrimeCurrentCertification.FinalAnalyticSourceCurrent
#print TwinPrimeCurrentCertification.current_source_implies_tpc

-- Each printed axiom report must contain only standard Lean axioms.
#print axioms TPCV9StatementAudit.actual_tpc_statement_matches_Nat_Prime
#print axioms TwinPrimeCurrentCertification.published_weil_to_turn397_kernel_bound
#print axioms TwinPrimeCurrentCertification.current_source_implies_tpc
#print axioms TP132V9WeilCRT.exact_crt_factorization_at_v9_prime_modulus
#print axioms TP132V9BVRange.v9_typeII_exponent_strictly_sublinear

end TPCV9StatementAudit
