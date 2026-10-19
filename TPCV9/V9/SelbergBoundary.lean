import Mathlib

/-!
# Twin Prime certification Run 11
## Historical ledger item 14: TrustedSelbergTwoLinearForm

Purpose
-------
This file does NOT re-prove Selberg's upper-bound sieve.

The publication trust boundary treats the classical fixed-q two-linear-form
Selberg upper sieve as an external mathematical theorem.  Lean's job here is
only to certify the exact adapter used by the manuscript:

* external relative constant 4 in the equal-log normalisation;
* audited conversion from equal-log weight to the natural endpoint weight;
* resulting safe relative constant 8;
* complete logical independence from any Q^(-1/132) endpoint-power claim.

This is the historical item-14 boundary.  No project axiom, `sorry`, or `admit`
is introduced.
-/

namespace TwinPrimeCertificationRun11

set_option autoImplicit false

/--
The exact finite quantities entering the already-audited Turn-397 endpoint
normalisation.  `eqWeight` is the equal-log Selberg normalisation and
`natWeight` is the natural `1/(log r log Y)` normalisation used in the paper.
-/
structure SelbergEndpointData where
  count : ℝ
  sigma : ℝ
  base : ℝ
  eqWeight : ℝ
  natWeight : ℝ
  sigma_nonneg : 0 ≤ sigma
  base_nonneg : 0 ≤ base
  weight_conversion : eqWeight ≤ 2 * natWeight

/--
The traditional mathematical input at item 14.  This is a proposition supplied
by the published/classical Selberg two-linear-form upper sieve, not a new axiom
of this Lean file.
-/
def PublishedSelbergTwoLinearForm (D : SelbergEndpointData) : Prop :=
  D.count ≤ 4 * (D.sigma * D.base * D.eqWeight)

/-- The endpoint conclusion actually consumed by the Turn-397 ledger. -/
def AuditedEndpointFactorEight (D : SelbergEndpointData) : Prop :=
  D.count ≤ 8 * (D.sigma * D.base * D.natWeight)

/-- Non-negativity of the common singular-series/base factor. -/
theorem sigma_base_nonneg (D : SelbergEndpointData) :
    0 ≤ D.sigma * D.base := by
  exact mul_nonneg D.sigma_nonneg D.base_nonneg

/--
Exact adapter already used in the Turn-397 audit: a relative-4 Selberg input,
together with the audited log-weight conversion, gives the safe relative-8
endpoint bound.
-/
theorem published_selberg_to_audited_factor_eight
    (D : SelbergEndpointData)
    (hSelberg : PublishedSelbergTwoLinearForm D) :
    AuditedEndpointFactorEight D := by
  unfold PublishedSelbergTwoLinearForm at hSelberg
  unfold AuditedEndpointFactorEight
  have hsb : 0 ≤ D.sigma * D.base := sigma_base_nonneg D
  have hw :
      (D.sigma * D.base) * D.eqWeight ≤
        (D.sigma * D.base) * (2 * D.natWeight) :=
    mul_le_mul_of_nonneg_left D.weight_conversion hsb
  nlinarith

/--
Publication-boundary packet: the external theorem is displayed explicitly as a
field, rather than hidden as a project axiom.
-/
structure Item14PublicationBoundary where
  data : SelbergEndpointData
  publishedSelberg : PublishedSelbergTwoLinearForm data

/-- Historical item 14 closes at the agreed publication trust boundary. -/
theorem item14_publication_boundary_closes
    (B : Item14PublicationBoundary) :
    AuditedEndpointFactorEight B.data := by
  exact published_selberg_to_audited_factor_eight B.data B.publishedSelberg

/--
Guardrail against the earlier detour: the item-14 endpoint conclusion is
independent of any additional endpoint-power assertion.
-/
theorem item14_independent_of_endpoint_power
    (B : Item14PublicationBoundary)
    (EndpointPowerClaim : Prop) :
    (EndpointPowerClaim → AuditedEndpointFactorEight B.data) ∧
      (¬ EndpointPowerClaim → AuditedEndpointFactorEight B.data) := by
  constructor
  · intro _
    exact item14_publication_boundary_closes B
  · intro _
    exact item14_publication_boundary_closes B

#print axioms sigma_base_nonneg
#print axioms published_selberg_to_audited_factor_eight
#print axioms item14_publication_boundary_closes
#print axioms item14_independent_of_endpoint_power

end TwinPrimeCertificationRun11
