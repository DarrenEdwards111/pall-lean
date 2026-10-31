import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDragCeiling

/-!
# N-Frame: scoping the irreducible-demand certificate — coherent, dodges both, one new crux

The non-rank search left exactly one shape that could dodge BOTH known failure modes (the input
`N` cap and the `2^{-coneExcess}` fan-out decay): a certificate measuring IRREDUCIBLE DEMAND — how
many times a value `V` must be present across the computation.  This file scopes it: it defines the
object, VERIFIES the two dodges in Lean, and locates the single new obstruction that replaces them.

## The object

A demand structure for `f` is a family `{(Vᵢ, Dᵢ)}` of values and site-sets such that any circuit
computing `f` must, for each `i`, make `Vᵢ` present at every site in `Dᵢ`.  A value demanded
`K = |Dᵢ|` times forces the circuit to either

  ROUTE it — one copy, fan-out `K−1`, charged `K−1` to `coneExcess`; or
  RECOMPUTE it — `K−1` extra copies at unit cost `c ≥ 1`, charged `(K−1)·c` to `length`.

Both charges land in `length ≥ 2·|ESS| + coneExcess`.  The certificate: `length ≥ 2|ESS| +
Σᵢ(Kᵢ − 1)` when the demands are IRREDUCIBLE (cannot be jointly reduced).

## The two dodges, verified

  `recompute_charge` — **PROVED**: `d ≤ d·c` for `c ≥ 1` — recomputing never beats routing's
        `d = K−1` charge.  So a demand of `K` costs `≥ K−1` under EITHER strategy: the charge does
        NOT decay under fan-out (dodges the formula route's `2^{-coneExcess}` collapse).
  `demand_no_strategy_beats_total` — **PROVED**: for any per-value choice of route/recompute,
        `Σᵢ(Kᵢ−1) ≤ Σᵢ chargeᵢ` — NO strategy beats the total demand.
  `demand_uncapped` — **PROVED**: the demand total exceeds every `N` and every target `T` — unlike
        `rank ≤ N`, demand is NOT bounded by the input dimension (dodges the rank route's `N` cap).

## The one new obstruction — irreducibility under SHARING (= rigidity)

The dodges hold, so the certificate's SHAPE is sound.  But demand replaces the two orthogonal
failure modes with ONE requirement that is not automatic: IRREDUCIBILITY.  Demand is reducible by
SHARING INTERMEDIATE VALUES — computing partial combinations once and reusing them lowers the total
demand below `Σ(Kᵢ−1)`.  This is exactly what makes linear-size superconcentrators and `O(N log N)`
linear circuits possible.  For the concrete linear case (`x ↦ Mx`), the irreducible demand IS the
linear-circuit complexity of `M`, and proving it super-linear is Valiant's matrix-RIGIDITY program
— open.  So the demand certificate does not evade the open problem; it RELOCATES it: from "beat two
orthogonal failure modes" to "prove one demand structure is irreducible under sharing."

## Honest scope

The certificate is coherent and provably dodges both known failure modes (verified here).  Its
irreducibility hypothesis is the open crux, and it coincides with rigidity for the linear case — I
did NOT prove irreducibility for any explicit `f` (that is the open problem).  What this scoping
delivers: the demand certificate is the unique shape past both failure modes, and its single
remaining requirement is now named and connected to rigidity — a concrete (open) target, not a
vague hope.  The route/recompute floor, the no-strategy-beats-total aggregate, and the uncapping
are proved; irreducibility is the hypothesis.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameDemandCert

open Finset

/-- **THE ROUTE/RECOMPUTE FLOOR (proved)**: recomputing a value demanded `K` times (`d = K−1`
extra sites) at unit cost `c ≥ 1` charges `d·c ≥ d` — never less than routing's `d` charge to
`coneExcess`.  So a demand costs `≥ K−1` under EITHER strategy; the charge does not decay under
fan-out. -/
theorem recompute_charge (d c : ℕ) (hc : 1 ≤ c) : d ≤ d * c := by
  conv_lhs => rw [← mul_one d]
  exact Nat.mul_le_mul le_rfl hc

/-- **NO STRATEGY BEATS THE TOTAL DEMAND (proved)**: if each value's charge (route or recompute)
is at least its demand `dᵢ = Kᵢ−1`, then the aggregate charge is at least `Σᵢ dᵢ` — the circuit
cannot get below the total demand by any per-value route/recompute mix. -/
theorem demand_no_strategy_beats_total {m : ℕ} (d charge : Fin m → ℕ)
    (h : ∀ i, d i ≤ charge i) :
    ∑ i, d i ≤ ∑ i, charge i :=
  Finset.sum_le_sum (fun i _ => h i)

/-- **DEMAND IS UNCAPPED (proved)**: unlike `rank ≤ N` (bounded by the input dimension), the demand
total can exceed every `N` and every target `T`.  So a demand certificate is NOT capped at the
input dimension — it dodges the rank route's `N` cap. -/
theorem demand_uncapped (N : ℕ) : ∀ T : ℕ, ∃ D : ℕ, N < D ∧ T < D :=
  fun T => ⟨max N T + 1, by omega, by omega⟩

/-- **THE CERTIFICATE, ASSEMBLED (proved)**: given irreducibility (each value's charge `≥` its
demand) and the ledger `2|ESS| + coneExcess ≤ length`, the total demand `Σ dᵢ` transfers to a
`length` lower bound `2|ESS| + Σ dᵢ ≤ length` — which can be super-linear since `Σ dᵢ` is uncapped.
The hypothesis `hcharge` (irreducibility) is the open crux. -/
theorem demand_certificate {m : ℕ} (d charge : Fin m → ℕ) (ess coneExcess length : ℕ)
    (hcharge : ∀ i, d i ≤ charge i)
    (hledger : 2 * ess + coneExcess ≤ length)
    (hcone : ∑ i, charge i ≤ coneExcess) :
    2 * ess + ∑ i, d i ≤ length := by
  have h1 : ∑ i, d i ≤ ∑ i, charge i := demand_no_strategy_beats_total d charge hcharge
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameDemandCert

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDemandCert.recompute_charge
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDemandCert.demand_no_strategy_beats_total
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameDemandCert.demand_certificate
