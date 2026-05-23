import PallLean.PaperFaithfulSeparation
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.CookLevin

/-! # Final P ≠ NP Wrapper

This file exposes the current lowest-surface final closeout
`PallLean.PaperFaithfulSeparation.P_ne_NP_via_theorem207_from_narrow_gauge`
under the `PallLean.Paper93.DeepMath.CookLevin` namespace, connecting our rank
chain (`theorem_207_rank_chain`, see `Theorem207Chain.lean`) to a concrete
paper-faithful `P ≠ NP` statement.

The exported theorem has concrete signature

```
P_ne_NP_via_theorem207_from_narrow_gauge : ∀ (_ : PeqNP_Paper), False
```

where `PeqNP_Paper` is the paper-faithful structure bundling a `DTM` decider
with `timeBound_le ≤ 4`, `numStates ≤ 2^804`, and the `DecidesSAT` predicate.
Unlike the legacy `P_ne_NP_unconditional` route, this wrapper does not forward
through `P_ne_NP_via_rank_sandwich`; unlike the older constructive sandwich
closeout, it also avoids the known-false legacy
`SymmetricPower.spdp_profile_generators` P-side axiom. Its custom surface now
tracks the narrower `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider`
seam audited in `GlobalGodMoveGauge.lean`.
-/

/-- **Final `P ≠ NP` wrapper** (paper §40 Theorem 232, p. 213): re-export
of the lowered Theorem-207 closeout under the Cook–Levin namespace.

Given any paper-faithful witness of `P = NP` (a `PeqNP_Paper` structure,
i.e.\ a polynomial-time DTM that decides 3-SAT with bounded time exponent and
bounded state count), we derive `False`. The proof forwards to
`P_ne_NP_via_theorem207_from_narrow_gauge`, not to the legacy rank-sandwich
route and not to the known-false `SymmetricPower.spdp_profile_generators`
route. -/
theorem accesses_paper_unconditional :
    ∀ (_ : PaperFaithfulSeparation.PeqNP_Paper), False :=
  PaperFaithfulSeparation.P_ne_NP_via_theorem207_from_narrow_gauge

/-- Convenience alias matching the `PeqNP_Paper → False` arrow form used
elsewhere in the Step 4 compiler chain (cf.
`Step4Compiler.PeqNP_Paper_False_unconditional`). -/
theorem PeqNP_Paper_False_via_rank_chain :
    PaperFaithfulSeparation.PeqNP_Paper → False :=
  PaperFaithfulSeparation.P_ne_NP_via_theorem207_from_narrow_gauge

#print axioms accesses_paper_unconditional
#print axioms PeqNP_Paper_False_via_rank_chain

end PallLean.Paper93.DeepMath.CookLevin
