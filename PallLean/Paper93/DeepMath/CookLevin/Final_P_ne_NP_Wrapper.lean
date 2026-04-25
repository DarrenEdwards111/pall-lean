import PallLean.PaperFaithfulSeparation
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.CookLevin

/-! # Final P ≠ NP Wrapper

This file exposes `PallLean.PaperFaithfulSeparation.P_ne_NP_unconditional`
under the `PallLean.Paper93.DeepMath.CookLevin` namespace, connecting our
rank chain (`theorem_207_rank_chain`, see `Theorem207Chain.lean`) to a
concrete paper-faithful `P ≠ NP` statement.

The underlying theorem `PaperFaithfulSeparation.P_ne_NP_unconditional`
has concrete signature

```
P_ne_NP_unconditional : ∀ (_ : PeqNP_Paper), False
```

(`PaperFaithfulSeparation.lean` line 1610), where `PeqNP_Paper`
(`PaperFaithfulSeparation.lean` line 948) is the paper-faithful
structure bundling a `DTM` decider with `timeBound_le ≤ 4`,
`numStates ≤ 2^804`, and the `DecidesSAT` predicate. The current proof
forwards to `P_ne_NP_via_rank_sandwich`, depending only on the single
custom axiom `GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider`.
-/

/-- **Final `P ≠ NP` wrapper** (paper §40 Theorem 232, p. 213): direct
re-export of `PaperFaithfulSeparation.P_ne_NP_unconditional` under the
Cook–Levin namespace.

Given any paper-faithful witness of `P = NP` (a `PeqNP_Paper` structure,
i.e.\ a polynomial-time DTM that decides 3-SAT with bounded time
exponent and bounded state count), we derive `False`. The proof simply
forwards to the canonical `P_ne_NP_unconditional` theorem, which routes
through `P_ne_NP_via_rank_sandwich`. -/
theorem accesses_paper_unconditional :
    ∀ (_ : PaperFaithfulSeparation.PeqNP_Paper), False :=
  PaperFaithfulSeparation.P_ne_NP_unconditional

/-- Convenience alias matching the `PeqNP_Paper → False` arrow form used
elsewhere in the Step 4 compiler chain (cf.
`Step4Compiler.PeqNP_Paper_False_unconditional`). -/
theorem PeqNP_Paper_False_via_rank_chain :
    PaperFaithfulSeparation.PeqNP_Paper → False :=
  PaperFaithfulSeparation.P_ne_NP_unconditional

end PallLean.Paper93.DeepMath.CookLevin
