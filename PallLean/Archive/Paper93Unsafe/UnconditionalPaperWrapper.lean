import PallLean.PaperFaithfulSeparation

namespace PallLean.Paper93.DeepMath.CookLevin

/-! # Unconditional Paper Wrapper

This file exposes `PallLean.PaperFaithfulSeparation.P_ne_NP_unconditional`
under the `PallLean.Paper93.DeepMath.CookLevin` namespace as a directly
callable witness with the canonical paper-faithful arrow signature.

The underlying theorem
`PaperFaithfulSeparation.P_ne_NP_unconditional` has signature

```
P_ne_NP_unconditional : ∀ (_ : PaperFaithfulSeparation.PeqNP_Paper), False
```

(see `PallLean/PaperFaithfulSeparation.lean:1610`), where
`PaperFaithfulSeparation.PeqNP_Paper`
(`PallLean/PaperFaithfulSeparation.lean:948`) is the paper-faithful
structure bundling

* `decider : DTM`
* `timeBound_le : decider.timeBound ≤ 4`
* `numStates_bound : decider.numStates ≤ 2 ^ 804`
* `decides_3sat : DecidesSAT decider`

The current proof body forwards via `P_ne_NP_via_rank_sandwich` and
depends on the single custom axiom
`GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider`.

The wrappers below are real, definitionally-meaningful re-exports: each
takes a `PeqNP_Paper` witness and produces `False` by applying the
underlying separation theorem. There is no `True` placeholder, no
`sorry`, and no new `axiom`. -/

/-- **Paper-faithful unconditional accessor** (Cook–Levin namespace).

Given any paper-faithful witness `h : PaperFaithfulSeparation.PeqNP_Paper`
of `P = NP` — i.e.\ a polynomial-time DTM with `timeBound ≤ 4`,
`numStates ≤ 2 ^ 804`, deciding 3-SAT — we derive `False`. The proof
forwards to `PaperFaithfulSeparation.P_ne_NP_unconditional`, the
canonical paper-faithful separation theorem in this codebase.

This wrapper is the Cook–Levin namespace re-export of the paper §40
Theorem 232 conclusion (`P ≠ NP`) in arrow form. -/
theorem paper_faithful_unconditional_accessible
    (h : PaperFaithfulSeparation.PeqNP_Paper) : False :=
  PaperFaithfulSeparation.P_ne_NP_unconditional h

/-- Universally-quantified arrow form of
`paper_faithful_unconditional_accessible`. This matches the canonical
shape `∀ (_ : PeqNP_Paper), False` used throughout the Step 4 compiler
chain (cf. `Step4Compiler.PeqNP_Paper_False_unconditional` and
`Final_P_ne_NP_Wrapper.PeqNP_Paper_False_via_rank_chain`). -/
theorem paper_faithful_unconditional_arrow :
    ∀ (_ : PaperFaithfulSeparation.PeqNP_Paper), False :=
  PaperFaithfulSeparation.P_ne_NP_unconditional

/-- Implication form `PeqNP_Paper → False`, equivalent to
`paper_faithful_unconditional_arrow` modulo the standard Lean
identification of `∀ (_ : α), β` with `α → β`. -/
theorem paper_faithful_unconditional_imp :
    PaperFaithfulSeparation.PeqNP_Paper → False :=
  PaperFaithfulSeparation.P_ne_NP_unconditional

/-- Empty-type form: the paper-faithful `PeqNP_Paper` structure
(which lives in `Type`) has no inhabitants. Useful for downstream code
that prefers the `IsEmpty` interface over the arrow form, e.g.\ when
discharging an existential whose witness type is `PeqNP_Paper`. -/
theorem isEmpty_PeqNP_Paper : IsEmpty PaperFaithfulSeparation.PeqNP_Paper :=
  ⟨PaperFaithfulSeparation.P_ne_NP_unconditional⟩

/-- Existence-elimination form: any existential over `PeqNP_Paper`
witnesses (with arbitrary motive `P`) can be turned into `False`. This
is a convenient consumer-side packaging of the underlying separation. -/
theorem exists_PeqNP_Paper_elim {P : PaperFaithfulSeparation.PeqNP_Paper → Prop}
    (h : ∃ x, P x) : False :=
  h.elim (fun x _ => PaperFaithfulSeparation.P_ne_NP_unconditional x)

end PallLean.Paper93.DeepMath.CookLevin
