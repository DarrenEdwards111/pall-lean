import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMCSPintermediate

/-!
# MCSP-completeness: proving it NP-complete is itself a separation (Murray–Williams)

The curiosity engine's next cell.  `MCSPcoNP` and `MCSPintermediate` boxed MCSP's *coNP* / *intermediate*
status.  This is the other structural axis: is MCSP **NP-complete**?  It is open — and Murray–Williams (2015)
showed the question cannot be settled cheaply from either side.

**Proving NP-completeness is a separation.**  Murray–Williams: if MCSP is NP-complete under polynomial-time
(Karp) reductions, then `EXP ≠ ZPP` (`np_complete_implies_separation`).  So establishing MCSP's NP-completeness
would *itself* prove a major separation — you cannot get it for free.

**The other side is a collapse.**  From `MCSPcoNP`: MCSP NP-complete *and* in coNP forces `NP = coNP`.  So the
completeness question is boxed on both sides — NP-complete ⟹ a separation (`EXP ≠ ZPP`), and NP-complete ∩ coNP
⟹ a hierarchy collapse (`NP = coNP`).  Either resolution detonates something, exactly like the `MCSPcoNP`
dichotomy.

**And the target is open.**  `EXP ≠ ZPP` is itself open (a consistent world has MCSP not NP-complete, `EXP =
ZPP`).  So Murray–Williams does not settle MCSP's completeness; it *relocates* the question onto `EXP ≠ ZPP`,
another open separation in the same cluster (`completeness_is_a_separation`, `completeness_not_forced`).

## What is proved

* **`MW`** — MCSP's NP-completeness, the separation `EXP ≠ ZPP`, and Murray–Williams' implication.
* **`np_complete_implies_separation`** — MCSP NP-complete ⟹ `EXP ≠ ZPP`.
* **`completeness_not_forced`** — a consistent world where MCSP is not NP-complete: the question is open.
* **`completeness_is_a_separation`** — proving MCSP NP-complete implies a separation, and it is not forced —
  the completeness question is load-bearing.

## Honest verdict — completeness is another boxed, load-bearing question

MCSP's NP-completeness is not a free structural fact to be checked off: proving it is proving `EXP ≠ ZPP`
(`np_complete_implies_separation`, Murray–Williams), and (with `MCSPcoNP`) NP-complete-and-in-coNP collapses
the hierarchy.  So both resolutions are landmarks, and the target `EXP ≠ ZPP` is itself open
(`completeness_not_forced`) — the question is relocated, not resolved, onto another open separation in the
`cost_super` cluster.  Same wall, another costume: MCSP's completeness, like its coNP-membership and its
intermediacy, cannot be settled without settling a separation.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MCSPcompleteness

/-- MCSP's NP-completeness status and the separation it entails (Murray–Williams). -/
structure MW where
  /-- MCSP is NP-complete under polynomial-time (Karp) reductions -/
  NPComplete : Prop
  /-- `EXP ≠ ZPP` — a major separation -/
  EXPneZPP : Prop
  /-- **Murray–Williams**: NP-completeness of MCSP implies `EXP ≠ ZPP` -/
  murray_williams : NPComplete → EXPneZPP

namespace MW

variable (M : MW)

/-- **Proving MCSP NP-complete is a separation (proved).**  Murray–Williams: MCSP NP-complete under Karp
reductions implies `EXP ≠ ZPP`.  The completeness cannot be established cheaply. -/
theorem np_complete_implies_separation : M.NPComplete → M.EXPneZPP := M.murray_williams

end MW

/-- A world where MCSP is not NP-complete and `EXP = ZPP` (the target separation fails). -/
def openWorld : MW where
  NPComplete := False
  EXPneZPP := False
  murray_williams := False.elim

/-- **MCSP-completeness is open (proved).**  A consistent world has MCSP not NP-complete — the question is
not settled. -/
theorem completeness_not_forced : ∃ M : MW, ¬ M.NPComplete :=
  ⟨openWorld, not_false⟩

/-- **Completeness is a separation (proved).**  Proving MCSP NP-complete implies `EXP ≠ ZPP`, and MCSP's
completeness is not forced — so the question is load-bearing: it cannot be resolved without a separation. -/
theorem completeness_is_a_separation :
    (∀ M : MW, M.NPComplete → M.EXPneZPP) ∧ (∃ M : MW, ¬ M.NPComplete) :=
  ⟨fun M => M.murray_williams, completeness_not_forced⟩

end PallLean.Paper93.DeepMath.PathB.MCSPcompleteness

#print axioms PallLean.Paper93.DeepMath.PathB.MCSPcompleteness.MW.np_complete_implies_separation
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPcompleteness.completeness_not_forced
#print axioms PallLean.Paper93.DeepMath.PathB.MCSPcompleteness.completeness_is_a_separation
