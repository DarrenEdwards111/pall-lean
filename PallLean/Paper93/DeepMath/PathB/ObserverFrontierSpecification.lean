/-!
# Observer-relative frontier: conjecture, consequences, and obstruction map

**STATUS: SPECIFICATION, NOT A PROOF.**

This file records, in kernel-checkable form, exactly what the N-frame /
observer-centric program would need in order to separate P from NP, and exactly
where every attempted route is blocked.  It does **not** prove `P ≠ NP`, and it
is not a step toward such a proof.

The load-bearing object — the *observer faithfulness invariant* / *non-local
semantic force* — is an **assumed hypothesis** here.  It is non-constructive and
it is `P≠NP`-strength: establishing it *is* the separation.  Consequently:

> A clean `#print axioms` on the theorems below is **NOT** evidence of progress.
> The theorems are either (a) *conditional* on the assumed invariant, or
> (b) documentation of logical structure (the conservation dilemma).  The
> genuinely proven obstruction facts live in the named files in the map below.

This is the honest deliverable of the program: a precisely stated conjecture,
its conditional consequences, the one theorem that explains *why* the program
both correctly evades the natural-proofs barrier and supplies no leverage (the
conservation dilemma), and a map of where each concrete route terminates.

## Obstruction map (pointers to separately-proven facts and cited barriers)

* **Rank sandwich refuted.**  The central object of the God-Move route is
  self-contradictory: `Theorem207Witness → False` at paper scale, clean, no
  custom axioms (`theorem207Witness_uninhabitable`).  The P-side rank bound
  `rank ≤ n^200` is false because the real Cook–Levin compiled polynomial has
  super-polynomial SPDP rank for *every* DTM (`compiled_np_lower_bound_any_dtm`,
  `PallLean/GodMoveReal.lean`).  Rank does not separate P from NP; it is a
  *natural property* (empirically: `scripts/spdp_separation_test.py` ties
  `det` and `perm`).

* **Restricted models saturate.**  Set-multilinear / NW families: Reed–Solomon
  is the envelope, ratio `R = q`, slope `1.00`; no evolved family beats it
  (`scripts/spdp_scaling_search.py`).  ROABP marks VP-easy polynomials (IMM,
  det) as hard.  All real, all bounded-model, none reach general P.

* **Energy route foreclosed.**  Bennett reversibility decouples energy from
  complexity, so the thermodynamic P-side bound is `~0`
  (`...ThermodynamicObserverBarrier.lean`, Bennett guardrail).

* **Metacomplexity bridge is separation-strength.**  The hardness-magnification
  package is provably equivalent to `¬(SAT ∈ P)` (commit `42d1fd10`,
  `...HardnessMagnificationSocket.lean`): it relocates `P≠NP`, it does not
  reduce it.

* **Cited external barriers.**  Razborov–Rudich (natural proofs): a
  *constructive*, *large* invariant cannot be *useful*.  CHOPRS (locality):
  blocks the magnification trigger.  The observer invariant evades natural
  proofs only by being non-constructive — which is exactly the conservation
  dilemma below.
-/

namespace ObserverFrontier

variable {Machine : Type}

/-! ## 1. The conjecture: the assumed, unproven, non-constructive invariant -/

/-- **CONJECTURE (assumed, unproven, non-constructive).**

The observer faithfulness invariant — the "non-local semantic force": every
polynomial-time SAT decider is *forced* to make the canonical God-Move boundary
visible (i.e. to faithfully encode the full counterfactual SAT/UNSAT bulk).

This is the breakthrough the program is missing.  It is *stated here, not
proved*.  The concrete instance is `SignedDTMDecidesSAT → CanonicalGodMove-
BoundaryVisible` in `ComputationalDepthNonLocalSemanticForce.lean`. -/
def ObserverForce (DecidesSAT BoundaryVisible : Machine → Prop) : Prop :=
  ∀ M, DecidesSAT M → BoundaryVisible M

/-! ## 2. Consequence — conditional on the conjecture -/

/-- **CONSEQUENCE (conditional).**  The proven downstream wiring
(`BoundaryVisible → SheetEssential`) composed with the *assumed* force gives the
essentiality endpoint for every decider.

Everything here is conditional on `force`; nothing here proves `force`. -/
theorem essentiality_of_decider
    {DecidesSAT BoundaryVisible SheetEssential : Machine → Prop}
    (wiring : ∀ M, BoundaryVisible M → SheetEssential M)
    (force : ObserverForce DecidesSAT BoundaryVisible)
    {M : Machine} (hM : DecidesSAT M) :
    SheetEssential M :=
  wiring M (force M hM)

/-- **THE SECOND OPEN/REFUTED LINK.**  Even granting the force, the original
program discharged the separation through the *rank sandwich*, which is refuted
(`theorem207Witness_uninhabitable`).  We name the proposition; we do **not**
prove it, and the only route that would (rank) is closed.  So the program has
*two* gaps, not one: the unproved force, and the broken discharge. -/
def ProgramYieldsSeparation
    (DecidesSAT BoundaryVisible : Machine → Prop) (Separation : Prop) : Prop :=
  ObserverForce DecidesSAT BoundaryVisible → Separation

/-! ## 3. The conservation dilemma (the honest crux) -/

/-- **CONSERVATION OF DIFFICULTY (the crux theorem).**

Model a candidate hardness invariant by four propositions:
`Constructive` (it is efficiently computable), `Large` (it holds for a large
fraction of objects), `Useful` (it genuinely certifies the separation), and
`Separation` (the target, `¬(SAT ∈ P)`).

Take the two facts that are *not* in dispute:
* `useful_gives_separation` — a useful invariant yields the separation, by the
  meaning of "useful";
* `razborov_rudich` — the cited external barrier: a constructive *and* large
  invariant cannot be useful.

Then any useful, large invariant is **simultaneously**:
* `¬ Constructive` — it must be *non-constructive*, hence it *evades* the
  natural-proofs barrier; and
* `Separation` — establishing it *is* the open problem.

These are the same fact wearing two faces.  This is precisely why the
observer-relative program is the right *shape* (non-constructive ⇒ not a natural
property) and yet supplies *no leverage* (non-constructive ⇒ as hard as the
separation).  Evading the barrier and proving `P≠NP` are the same act. -/
theorem conservation_dilemma
    (Constructive Large Useful Separation : Prop)
    (useful_gives_separation : Useful → Separation)
    (razborov_rudich : Constructive → Large → ¬ Useful)
    (hU : Useful) (hL : Large) :
    ¬ Constructive ∧ Separation :=
  ⟨fun hC => razborov_rudich hC hL hU, useful_gives_separation hU⟩

/-- Horn 1 in isolation: a useful, large invariant is non-constructive. -/
theorem useful_large_imp_nonconstructive
    {Constructive Large Useful : Prop}
    (razborov_rudich : Constructive → Large → ¬ Useful)
    (hU : Useful) (hL : Large) : ¬ Constructive :=
  fun hC => razborov_rudich hC hL hU

/-- Horn 2 in isolation: establishing a useful invariant *is* the separation. -/
theorem useful_imp_separation
    {Useful Separation : Prop}
    (useful_gives_separation : Useful → Separation)
    (hU : Useful) : Separation :=
  useful_gives_separation hU

end ObserverFrontier

/-! ## 4. Kernel-only axiom trace

These traces are expected to be clean — and that cleanliness is *not* progress.
`essentiality_of_decider` is conditional on the assumed `force`; the dilemma
theorems are documentation of logical structure given the cited barrier.  Neither
proves the separation. -/

#print axioms ObserverFrontier.essentiality_of_decider
#print axioms ObserverFrontier.conservation_dilemma
#print axioms ObserverFrontier.useful_large_imp_nonconstructive
#print axioms ObserverFrontier.useful_imp_separation
