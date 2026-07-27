import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEngineFaithfulnessAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSeparationTarget

/-!
# Route 2 assembled on the concrete faithful machine — the dent isolated

The magnification/uniform braid, built end-to-end over the CONCRETE classes (`NTIME`/`DTS`/`Σ₂`
over `ComposableMachine`) and routed through the DEBT-FAITHFUL engine at the `5/4` window (the one
the speedup/engine audit proved survives the one-tape overhead).  The result is the sharpest
statement of Route 2: `SAT ∉ P` follows from a fixed, named list of sockets, with the single genuine
wall — the DENT — isolated as one concrete `Prop`.

## The pieces

* **`ConcreteDent sparse p`** := `¬ DTS p sparse` — the sparse (magnifiable) target has no
  small-space `DTS(n^p)` algorithm.  This is the `n^{1+ε}`-strength statement the whole route rests
  on; on the `5/4` window it is a genuinely superlinear-but-modest bound.
* the four trading ingredients `ConcretePadding`/`ConcreteSlowdown`/`ConcreteHierarchy` +
  `debtSpeedup` (the one-tape speedup the audit established) — literature-strength / audited sockets.
* `trigger` — the magnification lever (published MMW/OPS theorem), concrete: `¬ DTS p sparse →
  SAT ∉ P`.
* `sparse_complete` — the sparse target is `NTIME(n^q)`-hard (the packaging that lets the engine's
  existential refutation land on `sparse` specifically); flagged OPEN/DUBIOUS.

## What is proved

* **`route2_direct`** — trigger + dent ⟹ `SAT ∉ P`.  The route with the dent taken as the single
  open input (bypasses `sparse_complete`).
* **`route2_via_engine_five_fourths`** — the full concrete assembly: the four ingredients (via the
  debt engine at `5/4`) refute `NTIME(4) ⊆ DTS(5)`; with `sparse_complete` that pins `¬ DTS 5 sparse`
  = the dent; with `trigger` this yields `SAT ∉ P`.  Every step over the concrete faithful model.
* **`route2_open_frontier`** — records that, `sparse_complete` and the literature sockets granted,
  the ENTIRE remaining content is `ConcreteDent`: the one concrete open sentence of the uniform
  route.

## Honest scope

Nothing here is closed: the dent is the wall, and it is where the route's difficulty concentrates —
but on the `5/4` window it is only an `n^{1+ε}`-strength uniform statement, the least this corpus
must prove to reach `SAT ∉ P` by any route (compare the circuit route's superpolynomial
`∀k∃n, n^k+k < cbudget`).  `sparse_complete` is the dubious socket (sparse compression targets are
not known `NTIME`-hard under the needed reductions); `route2_direct` shows a direct dent proof
bypasses it entirely.  The literature sockets are labor, not open mathematics; `debtSpeedup` is what
the one-tape model actually achieves (SpeedupAudit).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Route2Frontier

open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.EngineFaithfulnessAudit
open PallLean.Paper93.DeepMath.PathB.SeparationTarget

/-- **The dent**: the sparse magnifiable target has no small-space `DTS(n^p)` algorithm.  On the
`5/4` window this is an `n^{1+ε}`-strength uniform lower bound — the route's one genuine wall. -/
def ConcreteDent (sparse : Lang) (p : ℕ) : Prop := ¬ DTS p sparse

/-- **Route 2, direct (proved).**  The magnification trigger applied to the dent yields `SAT ∉ P`.
The route with the dent as its single open input. -/
theorem route2_direct (sparse : Lang) (p : ℕ)
    (trigger : ¬ DTS p sparse → SAT_not_in_P) (dent : ConcreteDent sparse p) :
    SAT_not_in_P :=
  trigger dent

/-- **Route 2 assembled through the debt-faithful engine at `5/4` (proved).**  The four concrete
ingredients drive the debt engine to refute `NTIME(4) ⊆ DTS(5)`; the sparse target's `NTIME(4)`-
hardness lands that refutation on `sparse`, giving the dent; the magnification trigger cashes it out
to `SAT ∉ P`.  Every step is over the concrete `ComposableMachine` model, on the faithful window the
audit proved survives the one-tape overhead. -/
theorem route2_via_engine_five_fourths (sparse : Lang)
    (hpad : ConcretePadding) (hslow : ConcreteSlowdown) (hhier : ConcreteHierarchy)
    (debtSpeedup : ∀ b, 1 ≤ b → ∀ L, DTS (2 * b) L → Sigma2 (b + 1) L)
    (sparse_complete : DTS 5 sparse → ∀ L, NTIME 4 L → DTS 5 L)
    (trigger : ¬ DTS 5 sparse → SAT_not_in_P) :
    SAT_not_in_P := by
  have hengine : ¬ (∀ L, NTIME 4 L → DTS 5 L) :=
    debt_engine 5 4 (by omega) (by omega) (by decide) hpad hslow hhier debtSpeedup
  have hdent : ¬ DTS 5 sparse := fun hd => hengine (sparse_complete hd)
  exact trigger hdent

/-- **The open frontier (proved).**  With the literature sockets and `sparse_complete` granted, the
entire remaining content of Route 2 is exactly the dent: `ConcreteDent sparse 5 ⟹ SAT ∉ P`.  The
uniform route is isolated to one concrete `Prop`. -/
theorem route2_open_frontier (sparse : Lang)
    (trigger : ¬ DTS 5 sparse → SAT_not_in_P) :
    ConcreteDent sparse 5 → SAT_not_in_P :=
  fun dent => route2_direct sparse 5 trigger dent

end PallLean.Paper93.DeepMath.PathB.Route2Frontier

#print axioms PallLean.Paper93.DeepMath.PathB.Route2Frontier.route2_direct
#print axioms PallLean.Paper93.DeepMath.PathB.Route2Frontier.route2_via_engine_five_fourths
#print axioms PallLean.Paper93.DeepMath.PathB.Route2Frontier.route2_open_frontier
