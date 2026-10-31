import Mathlib.Data.Nat.Basic

/-!
# The expander's teeth: how p-vs-np1 verifies, and where they slip

The compression shortcut needs **teeth** — rigid structure to bite onto.  Darren's `p-vs-np1`
(`ExpanderResonator`, `82995b40`) supplies them: a **Ramanujan expander has no small cut** — a rigid,
incompressible structure whose separation is large.  So "how does p-vs-np1 verify?"  The expander's cut is
the teeth; the bound *verifies* (bites) exactly when the circuit cost does **not slip below the cut**, and
the gap where it can slip is `cost_super`.

## The model

The expander gives a large `cut` (its separation — the teeth; Ramanujan ⟹ no small cut).  The circuit's
`cost` may dip below the cut by a `compression` amount — a circuit *smaller than its cut* is exactly mass
production.  So `cost + compression = cut`: `cost = cut − compression`.  `compression = 0` is the structural
model (`c = sep`), where the teeth bite fully.

## What is proved

* **`teeth_bite_no_compression`** — with no compression (`c = sep`), the cost equals the full cut:
  `cost = cut`.
* **`expander_forces_bound`** — then the expander's large cut transfers to the cost: `L ≤ cut ⟹ L ≤ cost`.
  This is how p-vs-np1 verifies — in the structural model the rigid cut *forces* the bound (super-linear /
  `2^d`).
* **`compression_slips_teeth`** — but any compression makes the cost slip below the cut: `compression > 0`
  ⟹ `cost < cut`.  The teeth don't bite.
* **`verifies_iff_no_compression`** — the bound bites (`cost = cut`) **iff** `compression = 0`.

## Honest scope — the teeth are real; whether they bite is the wall

p-vs-np1 genuinely verifies **in the structural model** (`c = sep`: formula / branching program), where the
expander's no-small-cut rigidity forces the bound — that is proved (`ExpanderResonator`), and the teeth are
real (a Ramanujan expander truly has no small cut).  But a general circuit can have `cost < cut` — cost
below its own separation — which *is* mass production / sharing.  `verifies_iff_no_compression`: the teeth
bite exactly when `compression = 0`, i.e. `c = sep`, i.e. no mass production — which is `cost_super`.

And this closes the compression thread: `compression` here is the `savings` of `HeuristicShortcut` — the
exploited shared structure.  The expander is the **incompressible core** (no small cut = nothing to
compress), so it is where the heuristic shortcut has no teeth to bite — and it forces the bound *only* when
the circuit likewise cannot compress below the cut.  Teeth (expander) and no-teeth (incompressible core) are
the same wall: p-vs-np1 verifies iff no compression, and no-compression-for-SAT is `cost_super`.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExpanderTeeth

/-- The expander as **teeth**: a rigid separation `cut` (Ramanujan ⟹ no small cut), the circuit `cost`, and
the `compression` by which the cost slips below the cut (a circuit smaller than its cut = mass production).
`slip : cost + compression = cut`. -/
structure ExpanderTeeth where
  /-- the expander's cut / separation — the teeth (large, no small cut) -/
  cut : ℕ
  /-- the circuit cost -/
  cost : ℕ
  /-- how far the cost slips below the cut (= mass production / sharing) -/
  compression : ℕ
  /-- cost = cut − compression -/
  slip : cost + compression = cut

/-- **No compression ⟹ teeth bite fully (proved).**  In the structural model (`c = sep`, `compression = 0`)
the cost equals the full cut: `cost = cut`. -/
theorem teeth_bite_no_compression (E : ExpanderTeeth) (h0 : E.compression = 0) : E.cost = E.cut := by
  have h := E.slip
  omega

/-- **The expander forces the bound (proved).**  With no compression, the expander's large cut transfers to
the cost: `L ≤ cut ⟹ L ≤ cost`.  This is how p-vs-np1 verifies — the rigid cut forces the bound. -/
theorem expander_forces_bound (E : ExpanderTeeth) (L : ℕ) (h0 : E.compression = 0) (hcut : L ≤ E.cut) :
    L ≤ E.cost := by
  have h := E.slip
  omega

/-- **Compression slips the teeth (proved).**  Any compression makes the cost dip below the cut:
`compression > 0 ⟹ cost < cut`.  A circuit smaller than its cut — mass production — and the teeth don't
bite. -/
theorem compression_slips_teeth (E : ExpanderTeeth) (hpos : 0 < E.compression) : E.cost < E.cut := by
  have h := E.slip
  omega

/-- **Verifies iff no compression (proved).**  The teeth bite (`cost = cut`) exactly when there is no
compression (`c = sep`).  So p-vs-np1 verifies iff the circuit cannot compress below the cut — which for SAT
is `cost_super`. -/
theorem verifies_iff_no_compression (E : ExpanderTeeth) : E.cost = E.cut ↔ E.compression = 0 := by
  have h := E.slip
  omega

/-- The structural model: teeth bite, cost equals the full cut `100`. -/
def biteWitness : ExpanderTeeth where
  cut := 100
  cost := 100
  compression := 0
  slip := by decide

/-- The general model: the cost slips `5` below the cut (mass production), teeth don't fully bite. -/
def slipWitness : ExpanderTeeth where
  cut := 100
  cost := 95
  compression := 5
  slip := by decide

end PallLean.Paper93.DeepMath.PathB.ExpanderTeeth

#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderTeeth.expander_forces_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ExpanderTeeth.verifies_iff_no_compression
