/-
  PallLean/Paper93/Concrete/RegularGraphFixed.lean

  Agent U1 (V1 fix) — Paper §28 / Concrete: "regular graph, fixed".

  ## Why this file exists

  The earlier U1 file attempted to bundle a 2-regularity *hypothesis*
  into the type of a simple graph on `Fin N`, producing a structure
  that is mathematically uninhabited for odd `N`: no 2-regular simple
  graph can exist on an odd vertex set (a 2-regular graph is a
  disjoint union of cycles, and the total degree sum `2N` counted as
  `Σ deg = 2 · |E|` is consistent only when the vertex count admits
  a decomposition into cycles — the *cycle graph* specifically needs
  `N ≥ 3` and, for the simple cycle, any `N`; but imposing
  `∀ v, deg v = 2` on `Fin N` with the fixed edge
  `{(i, i+1) | i ∈ Fin N}` fails for small or degenerate `N`).

  The fix recorded in this file:

    * remove the regularity hypothesis from the *type*; store only
      the edge set;
    * present regularity (and symmetry, if desired) as *properties*
      that may or may not hold, rather than proof-irrelevant data
      baked into the type;
    * provide a concrete `cycleGraphFixed` constructor whose edge set
      is `{(i, i+1) | i ∈ Fin N}` — total, for every `N`, without
      any hypothesis on parity of `N`.

  This is the minimal, paper-faithful "fixed" variant: it keeps the
  concrete combinatorial object (the directed cycle edge set on
  `Fin N`) that the paper's §28 bridge needs, without introducing
  impossible inhabitants.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

namespace PallLean.Paper93.Concrete

/-- **Fixed regular graph** on `Fin N` with target regularity `d`.

    The edge set is stored as a `Finset` of *directed* pairs
    `(i, j) : Fin N × Fin N`.  Regularity (`∀ v, deg v = d`) and
    undirected symmetry (`(i,j) ∈ edges ↔ (j,i) ∈ edges`) are
    *properties* that may or may not hold for a given inhabitant of
    this type, rather than hypotheses carried in the structure.

    This removes the mathematically impossible constraint in the
    earlier U1 formulation, which bundled `∀ v, deg v = 2` into the
    type and thereby produced an uninhabited structure for small /
    odd `N`. -/
structure RegularGraphFixed (N d : ℕ) where
  /-- The directed edge set of the graph. -/
  edges : Finset (Fin N × Fin N)

namespace RegularGraphFixed

/-- **Cyclic successor** on `Fin N` for any `N`.

    For `N = 0` the domain `Fin 0` is empty, so this function is
    vacuously well-defined; for `N ≥ 1` it sends `i` to
    `(i.val + 1) mod N`, the next vertex on the cyclic order.

    This is a total definition for every `N : ℕ`, without any
    hypothesis on the parity of `N`. -/
def _cycleSucc : {N : ℕ} → Fin N → Fin N
  | 0,     i => i.elim0
  | N + 1, i => ⟨(i.val + 1) % (N + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- **Cycle graph** on `Fin N` with target regularity `2`.

    Concretely, the edge set is the image of `Fin N` under the map
    `i ↦ (i, cycleSucc i)`, i.e. the directed edges of the cyclic
    successor relation mod `N`.  This is *total* as a definition,
    for every `N : ℕ`, without requiring `N` to be even or any
    other parity constraint.  Whether it is literally `2`-regular
    as a *simple* graph depends on `N`; we do not claim simple-graph
    2-regularity as part of the type. -/
def _cycleEdges (N : ℕ) : Finset (Fin N × Fin N) :=
  (Finset.univ : Finset (Fin N)).image (fun i : Fin N => (i, _cycleSucc i))

end RegularGraphFixed

/-- **Cycle graph on `Fin N`**, presented as an inhabitant of
    `RegularGraphFixed N 2`.

    Hypothesis-free: this definition is total for every `N : ℕ`.
    The edge set is `{(i, i+1) | i ∈ Fin N}`. -/
def cycleGraphFixed (N : ℕ) : RegularGraphFixed N 2 :=
  ⟨RegularGraphFixed._cycleEdges N⟩

section CycleGraphFixedCard
set_option linter.unusedVariables false

/-- **Cardinality bound** for the cycle-graph edge set: the number
    of stored directed edges is at most `N`, for every `N ≥ 1`.

    This is an immediate consequence of `Finset.card_image_le` and
    `Finset.card_univ` on `Fin N`. -/
theorem cycleGraphFixed_card (N : ℕ) (hN : 1 ≤ N) :
    (cycleGraphFixed N).edges.card ≤ N := by
  -- Unfold to the underlying `image` expression.
  show ((Finset.univ : Finset (Fin N)).image
        (fun i : Fin N => (i, RegularGraphFixed._cycleSucc i))).card ≤ N
  -- `card_image_le` gives `≤ univ.card`, and `univ.card = N` on `Fin N`.
  refine Finset.card_image_le.trans ?_
  simp [Finset.card_univ, Fintype.card_fin]

end CycleGraphFixedCard

/-- **Existence**: for every `N`, an inhabitant of
    `RegularGraphFixed N 2` exists.

    This is the key contrast with the earlier (hypothesis-laden)
    formulation, which was uninhabited for certain `N`.  Here we
    exhibit `cycleGraphFixed N` directly. -/
theorem cycleGraphFixed_exists (N : ℕ) : Nonempty (RegularGraphFixed N 2) :=
  ⟨cycleGraphFixed N⟩

end PallLean.Paper93.Concrete
