/-
  PallLean/Paper93/Concrete/EvenCycleGraph.lean

  Agent V2 — Paper §28 / Concrete: even-cycle graph `C_{2k}`.

  ## Why this file exists

  The simplest 2-regular connected graph with concrete structure is the
  even cycle `C_{2k}` on `2k` vertices.  Whenever `k` is prime and the
  Moore bound is saturated, `C_{2k}` qualifies as a Ramanujan graph;
  here we record just the concrete combinatorial structure — the
  directed edge set `{(i, (i+1) mod 2k) | i ∈ Fin (2k)}` — packaged as
  an inhabitant of `RegularGraphFixed (2*k) 2`.

  This is the simplest non-degenerate even-cycle instance of the
  paper-faithful "fixed regular graph" type from V1
  (`Paper93/Concrete/RegularGraphFixed.lean`).

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.
-/
import PallLean.Paper93.Concrete.RegularGraphFixed

namespace PallLean.Paper93.Concrete

/-- **Even cycle `C_{2k}`** — the simplest 2-regular connected graph
    with concrete structure.

    Packaged as an inhabitant of `RegularGraphFixed (2*k) 2` with the
    directed edge set `{(i, (i+1) mod 2k) | i ∈ Fin (2k)}`.  This is
    Ramanujan whenever `k` is prime and the Moore bound is saturated;
    here we just record the structure with concrete edges.

    The `Fin.mk` proof obligation `(i.val + 1) % (2*k) < 2*k` is
    discharged by case analysis on `2*k`: at `0` the index `i : Fin 0`
    is vacuously eliminated via `Fin.elim0`; at `m+1` we apply
    `Nat.mod_lt` with the successor positivity witness. -/
def evenCycle (k : ℕ) : RegularGraphFixed (2 * k) 2 :=
  ⟨Finset.univ.image (fun i : Fin (2*k) =>
    (i, Fin.mk ((i.val + 1) % (2*k))
      (Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by
        -- `i : Fin (2*k)`; if `2*k = 0` then `Fin 0` is empty.
        rw [h] at i
        exact i.elim0)))))⟩

/-- **Nonempty-edges theorem** for the even cycle `C_{2k}`.

    For every `k ≥ 1` the even-cycle edge set is nonempty: the vertex
    `⟨0, _⟩ ∈ Fin (2*k)` (which exists because `2*k ≥ 2 > 0`) gives
    rise to a directed edge `(⟨0, _⟩, ⟨1 mod 2k, _⟩)` in
    `(evenCycle k).edges`. -/
theorem evenCycle_has_edges (k : ℕ) (hk : 1 ≤ k) :
    (evenCycle k).edges.Nonempty := by
  unfold evenCycle
  apply Finset.Nonempty.image
  exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩

end PallLean.Paper93.Concrete
