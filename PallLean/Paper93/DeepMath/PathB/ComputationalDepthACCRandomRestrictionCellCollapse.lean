import PallLean.Paper93.DeepMath.PathB.ComputationalDepthManyGateCorrelation

/-!
# Past the shattering wall: restriction collapses cells

`…ManyGateCorrelation` pinned the engine's reach to a gate‑count threshold: with `≥ ⌈log₂ n⌉` modular supports the
cells can shatter the coordinates into singletons and the involution dies.  The route past it (switching‑lemma
strategy): **a restriction simplifies the supports so the live coordinates regain large cells**, after which the
existing same‑cell witness machinery bites on the restricted instance.

This file proves the *combinatorial* half of that route deterministically, and names the *probabilistic* half (a
random restriction actually collapses ACC⁰ supports) as the open switching‑strength hypothesis.

The clean cell‑collapse mechanism: if every support is **trivial on the live set `L`** (`L` lies entirely inside
or entirely outside each support), then *all* live coordinates share one cell — so any two of them are a
same‑cell pair, and any holonomy support `D` separating two live coordinates is a witness.  A concrete instance
needing no probability: if the supports' union misses `≥ 2` coordinates (bounded fan‑in too small to cover), those
untouched coordinates share the empty cell.

## What is proved (clean axioms, no `sorry`)

* `exists_sameCell_pair_on` — relativized pigeonhole: `2^k <` (#live coordinates) ⇒ a same‑cell live pair.
* `TrivialOn`, `sameCell_of_trivialOn`, `cellWitness_of_trivialOn` — **cell collapse**: supports trivial on `L`
  ⇒ all live coordinates share a cell ⇒ a separating `D` is a witness.
* `collapse_gives_cellWitness`, `collapse_gives_low_correlation` — **the plug‑in**: a collapsing restriction gives
  a witness, and (via `kGate_low_correlation_offdiagonal`) the `k`‑gate ACC⁰ predictor has no correlation
  advantage against the restricted holonomy parity.
* `exists_untouched_pair`, `exists_cellWitness_of_small_union` — **the bounded‑support instance** (no probability):
  if `⋃_j S_j` misses `≥ 2` coordinates, the engine bites.

## The named open step (the switching‑strength half)

* `ACC0RestrictionCollapsesCells` — a small‑depth ACC⁰ support family admits a restriction leaving `≥ 2` live
  coordinates on which the supports are trivial (cells collapse).  Proving a *random* restriction achieves this
  for ACC⁰ is the Håstad/Razborov–Smolensky switching content — `NP ⊄ ACC⁰`‑strength.  Granted it,
  `acc0_collapse_gives_cellWitness` discharges the rest: collapse ⇒ witness ⇒ the engine bites again below the
  live‑variable threshold, so the ACC⁰ predictor fails on the restricted holonomy parity.

This is route 2 in skeleton: the deterministic cell combinatorics are proved; the one probabilistic switching step
is isolated and named.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse

open PallLean.Paper93.DeepMath.PathB.HolonomyBalanceFragments
open PallLean.Paper93.DeepMath.PathB.ManyGateCorrelation

variable {n k : ℕ}

/-! ## Relativized pigeonhole on the live set -/

/-- **A restriction leaving more than `2^k` live coordinates already has a same‑cell live pair (proved).**  The
cell map restricted to `L` cannot be injective when `2^k < |L|`. -/
theorem exists_sameCell_pair_on (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : 2 ^ k < L.card) :
    ∃ v ∈ L, ∃ w ∈ L, v ≠ w ∧ SameCell supports v w := by
  have hcard : (Finset.univ : Finset (Fin k → Bool)).card < L.card := by
    rw [Finset.card_univ]
    calc Fintype.card (Fin k → Bool) = 2 ^ k := by simp [Fintype.card_fin, Fintype.card_bool]
      _ < L.card := h
  obtain ⟨v, hv, w, hw, hne, hmap⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := cellMap supports) (fun a _ => Finset.mem_univ _)
  exact ⟨v, hv, w, hw, hne, (sameCell_iff_cellMap supports v w).mpr hmap⟩

/-! ## Cell collapse: trivial supports on the live set -/

/-- A support family is **trivial on `L`** if each support lies entirely inside or entirely outside `L`. -/
def TrivialOn (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : Prop :=
  ∀ j, Disjoint (supports j) L ∨ L ⊆ supports j

/-- **Cell collapse (proved): trivial supports ⇒ all live coordinates share one cell.** -/
theorem sameCell_of_trivialOn (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (htr : TrivialOn supports L) (v w : Fin n) (hv : v ∈ L) (hw : w ∈ L) :
    SameCell supports v w := by
  intro j
  rcases htr j with hdis | hsub
  · have hv' : v ∉ supports j := Finset.disjoint_right.mp hdis hv
    have hw' : w ∉ supports j := Finset.disjoint_right.mp hdis hw
    exact ⟨fun h => absurd h hv', fun h => absurd h hw'⟩
  · exact ⟨fun _ => hsub hw, fun _ => hsub hv⟩

/-- **A separating `D` on collapsed cells is a witness (proved).** -/
theorem cellWitness_of_trivialOn (supports : Fin k → Finset (Fin n)) (L D : Finset (Fin n))
    (htr : TrivialOn supports L) (v w : Fin n) (hv : v ∈ L) (hw : w ∈ L) (hne : v ≠ w)
    (hvD : v ∈ D) (hwD : w ∉ D) : CellWitness supports D :=
  ⟨v, w, hne, hvD, hwD, sameCell_of_trivialOn supports L htr v w hv hw⟩

/-- **The plug‑in (proved): a collapsing restriction with `≥ 2` live coordinates yields a holonomy support the
engine bites on.** -/
theorem collapse_gives_cellWitness (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (htr : TrivialOn supports L) (hL : 2 ≤ L.card) :
    ∃ D : Finset (Fin n), CellWitness supports D := by
  obtain ⟨v, hv, w, hw, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < L.card)
  exact ⟨{v}, v, w, hne, Finset.mem_singleton_self v,
    fun h => hne (Finset.mem_singleton.mp h).symm, sameCell_of_trivialOn supports L htr v w hv hw⟩

/-- **Low correlation after collapse (proved): with the supports trivial on `L`, a holonomy support `D` separating
two live coordinates leaves the `k`‑gate ACC⁰ predictor with no correlation advantage on the off‑diagonal.** -/
theorem collapse_gives_low_correlation (supports : Fin k → Finset (Fin n)) (L D : Finset (Fin n))
    (htr : TrivialOn supports L) (v w : Fin n) (hv : v ∈ L) (hw : w ∈ L) (hne : v ≠ w)
    (hvD : v ∈ D) (hwD : w ∉ D) (g : (Fin k → ℕ) → Bool) :
    2 * (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).filter
          (fun x => g (weightVec supports x) = fParity D x)).card
      ≤ ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => x v ≠ x w)).card :=
  kGate_low_correlation_offdiagonal supports D v w hne hvD hwD
    (sameCell_of_trivialOn supports L htr v w hv hw) g

/-! ## Bounded‑support instance (no probability): too small to cover -/

/-- Two coordinates outside every support share the empty cell. -/
theorem sameCell_of_not_mem_union (supports : Fin k → Finset (Fin n)) (v w : Fin n)
    (hv : ∀ j, v ∉ supports j) (hw : ∀ j, w ∉ supports j) : SameCell supports v w :=
  fun j => ⟨fun h => absurd h (hv j), fun h => absurd h (hw j)⟩

/-- **If the supports' union misses `≥ 2` coordinates, two of them are untouched (proved).** -/
theorem exists_untouched_pair (supports : Fin k → Finset (Fin n))
    (h : (Finset.univ.biUnion supports).card + 1 < n) :
    ∃ v w, v ≠ w ∧ (∀ j, v ∉ supports j) ∧ (∀ j, w ∉ supports j) := by
  have hcard : 1 < (Finset.univ.biUnion supports)ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨v, hv, w, hw, hne⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_compl, Finset.mem_biUnion] at hv hw
  push_neg at hv hw
  exact ⟨v, w, hne, fun j => hv j (Finset.mem_univ j), fun j => hw j (Finset.mem_univ j)⟩

/-- **The bounded‑support instance (proved): if the supports cannot cover all but one coordinate, the engine bites
— no probability needed.** -/
theorem exists_cellWitness_of_small_union (supports : Fin k → Finset (Fin n))
    (h : (Finset.univ.biUnion supports).card + 1 < n) :
    ∃ D : Finset (Fin n), CellWitness supports D := by
  obtain ⟨v, w, hne, hv, hw⟩ := exists_untouched_pair supports h
  exact ⟨{v}, v, w, hne, Finset.mem_singleton_self v,
    fun hmem => hne (Finset.mem_singleton.mp hmem).symm, sameCell_of_not_mem_union supports v w hv hw⟩

/-! ## The named switching step, and the discharge -/

/-- **(Named open — switching / `NP ⊄ ACC⁰`‑strength).**  A small‑depth ACC⁰ support family admits a restriction
leaving `≥ 2` live coordinates on which the supports are trivial (cells collapse).  Proving a *random* restriction
achieves this for ACC⁰ is the Håstad / Razborov–Smolensky switching content. -/
def ACC0RestrictionCollapsesCells (supports : Fin k → Finset (Fin n)) : Prop :=
  ∃ L : Finset (Fin n), 2 ≤ L.card ∧ TrivialOn supports L

/-- **The discharge (proved): granted the switching step, the engine bites** — a collapsing restriction yields a
holonomy support the `k`‑gate ACC⁰ predictor cannot correlate with, past the shattering wall. -/
theorem acc0_collapse_gives_cellWitness (supports : Fin k → Finset (Fin n))
    (h : ACC0RestrictionCollapsesCells supports) : ∃ D : Finset (Fin n), CellWitness supports D := by
  obtain ⟨L, hL, htr⟩ := h
  exact collapse_gives_cellWitness supports L htr hL

/-! ## A *proved* deterministic switching instance: bounded fan‑in

For depth‑2 / bounded‑fan‑in supports (`|S_j| ≤ s`) there is an explicit, non‑random restriction achieving
`TrivialOn`: **kill every touched coordinate** — take the live set to be the complement of the supports' union.
Every support is then disjoint from the live set, and `|live| = n − |⋃_j S_j| ≥ n − k·s`.  This turns
`ACC0RestrictionCollapsesCells` from a named hypothesis into a *proved* lemma on the bounded‑fan‑in fragment
(whenever `k·s + 2 ≤ n`), with no probability. -/

/-- **The explicit restriction is trivializing (proved): the complement of the supports' union is `TrivialOn`** —
every support is disjoint from it. -/
theorem trivialOn_compl_union (supports : Fin k → Finset (Fin n)) :
    TrivialOn supports (Finset.univ.biUnion supports)ᶜ := by
  intro j
  left
  rw [Finset.disjoint_right]
  intro a ha
  rw [Finset.mem_compl, Finset.mem_biUnion] at ha
  push_neg at ha
  exact ha j (Finset.mem_univ j)

/-- **The live set is large (proved): `n − k·s ≤ |live|`** for fan‑in `≤ s`. -/
theorem card_compl_union_ge (supports : Fin k → Finset (Fin n)) (s : ℕ)
    (hfan : ∀ j, (supports j).card ≤ s) :
    n - k * s ≤ (Finset.univ.biUnion supports)ᶜ.card := by
  rw [Finset.card_compl, Fintype.card_fin]
  have hbu : (Finset.univ.biUnion supports).card ≤ k * s :=
    calc (Finset.univ.biUnion supports).card
        ≤ ∑ j, (supports j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin k, s := Finset.sum_le_sum (fun j _ => hfan j)
      _ = k * s := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- **Deterministic switching for bounded fan‑in (proved): `ACC0RestrictionCollapsesCells` holds outright** when
the supports have fan‑in `≤ s` and `k·s + 2 ≤ n` — the explicit "kill all touched coordinates" restriction
trivializes them and leaves `≥ 2` live coordinates. -/
theorem boundedFanIn_collapsesCells (supports : Fin k → Finset (Fin n)) (s : ℕ)
    (hfan : ∀ j, (supports j).card ≤ s) (hsize : k * s + 2 ≤ n) :
    ACC0RestrictionCollapsesCells supports := by
  refine ⟨(Finset.univ.biUnion supports)ᶜ, ?_, trivialOn_compl_union supports⟩
  have := card_compl_union_ge supports s hfan
  omega

/-- **End‑to‑end on the bounded‑fan‑in fragment (proved): the engine bites with no hypothesis** — bounded fan‑in
that cannot cover the cube yields a holonomy support the predictor fails to correlate with. -/
theorem boundedFanIn_cellWitness (supports : Fin k → Finset (Fin n)) (s : ℕ)
    (hfan : ∀ j, (supports j).card ≤ s) (hsize : k * s + 2 ≤ n) :
    ∃ D : Finset (Fin n), CellWitness supports D :=
  acc0_collapse_gives_cellWitness supports (boundedFanIn_collapsesCells supports s hfan hsize)

end PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse.exists_sameCell_pair_on
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse.cellWitness_of_trivialOn
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse.collapse_gives_low_correlation
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse.exists_cellWitness_of_small_union
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse.acc0_collapse_gives_cellWitness
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse.trivialOn_compl_union
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse.boundedFanIn_collapsesCells
#print axioms PallLean.Paper93.DeepMath.PathB.ACCRandomRestrictionCellCollapse.boundedFanIn_cellWitness
