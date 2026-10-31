import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheReasonShared
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The cohomological obstruction on the tower's incidence geometry

The local-to-global shape of the sharing question, made literal.  The blocks demand witness mass
locally; the adversary tries to satisfy all demands with a small global gate set; sharing is the
gluing.  This file builds the chain complex of that gluing problem and proves the obstruction
theorems that are true today.

## The complex

The **incidence complex** of a shared-witness circuit: 1-cells = incidences `(i, g)` with
`g ∈ witness i` (the edge set is `Finset.sigma`, so `|E| = Σᵢ|wᵢ|` — the witness mass);
0-cells = blocks ⊕ used gates.  Cochains are GF(2)-valued (`ZMod 2`); the **boundary map**
`∂ : C¹ → C⁰` sends an edge-vector to its vertex-incidence sums.  The **cycle space** `ker ∂` is
the first homology of the incidence geometry — its nontrivial elements are the closed loops
(block–gate–block–gate…) along which witness mass can be traded.

## What is proved

* **`boundary_add`** — `∂` is GF(2)-linear (by hand, no bundled algebra needed).
* **`acyclic_kills_sharing`** — trivial cycle space ⟹ `k·b ≤ |gates| + k`: if the incidence
  geometry has no cycles, the adversary keeps essentially nothing — the disjoint bound holds up
  to the trivial slack `k` (a spanning forest's worth).  Proof: trivial kernel ⟹ `∂` injective
  ⟹ `2^E ≤ 2^V` ⟹ `E ≤ V` — a cardinality argument, no rank-nullity required.
* **`acyclic_overlap_bound`** — the same, in the overlap language: trivial `H¹` ⟹ `overlap ≤ k`.
* **`sharing_forces_cycles` / `overlap_forces_cycles`** — the converse reading, and the honest
  headline: any circuit that BEATS the disjoint bound by more than `k` — any overlap beyond the
  forest slack — CONTAINS a nonzero cycle.  Mass production is not merely permitted by cycles;
  it is MADE of them.  The adversary's savings live in `H¹`, nowhere else.
* **`collapse_has_cycles`** — Uhlig calibration: the full-sharing collapse witness provably has
  nonzero cycles (obtained THROUGH the obstruction theorem, not by hand).

## Honest scope — what the obstruction does and does not do

This identifies WHERE the sharing lives (the cycle space of the incidence geometry) and proves
the two qualitative directions.  It does NOT bound the cycle space for circuits computing the
tower target — proving "SAT's semantics kills (or caps) `H¹` of every small circuit's incidence
geometry" is precisely `cost_super` in cohomological costume, and it is not attempted here.  Two
named next steps: (i) the quantitative form `overlap ≤ k + log₂|ker ∂|` (rank–nullity over
GF(2); machinery, not mystery), and (ii) wiring the SEMANTIC layer (`WitnessLocalization`) to
the cocycles — the open question becomes: can a nonlinear-on-many-blocks wire support a large
cycle space when the blocks are correlated?  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.IncidenceCohomology

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.TheReasonShared

variable {k b : ℕ}

/-- The **edge set** of the incidence complex: the block–gate incidences.  Its cardinality is the
witness mass `Σᵢ|wᵢ|`. -/
def edgeSet (C : SharedCircuitForTarget k b) : Finset ((_ : Fin k) × ℕ) :=
  Finset.univ.sigma (fun i => C.witness i)

theorem edgeSet_card (C : SharedCircuitForTarget k b) :
    (edgeSet C).card = ∑ i, (C.witness i).card := by
  rw [edgeSet, Finset.card_sigma]

theorem kb_le_edgeCard (C : SharedCircuitForTarget k b) : k * b ≤ (edgeSet C).card := by
  rw [edgeSet_card]
  exact kb_le_witness_sum C

/-- 1-cochains: GF(2) labellings of the incidence edges. -/
abbrev Cochain1 (C : SharedCircuitForTarget k b) := {e // e ∈ edgeSet C} → ZMod 2

/-- 0-cells: blocks on the left, used gates on the right. -/
abbrev Vert (C : SharedCircuitForTarget k b) := (Fin k) ⊕ {g // g ∈ distinctWitnesses C}

/-- 0-cochains: GF(2) labellings of the vertices. -/
abbrev Cochain0 (C : SharedCircuitForTarget k b) := Vert C → ZMod 2

/-- The **boundary map** `∂ : C¹ → C⁰`: an edge-vector's incidence sum at each vertex.  Its
kernel is the cycle space of the incidence geometry. -/
def boundary (C : SharedCircuitForTarget k b) (x : Cochain1 C) : Cochain0 C := fun v =>
  match v with
  | Sum.inl i => ∑ e, (if e.val.1 = i then x e else 0)
  | Sum.inr g => ∑ e, (if e.val.2 = g.val then x e else 0)

/-- `∂` is GF(2)-linear. -/
theorem boundary_add (C : SharedCircuitForTarget k b) (x y : Cochain1 C) :
    boundary C (x + y) = boundary C x + boundary C y := by
  funext v
  cases v with
  | inl i =>
    show (∑ e, if e.val.1 = i then (x + y) e else 0)
        = (∑ e, if e.val.1 = i then x e else 0) + (∑ e, if e.val.1 = i then y e else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : e.val.1 = i
    · simp [h]
    · simp [h]
  | inr g =>
    show (∑ e, if e.val.2 = g.val then (x + y) e else 0)
        = (∑ e, if e.val.2 = g.val then x e else 0)
          + (∑ e, if e.val.2 = g.val then y e else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : e.val.2 = g.val
    · simp [h]
    · simp [h]

theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem zmod2_cancel : ∀ a c : ZMod 2, a + c = 0 → a = c := by decide

/-- Trivial cycle space makes `∂` injective (GF(2): differences are sums). -/
theorem boundary_injective (C : SharedCircuitForTarget k b)
    (hker : ∀ x : Cochain1 C, boundary C x = 0 → x = 0) :
    Function.Injective (boundary C) := by
  intro x y hxy
  have hsum : boundary C (x + y) = 0 := by
    rw [boundary_add, hxy]
    funext v
    exact zmod2_add_self (boundary C y v)
  have hxy0 : x + y = 0 := hker (x + y) hsum
  funext e
  exact zmod2_cancel (x e) (y e) (congrFun hxy0 e)

/-- **The Euler bound (proved).**  Trivial cycle space ⟹ no more edges than vertices:
`Σᵢ|wᵢ| ≤ k + |union|`.  Pure cardinality: `∂` injective ⟹ `2^E ≤ 2^V`. -/
theorem edge_le_vert_of_trivial_ker (C : SharedCircuitForTarget k b)
    (hker : ∀ x : Cochain1 C, boundary C x = 0 → x = 0) :
    (edgeSet C).card ≤ k + (distinctWitnesses C).card := by
  have hinj := boundary_injective C hker
  have hcard : Fintype.card (Cochain1 C) ≤ Fintype.card (Cochain0 C) :=
    Fintype.card_le_of_injective _ hinj
  have h1 : Fintype.card (Cochain1 C) = 2 ^ (edgeSet C).card := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_coe]
  have h2 : Fintype.card (Cochain0 C) = 2 ^ (k + (distinctWitnesses C).card) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe]
  rw [h1, h2] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega)).mp hcard

/-- **Acyclicity kills sharing (proved).**  If the incidence geometry has trivial cycle space,
the disjoint bound holds up to the forest slack: `k·b ≤ |gates| + k`. -/
theorem acyclic_kills_sharing (C : SharedCircuitForTarget k b)
    (hker : ∀ x : Cochain1 C, boundary C x = 0 → x = 0) :
    k * b ≤ C.gates.card + k := by
  have h1 := kb_le_edgeCard C
  have h2 := edge_le_vert_of_trivial_ker C hker
  have h3 : (distinctWitnesses C).card ≤ C.gates.card :=
    Finset.card_le_card (distinctWitnesses_subset C)
  omega

/-- The same in the overlap language: trivial `H¹` ⟹ `overlap ≤ k`. -/
theorem acyclic_overlap_bound (C : SharedCircuitForTarget k b)
    (hker : ∀ x : Cochain1 C, boundary C x = 0 → x = 0) :
    overlap C ≤ k := by
  have h2 := edge_le_vert_of_trivial_ker C hker
  have hov : overlap C = (∑ i, (C.witness i).card) - (distinctWitnesses C).card := rfl
  have hE := edgeSet_card C
  omega

/-- **Sharing forces cycles (proved).**  Any circuit beating the disjoint bound by more than the
forest slack `k` contains a nonzero cycle: the adversary's savings LIVE in `H¹`. -/
theorem sharing_forces_cycles (C : SharedCircuitForTarget k b)
    (hbig : C.gates.card + k < k * b) :
    ∃ x : Cochain1 C, boundary C x = 0 ∧ x ≠ 0 := by
  by_contra hno
  have hker : ∀ x : Cochain1 C, boundary C x = 0 → x = 0 := by
    intro x hx
    by_contra hxne
    exact hno ⟨x, hx, hxne⟩
  exact absurd (acyclic_kills_sharing C hker) (by omega)

/-- The overlap reading: overlap beyond `k` is carried by nonzero cycles. -/
theorem overlap_forces_cycles (C : SharedCircuitForTarget k b)
    (hbig : k < overlap C) :
    ∃ x : Cochain1 C, boundary C x = 0 ∧ x ≠ 0 := by
  by_contra hno
  have hker : ∀ x : Cochain1 C, boundary C x = 0 → x = 0 := by
    intro x hx
    by_contra hxne
    exact hno ⟨x, hx, hxne⟩
  exact absurd (acyclic_overlap_bound C hker) (by omega)

/-- **Uhlig calibration (proved).**  The full-sharing collapse witness (`|gates| + k = 6 < 9 =
k·b`) provably contains nonzero cycles — obtained through the obstruction theorem itself. -/
theorem collapse_has_cycles :
    ∃ x : Cochain1 collapseWitness, boundary collapseWitness x = 0 ∧ x ≠ 0 :=
  sharing_forces_cycles collapseWitness (by decide)

end PallLean.Paper93.DeepMath.PathB.IncidenceCohomology

#print axioms PallLean.Paper93.DeepMath.PathB.IncidenceCohomology.boundary_add
#print axioms PallLean.Paper93.DeepMath.PathB.IncidenceCohomology.acyclic_kills_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.IncidenceCohomology.acyclic_overlap_bound
#print axioms PallLean.Paper93.DeepMath.PathB.IncidenceCohomology.sharing_forces_cycles
#print axioms PallLean.Paper93.DeepMath.PathB.IncidenceCohomology.overlap_forces_cycles
#print axioms PallLean.Paper93.DeepMath.PathB.IncidenceCohomology.collapse_has_cycles
