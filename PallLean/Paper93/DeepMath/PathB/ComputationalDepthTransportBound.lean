import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSelfRefBraid

/-!
# Trying to close the transport socket — how far it bounds, and where the wall sits

The `SelfRefBraid` composition left ONE open input: the transport socket

  `transport : NonLocalClass C → ¬ B.W.DTS B.p B.sparse`

— a non-local global-gate obstruction on the self-reference carrier `C` yields the braid's dent
(a uniform small-space lower bound on the sparse magnifiable target).  Here we push on it as hard
as the mathematics allows and report exactly which layers close and which one does not.

## The decomposition — three layers, two of them not the wall

The transport is NOT monolithic.  Reading right-to-left it factors as:

1. **Uniform → circuit (a literature socket, NOT `P≠NP`-strength).**  A language in `DTS[n^p]`
   (deterministic time `n^p`, small space) has circuits of size `≈ n^p·polylog`
   (time·space → circuit, Pippenger–Fischer / Borodin).  Named `SimInclusion`.  Contrapositively a
   circuit-size lower bound gives the uniform dent — the uniform layer STRIPS to a pure non-uniform
   circuit-size lower bound.  **`dent_of_sim_and_circuitLB` (AXIOM-FREE).**

2. **No-sharing → circuit size (PROVED — the ruler).**  `entangled_reason` (proved in
   `EntanglementRuler`) already gives `k·b ≤ σ·|gates|`: the private demand `k·b` forces circuit
   size `|gates| ≥ k·b/σ`.  So a size lower bound follows from (demand `k·b`) ∧ (localization `σ`) ∧
   (realizability: the tower's gates ARE a circuit for `sparse`).  **`circuitLB_of_ruler`** reuses the
   proved ruler; **`transport_bounded_by_pieces`** assembles layers 1–2; **`selfref_braid_fires_via_ruler`**
   cashes out through the proved `braid_fires`.

3. **The residue = the wall.**  What is left after stripping layers 1–2 is exactly two semantic
   claims about SAT's tower: **demand-generation** (`k·b` large — the sparse target induces private
   nonlinear demand `b ≥ n^ε`) and **localization** (`σ` small — minimal circuits are reach-local).
   Both are `cost_super` in the costumes the map already carries (`EntanglementRuler` /
   `LocalizationBound`).

## Can we close it?  No — and here is the machine-checked reason

`localization_implies_sharing_bound`: assuming the localization hypothesis `∀g, depCard g ≤ σ`
IS assuming a sharing bound `∀g, mult g ≤ σ` (because `mult ≤ depCard`, the proved ruler).  So
"close localization" ⟺ "bound multiplicity" ⟺ "forbid mass-production" = `cost_super`.  And
`collapse_to_floor` shows the honest degeneration: a gate that straddles all `k` blocks forces
`σ ≥ k` (`sharing_forces_localization_ge`), whereupon the ruler's demand condition `σ·s < k·b`
collapses to `s < b` — the circuit must be smaller than a single block's demand, i.e. the bound is
VACUOUS exactly in the Uhlig regime where sharing is real.

**Verdict.**  The transport is BOUNDED, not closed.  Its uniform layer is a literature simulation
(closable labor), its no-sharing→size layer is the PROVED ruler, and the irreducible residue is
`localization ∧ demand-generation = cost_super` — the same wall every route hits, now wearing the
magnification-transport costume.  The transport introduces NO new hardness beyond the wall; but it
does not remove it either.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TransportBound

open PallLean.Paper93.DeepMath.PathB.MagnificationBraid
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.AttackNoSharing
open PallLean.Paper93.DeepMath.PathB.EntanglementRuler
open PallLean.Paper93.DeepMath.PathB.TheReasonShared

/-! ### Layer 1 — the uniform → circuit crossing (literature socket), stripped -/

/-- **The time·space → circuit inclusion (named literature socket).**  A language decided in
`DTS[n^p]` has a circuit family of size `s ≈ n^p·polylog`.  NOT `P≠NP`-strength — a standard
simulation.  Parametrised over the ambient circuit-size notion `HasCircuitSize`. -/
def SimInclusion (HasCircuitSize : Lang → ℕ → Prop) (B : Braid) (s : ℕ) : Prop :=
  B.W.DTS B.p B.sparse → HasCircuitSize B.sparse s

/-- **The uniform layer strips (proved, AXIOM-FREE).**  Given the simulation socket and a pure
circuit-size lower bound on `sparse`, the braid's dent follows by contraposition — the uniform
machine layer is gone, replaced by a non-uniform circuit-size question. -/
theorem dent_of_sim_and_circuitLB (HasCircuitSize : Lang → ℕ → Prop) (B : Braid) (s : ℕ)
    (sim : SimInclusion HasCircuitSize B s)
    (circuitLB : ¬ HasCircuitSize B.sparse s) :
    ¬ B.W.DTS B.p B.sparse :=
  fun hdts => circuitLB (sim hdts)

/-! ### Layer 2 — the circuit-size lower bound from the PROVED ruler -/

/-- **The circuit-size lower bound, grounded in the proved ruler.**  Realizability (`hreal`: a
size-`s` circuit for `sparse` instantiates a tower with `≤ s` gates) + localization (`hloc`:
dependency count `≤ σ`) + demand (`hdemand`: `σ·s < k·b`) contradict `entangled_reason`
(`k·b ≤ σ·|gates|`).  So `sparse` has no size-`s` circuit. -/
theorem circuitLB_of_ruler (HasCircuitSize : Lang → ℕ → Prop) {k b n : ℕ}
    (B : Braid) (C : EntangledTower k b n) (σ s : ℕ)
    (hloc : ∀ g ∈ C.gates, (depSet C g).card ≤ σ)
    (hdemand : σ * s < k * b)
    (hreal : HasCircuitSize B.sparse s → C.gates.card ≤ s) :
    ¬ HasCircuitSize B.sparse s := by
  intro hsize
  have hg : C.gates.card ≤ s := hreal hsize
  have hr : k * b ≤ σ * C.gates.card := entangled_reason C σ hloc
  have hσ : σ * C.gates.card ≤ σ * s := Nat.mul_le_mul (le_refl σ) hg
  exact absurd (le_trans hr hσ) (Nat.not_le.mpr hdemand)

/-- **The transport, bounded by its layers (proved).**  Assemble layer 1 (simulation) and layer 2
(ruler): the dent follows from the simulation socket + realizability + localization + demand. -/
theorem transport_bounded_by_pieces (HasCircuitSize : Lang → ℕ → Prop) {k b n : ℕ}
    (B : Braid) (C : EntangledTower k b n) (σ s : ℕ)
    (sim : SimInclusion HasCircuitSize B s)
    (hloc : ∀ g ∈ C.gates, (depSet C g).card ≤ σ)
    (hdemand : σ * s < k * b)
    (hreal : HasCircuitSize B.sparse s → C.gates.card ≤ s) :
    ¬ B.W.DTS B.p B.sparse :=
  dent_of_sim_and_circuitLB HasCircuitSize B s sim
    (circuitLB_of_ruler HasCircuitSize B C σ s hloc hdemand hreal)

/-- **The braid fires through the bounded transport (proved glue).**  Composes the assembly with
the proved `braid_fires`.  The open inputs are exactly the residue of layers 1–2. -/
theorem selfref_braid_fires_via_ruler (HasCircuitSize : Lang → ℕ → Prop) {k b n : ℕ}
    (B : Braid) (C : EntangledTower k b n) (σ s : ℕ)
    (sim : SimInclusion HasCircuitSize B s)
    (hloc : ∀ g ∈ C.gates, (depSet C g).card ≤ σ)
    (hdemand : σ * s < k * b)
    (hreal : HasCircuitSize B.sparse s → C.gates.card ≤ s) :
    SAT_not_in_P :=
  braid_fires B (transport_bounded_by_pieces HasCircuitSize B C σ s sim hloc hdemand hreal)

/-! ### Layer 3 — why the residue is the wall (the non-closure) -/

/-- **Localization IS a sharing bound (proved).**  Assuming reach `≤ σ` on every gate implies
multiplicity `≤ σ` on every gate — because `mult ≤ depCard` (the proved ruler `mult_le_depCard`).
So "close localization" is definitionally "bound sharing multiplicity" = forbid mass-production =
`cost_super`.  The residue cannot be closed without the wall. -/
theorem localization_implies_sharing_bound {k b n : ℕ} (C : EntangledTower k b n) (σ : ℕ)
    (hloc : ∀ g ∈ C.gates, (depSet C g).card ≤ σ) :
    ∀ g ∈ C.gates, mult (toShared C) g ≤ σ :=
  fun g hg => le_trans (mult_le_depCard C g) (hloc g hg)

/-- **A global gate forces the localization parameter up (proved).**  A gate whose multiplicity is
`≥ k` (it serves all blocks) forces `σ ≥ k`. -/
theorem sharing_forces_localization_ge {k b n : ℕ} (C : EntangledTower k b n) (σ g : ℕ)
    (hg : g ∈ C.gates) (hshare : k ≤ mult (toShared C) g)
    (hloc : ∀ g ∈ C.gates, (depSet C g).card ≤ σ) : k ≤ σ :=
  le_trans hshare (localization_implies_sharing_bound C σ hloc g hg)

/-- **The honest degeneration (proved).**  If a gate straddles all `k` blocks (`hshare`), then
`σ ≥ k`, and the ruler's demand condition `σ·s < k·b` collapses to `s < b`: the circuit must be
smaller than a single block's demand.  The lower bound is VACUOUS exactly in the Uhlig regime where
sharing is real — the theorem reproduces its own counterexample, the honest tell that the residue is
`cost_super`. -/
theorem collapse_to_floor {k b n : ℕ} (C : EntangledTower k b n) (σ s g : ℕ)
    (hg : g ∈ C.gates) (hshare : k ≤ mult (toShared C) g)
    (hloc : ∀ g ∈ C.gates, (depSet C g).card ≤ σ)
    (hdemand : σ * s < k * b) : s < b := by
  have hkσ : k ≤ σ := sharing_forces_localization_ge C σ g hg hshare hloc
  by_contra hsb
  have hbs : b ≤ s := Nat.not_lt.mp hsb
  have h1 : k * b ≤ k * s := Nat.mul_le_mul (le_refl k) hbs
  have h2 : k * s ≤ σ * s := Nat.mul_le_mul hkσ (le_refl s)
  have h3 : k * b ≤ σ * s := le_trans h1 h2
  omega

end PallLean.Paper93.DeepMath.PathB.TransportBound

#print axioms PallLean.Paper93.DeepMath.PathB.TransportBound.dent_of_sim_and_circuitLB
#print axioms PallLean.Paper93.DeepMath.PathB.TransportBound.circuitLB_of_ruler
#print axioms PallLean.Paper93.DeepMath.PathB.TransportBound.transport_bounded_by_pieces
#print axioms PallLean.Paper93.DeepMath.PathB.TransportBound.selfref_braid_fires_via_ruler
#print axioms PallLean.Paper93.DeepMath.PathB.TransportBound.localization_implies_sharing_bound
#print axioms PallLean.Paper93.DeepMath.PathB.TransportBound.collapse_to_floor
