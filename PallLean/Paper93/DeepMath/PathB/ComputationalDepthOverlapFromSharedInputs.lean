import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheReasonShared

/-!
# Bounding overlap from the tower's shared inputs — the first semantic bound

`TheReasonShared` left ONE scalar between the reason-for-all and the truth: `overlap C`, the
double-counted witness mass, controlled by the adversary.  This file bounds it — not by assuming a
multiplicity cap, but by DERIVING one from two structural quantities of the tower and the circuit:

* `t` — the **input-sharing profile** of the tower layout: each variable belongs to at most `t`
  blocks (`var_shared`).  This is where "the tower's shared inputs" enters as mathematics.
* `s` — the **support locality** of the circuit: each gate reads at most `s` variables
  (`sup_bound`), and a witness for block `i` must actually touch block `i`'s variables
  (`wit_touches` — the semantic content of "witness").

Then a gate can witness at most `s·t` blocks (`mult_le_geometry`: its `≤ s` variables each lie in
`≤ t` blocks), and the machinery of `TheReasonShared` fires with `r = s·t` DERIVED:

* **`overlap_le_of_mult_le`** — generic: multiplicity `≤ r` everywhere ⟹
  `overlap ≤ (r−1)·|gates|`.
* **`overlap_le_shared_inputs`** — THE requested bound: `overlap ≤ (s·t − 1)·|gates|`.
  Overlap is no longer a free adversary knob; it is priced by locality × sharing profile.
* **`the_reason_from_shared_inputs`** — the cash-out: `k·b ≤ s·t·|gates|`, i.e.
  `|gates| ≥ k·b/(s·t)` for every support-local circuit over the layout.
* **`graded_from_shared_inputs`** — the handoff form: `s·t·D ≤ k ⟹ D·b ≤ |gates|`.
* **`privateExample`** — non-vacuous, tight at `s = t = 1`.

## Honest scope — exactly where the wall now stands

The bound has teeth iff `s·t ≪ k`, and BOTH factors are honest open fronts:

1. **`t` (the tower's side).**  A fresh-variable / padded composition tower keeps `t` small
   (a variable belongs to its own block and the few levels above it).  But the doubling tower
   with fully shared base inputs has `t ≈ k` at depth — and there the bound degenerates to the
   floor, exactly as it must: Uhlig's mass production really does achieve near-total overlap for
   repeated instances on shared inputs.  The theorem is calibrated, not evaded.
2. **`s` (the circuit's side).**  The adversary's gates need not be support-local (`s` can be
   `n`).  The missing theorem is that minimal circuits ADMIT support-local witnesses — that
   witness mass can be pushed toward the inputs.  That localization claim is open, and it is the
   precise residue of `cost_super` in this frame:
   `cost_super ⟸ (witness localization) + (layout with s·t ≪ k)`.

So: overlap is now bounded BY the shared-input geometry, in the support-local regime; what
remains open is not the counting but the localization.  As before, per-block witness demand
(`wit_size`) is a structure field; the proved content is the geometry-to-multiplicity-to-overlap
pipeline.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.OverlapFromSharedInputs

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.TheReasonShared

/-- A circuit over a **tower layout**: blocks own variable sets (possibly overlapping — the
shared inputs), gates have variable supports, and witnessing is semantic — a witness for block
`i` must touch block `i`'s variables.  `s` bounds gate support, `t` bounds how many blocks share
one variable. -/
structure TowerCircuit (k b n s t : ℕ) where
  /-- the gates of the circuit -/
  gates : Finset ℕ
  /-- block `i`'s witness gates -/
  witness : Fin k → Finset ℕ
  /-- witnesses are real gates -/
  wit_sub : ∀ i, witness i ⊆ gates
  /-- each block needs at least `b` witness gates -/
  wit_size : ∀ i, b ≤ (witness i).card
  /-- block `i`'s input variables (blocks may SHARE variables) -/
  blockVars : Fin k → Finset (Fin n)
  /-- gate `g`'s variable support (its input cone) -/
  support : ℕ → Finset (Fin n)
  /-- support locality: every gate reads at most `s` variables -/
  sup_bound : ∀ g ∈ gates, (support g).card ≤ s
  /-- the sharing profile: every variable belongs to at most `t` blocks -/
  var_shared : ∀ v : Fin n,
    ((Finset.univ : Finset (Fin k)).filter (fun i => v ∈ blockVars i)).card ≤ t
  /-- semantic witnessing: a witness for block `i` touches block `i`'s variables -/
  wit_touches : ∀ i, ∀ g ∈ witness i, ((support g) ∩ blockVars i).Nonempty

/-- Forget the geometry: the underlying shared-witness circuit. -/
def toShared {k b n s t : ℕ} (C : TowerCircuit k b n s t) : SharedCircuitForTarget k b :=
  ⟨C.gates, C.witness, C.wit_sub, C.wit_size⟩

/-- **Geometry prices multiplicity (proved).**  A gate with `≤ s` support variables, each shared
by `≤ t` blocks, witnesses at most `s·t` blocks.  The multiplicity cap is DERIVED from the
layout, not assumed. -/
theorem mult_le_geometry {k b n s t : ℕ} (C : TowerCircuit k b n s t) (g : ℕ)
    (hg : g ∈ C.gates) : mult (toShared C) g ≤ s * t := by
  have h0 : mult (toShared C) g
      = ((Finset.univ : Finset (Fin k)).filter (fun i => g ∈ (toShared C).witness i)).card := rfl
  have hsub1 : (Finset.univ : Finset (Fin k)).filter (fun i => g ∈ (toShared C).witness i)
      ⊆ Finset.univ.filter (fun i => ((C.support g) ∩ C.blockVars i).Nonempty) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, C.wit_touches i g hi.2⟩
  have hsub2 : Finset.univ.filter (fun i : Fin k => ((C.support g) ∩ C.blockVars i).Nonempty)
      ⊆ (C.support g).biUnion
        (fun v => Finset.univ.filter (fun i => v ∈ C.blockVars i)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨v, hv⟩ := hi.2
    rw [Finset.mem_inter] at hv
    rw [Finset.mem_biUnion]
    exact ⟨v, hv.1, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ i, hv.2⟩⟩
  have h1 : mult (toShared C) g
      ≤ ((C.support g).biUnion
          (fun v => Finset.univ.filter (fun i => v ∈ C.blockVars i))).card := by
    rw [h0]
    exact Finset.card_le_card (Finset.Subset.trans hsub1 hsub2)
  have h2 : ((C.support g).biUnion
        (fun v => Finset.univ.filter (fun i => v ∈ C.blockVars i))).card
      ≤ ∑ v ∈ C.support g,
          (Finset.univ.filter (fun i : Fin k => v ∈ C.blockVars i)).card :=
    Finset.card_biUnion_le
  have h3 : (∑ v ∈ C.support g,
        (Finset.univ.filter (fun i : Fin k => v ∈ C.blockVars i)).card)
      ≤ ∑ _v ∈ C.support g, t :=
    Finset.sum_le_sum (fun v _ => C.var_shared v)
  have h4 : (∑ _v ∈ C.support g, t) = (C.support g).card * t := by
    rw [Finset.sum_const]
    simp
  have h5 : (C.support g).card * t ≤ s * t :=
    Nat.mul_le_mul_right t (C.sup_bound g hg)
  omega

/-- **Overlap is priced by multiplicity (proved, generic).**  If every gate witnesses at most `r`
blocks, the double-counting cannot exceed `(r−1)` per gate: `overlap ≤ (r−1)·|gates|`. -/
theorem overlap_le_of_mult_le {k b : ℕ} (C : SharedCircuitForTarget k b) (r : ℕ)
    (hr : ∀ g ∈ C.gates, mult C g ≤ r) :
    overlap C ≤ (r - 1) * C.gates.card := by
  have hUsub : distinctWitnesses C ⊆ C.gates := distinctWitnesses_subset C
  have hzero : ∀ g ∈ C.gates, g ∉ distinctWitnesses C → mult C g = 0 := by
    intro g _ hgU
    rw [mult, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hgi
    exact hgU (by rw [distinctWitnesses, Finset.mem_biUnion]
                  exact ⟨i, Finset.mem_univ i, hgi⟩)
  have hsum : ∑ g ∈ distinctWitnesses C, mult C g = ∑ g ∈ C.gates, mult C g :=
    Finset.sum_subset hUsub hzero
  have hbound : ∑ g ∈ distinctWitnesses C, mult C g ≤ (distinctWitnesses C).card • r :=
    Finset.sum_le_card_nsmul _ _ _ (fun g hgU => hr g (hUsub hgU))
  have hsmul : (distinctWitnesses C).card • r = (distinctWitnesses C).card * r := by simp
  have hover : overlap C = (∑ g ∈ C.gates, mult C g) - (distinctWitnesses C).card := by
    rw [overlap, incidence_count]
  have hUcard : (distinctWitnesses C).card ≤ C.gates.card := Finset.card_le_card hUsub
  have h1 : (∑ g ∈ distinctWitnesses C, mult C g) - (distinctWitnesses C).card
      ≤ (distinctWitnesses C).card * r - (distinctWitnesses C).card :=
    Nat.sub_le_sub_right (le_of_le_of_eq hbound hsmul) _
  have h2 : (distinctWitnesses C).card * r - (distinctWitnesses C).card
      = (r - 1) * (distinctWitnesses C).card := by
    rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
  have h3 : (r - 1) * (distinctWitnesses C).card ≤ (r - 1) * C.gates.card :=
    Nat.mul_le_mul_left (r - 1) hUcard
  omega

/-- **THE BOUND (proved): overlap from the tower's shared inputs.**
`overlap ≤ (s·t − 1)·|gates|` — the adversary's double-counting is capped by support locality
times the input-sharing profile.  Overlap is no longer a free knob: it is a priced consequence
of how many variables a gate reads and how many blocks share a variable. -/
theorem overlap_le_shared_inputs {k b n s t : ℕ} (C : TowerCircuit k b n s t) :
    overlap (toShared C) ≤ (s * t - 1) * C.gates.card :=
  overlap_le_of_mult_le (toShared C) (s * t) (fun g hg => mult_le_geometry C g hg)

/-- **The cash-out (proved).**  For every support-local circuit over the layout:
`k·b ≤ s·t·|gates|` — the reason-for-all with its overlap term discharged by geometry. -/
theorem the_reason_from_shared_inputs {k b n s t : ℕ} (C : TowerCircuit k b n s t) :
    k * b ≤ (s * t) * C.gates.card :=
  the_reason_shared (toShared C) (s * t) (fun g hg => mult_le_geometry C g hg)

/-- **The handoff form (proved).**  Locality×sharing a `D`-fold factor below the block count
leaves a `D`-fold bound — the magnifiable residue survives whenever `s·t ≪ k`. -/
theorem graded_from_shared_inputs {k b n s t D : ℕ} (C : TowerCircuit k b n s t)
    (hst : 1 ≤ s * t) (hgap : s * t * D ≤ k) : D * b ≤ C.gates.card :=
  graded_survivor (toShared C) (s * t) D hst (fun g hg => mult_le_geometry C g hg) hgap

/-- **Non-vacuous and tight.**  Two blocks on private variables (`t = 1`), single-variable gates
(`s = 1`): the bound gives `2·1 ≤ 1·1·2` — equality. -/
def privateExample : TowerCircuit 2 1 2 1 1 where
  gates := {0, 1}
  witness := fun i => {i.val}
  wit_sub := by decide
  wit_size := by decide
  blockVars := fun i => {i}
  support := fun g => if g = 0 then {0} else {1}
  sup_bound := by decide
  var_shared := by decide
  wit_touches := by decide

theorem privateExample_tight : 2 * 1 ≤ 1 * 1 * privateExample.gates.card :=
  the_reason_from_shared_inputs privateExample

end PallLean.Paper93.DeepMath.PathB.OverlapFromSharedInputs

#print axioms PallLean.Paper93.DeepMath.PathB.OverlapFromSharedInputs.mult_le_geometry
#print axioms PallLean.Paper93.DeepMath.PathB.OverlapFromSharedInputs.overlap_le_of_mult_le
#print axioms PallLean.Paper93.DeepMath.PathB.OverlapFromSharedInputs.overlap_le_shared_inputs
#print axioms PallLean.Paper93.DeepMath.PathB.OverlapFromSharedInputs.the_reason_from_shared_inputs
#print axioms PallLean.Paper93.DeepMath.PathB.OverlapFromSharedInputs.graded_from_shared_inputs
#print axioms PallLean.Paper93.DeepMath.PathB.OverlapFromSharedInputs.privateExample_tight
