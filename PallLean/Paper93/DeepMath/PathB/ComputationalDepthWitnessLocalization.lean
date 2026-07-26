import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAffineSemantics
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheReasonShared

/-!
# Witness localization, the affine half: deep global gates are no refuge without nonlinearity

`OverlapFromSharedInputs` left ONE open move: localization — why can't the adversary keep all its
witness mass in deep, global gates?  This file proves the half of that question that is provable
today, and names the half that is the wall.

## The provable half: affine gates carry ZERO witness mass — at any depth

Make witnessing semantic: block `i` has a variable mask, gate `g` computes a wire function, and a
witness for block `i` must be **nonlinear on block `i`** — some fixing of the outside variables
leaves a non-affine function of the block's variables (`NonlinearOnBlock`).  This is the honest
reading of "does that block's work": an affine dependence is free (XOR gadgets), only nonlinear
dependence is work (`HornCollapse`: SAT-like targets are nonlinear).

The key lemma is `isAffineFn_restrict`: **restrictions of affine functions are affine** — gluing a
constant outside the block preserves the 3-fold difference identity, because a 3-fold XOR of a
constant is the constant.  Consequently (`affine_no_block_nonlinearity`) an affine wire is
nonlinear on NO block, hence witnesses nothing — regardless of its depth, fan-in, or how many
blocks its cone touches.  Globality does not help an affine gate.

* **`witness_mass_localizes`** — every gate carrying witness mass has a non-affine wire function.
* **`skeleton`** — the nonlinear sub-circuit; `union_subset_skeleton`: ALL witness mass lives on it.
* **`floor_localizes`** — `b ≤ |skeleton|`: the floor bound transfers from all gates to the
  nonlinear skeleton.
* **`localized_reason`** — the reason-for-all, sharpened: `k·b ≤ |skeleton| + overlap`.  Affine
  gates are FREE for the adversary but USELESS: they neither absorb witness demand nor appear on
  the cost side.  The adversary's whole game is squeezed onto its nonlinear skeleton.
* **`affine_adversary_impossible`** — the fully-affine deep-global adversary is dead: any valid
  semantic tower contains a non-affine gate.  (The Valiant-horn localization, matching
  `HornCollapse`: the linear horn contributes nothing.)
* **`and_nonlinearOnBlock` / `andExample`** — the semantic demand is non-vacuous.

## Honest scope: the remaining half, named

What survives for the adversary is the NONLINEAR global gate: this file relocates localization
from "all gates" to "count the nonlinear skeleton".  The repository's degree machinery
(`WireDegreeBound`, `AndPeeling`) bounds that skeleton — but only LOGARITHMICALLY, and the degree
method is provably capped there.  A superpolynomial skeleton bound for the tower IS `cost_super`.
So the deep-global refuge is now half-closed: closed for affine gates (proved here,
unconditionally), open for nonlinear ones — and the open half is exactly the wall, in its
sharpest form yet: `cost_super ⟸ superpolynomial nonlinear-skeleton bound + overlap control
(OverlapFromSharedInputs)`.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.WitnessLocalization

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.AffineSemantics
open PallLean.Paper93.DeepMath.PathB.TheReasonShared

variable {n : ℕ}

/-- Glue a block assignment `u` (on the mask) with a fixed outside assignment `ρ`. -/
def glue (blk ρ u : Fin n → Bool) : Fin n → Bool :=
  fun v => if blk v then u v else ρ v

/-- The 3-fold pointwise XOR passes through gluing: on the block it is the XOR of the block
assignments; outside, the 3-fold XOR of the constant `ρ` is `ρ`. -/
theorem glue_xor3 (blk ρ x y z : Fin n → Bool) :
    (fun i => Bool.xor (Bool.xor (glue blk ρ x i) (glue blk ρ y i)) (glue blk ρ z i))
      = glue blk ρ (fun i => Bool.xor (Bool.xor (x i) (y i)) (z i)) := by
  funext v
  simp only [glue]
  cases blk v <;> cases x v <;> cases y v <;> cases z v <;> cases ρ v <;> rfl

/-- **Restrictions of affine functions are affine (proved).**  Fixing the variables outside a
block preserves affineness — the core of the localization. -/
theorem isAffineFn_restrict {F : (Fin n → Bool) → Bool} (hF : IsAffineFn F)
    (blk ρ : Fin n → Bool) : IsAffineFn (fun u => F (glue blk ρ u)) := by
  intro x y z
  dsimp only
  rw [hF (glue blk ρ x) (glue blk ρ y) (glue blk ρ z), glue_xor3]

/-- `F` is **nonlinear on the block** `blk`: some fixing of the outside variables leaves a
non-affine function of the block assignment.  The semantic content of "witnessing a nonlinear
block demand". -/
def NonlinearOnBlock (blk : Fin n → Bool) (F : (Fin n → Bool) → Bool) : Prop :=
  ∃ ρ : Fin n → Bool, ¬ IsAffineFn (fun u => F (glue blk ρ u))

/-- **Affine wires witness nothing (proved).**  An affine function is nonlinear on NO block —
regardless of depth, fan-in, or how many blocks its cone touches. -/
theorem affine_no_block_nonlinearity {F : (Fin n → Bool) → Bool} (hF : IsAffineFn F)
    (blk : Fin n → Bool) : ¬ NonlinearOnBlock blk F :=
  fun ⟨ρ, hρ⟩ => hρ (isAffineFn_restrict hF blk ρ)

/-- The demand is non-vacuous: 2-bit AND is nonlinear on the full block. -/
theorem and_nonlinearOnBlock :
    NonlinearOnBlock (fun _ : Fin 2 => true) (fun x => Bool.and (x 0) (x 1)) := by
  unfold NonlinearOnBlock IsAffineFn glue
  decide

/-- A **semantic tower**: gates compute wire functions, blocks have variable masks, and a witness
for block `i` must be nonlinear on block `i`.  Witness demand is no longer a bare cardinality
field about abstract sets of gate NAMES — membership in a witness set forces a SEMANTIC property
of the gate's wire function. -/
structure SemanticTower (k b n : ℕ) where
  /-- the gates of the circuit -/
  gates : Finset ℕ
  /-- the wire function each gate computes -/
  wireFn : ℕ → (Fin n → Bool) → Bool
  /-- block `i`'s variable mask -/
  blockMask : Fin k → Fin n → Bool
  /-- block `i`'s witness gates -/
  witness : Fin k → Finset ℕ
  /-- witnesses are real gates -/
  wit_sub : ∀ i, witness i ⊆ gates
  /-- each block needs at least `b` witness gates -/
  wit_size : ∀ i, b ≤ (witness i).card
  /-- SEMANTIC witnessing: a witness for block `i` is nonlinear on block `i` -/
  wit_semantic : ∀ i, ∀ g ∈ witness i, NonlinearOnBlock (blockMask i) (wireFn g)

/-- Forget the semantics: the underlying shared-witness circuit. -/
def toShared {k b n : ℕ} (C : SemanticTower k b n) : SharedCircuitForTarget k b :=
  ⟨C.gates, C.witness, C.wit_sub, C.wit_size⟩

/-- **Witness mass localizes (proved).**  Every gate carrying witness mass has a non-affine wire
function.  Depth and globality are no refuge: an affine gate — however deep, however global —
carries none. -/
theorem witness_mass_localizes {k b n : ℕ} (C : SemanticTower k b n) (g : ℕ)
    (hg : g ∈ distinctWitnesses (toShared C)) : ¬ IsAffineFn (C.wireFn g) := by
  rw [distinctWitnesses, Finset.mem_biUnion] at hg
  obtain ⟨i, _, hgi⟩ := hg
  intro hAff
  exact affine_no_block_nonlinearity hAff (C.blockMask i) (C.wit_semantic i g hgi)

/-- Affineness over a finite input space is decidable — the skeleton is a genuine `Finset`, not a
classical shadow. -/
instance (F : (Fin n → Bool) → Bool) : Decidable (IsAffineFn F) := by
  unfold IsAffineFn
  infer_instance

/-- The **nonlinear skeleton**: the gates whose wire functions are non-affine. -/
def skeleton {k b n : ℕ} (C : SemanticTower k b n) : Finset ℕ :=
  C.gates.filter (fun g => ¬ IsAffineFn (C.wireFn g))

/-- ALL witness mass lives on the nonlinear skeleton. -/
theorem union_subset_skeleton {k b n : ℕ} (C : SemanticTower k b n) :
    distinctWitnesses (toShared C) ⊆ skeleton C := by
  intro g hg
  rw [skeleton, Finset.mem_filter]
  exact ⟨distinctWitnesses_subset (toShared C) hg, witness_mass_localizes C g hg⟩

/-- **The floor localizes (proved).**  `b ≤ |skeleton|`: already one block's demand must be met
by nonlinear gates alone. -/
theorem floor_localizes {k b n : ℕ} (C : SemanticTower k b n) (hk : 1 ≤ k) :
    b ≤ (skeleton C).card := by
  have h1 : C.witness ⟨0, hk⟩ ⊆ distinctWitnesses (toShared C) := by
    intro g hg
    rw [distinctWitnesses, Finset.mem_biUnion]
    exact ⟨⟨0, hk⟩, Finset.mem_univ _, hg⟩
  exact le_trans (C.wit_size ⟨0, hk⟩)
    (Finset.card_le_card (Finset.Subset.trans h1 (union_subset_skeleton C)))

/-- **The localized reason-for-all (proved).**  `k·b ≤ |skeleton| + overlap`: the reason-for-all
with its cost side shrunk from all gates to the nonlinear skeleton.  Affine gates are free but
useless — they neither absorb witness demand nor count toward the bound. -/
theorem localized_reason {k b n : ℕ} (C : SemanticTower k b n) :
    k * b ≤ (skeleton C).card + overlap (toShared C) := by
  have h1 : k * b ≤ ∑ i, ((toShared C).witness i).card := kb_le_witness_sum (toShared C)
  have h2 : (distinctWitnesses (toShared C)).card + overlap (toShared C)
      = ∑ i, ((toShared C).witness i).card := union_card_add_overlap (toShared C)
  have h3 : (distinctWitnesses (toShared C)).card ≤ (skeleton C).card :=
    Finset.card_le_card (union_subset_skeleton C)
  omega

/-- **The fully-affine adversary is dead (proved).**  Any valid semantic tower contains a
non-affine gate: no purely affine circuit — of ANY depth or topology — meets even one nonlinear
block demand.  (The Valiant-horn half of localization, matching `HornCollapse`.) -/
theorem affine_adversary_impossible {k b n : ℕ} (C : SemanticTower k b n)
    (hk : 1 ≤ k) (hb : 1 ≤ b) :
    ∃ g ∈ C.gates, ¬ IsAffineFn (C.wireFn g) := by
  have h := floor_localizes C hk
  have hne : (skeleton C).Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hb h)
  obtain ⟨g, hg⟩ := hne
  rw [skeleton, Finset.mem_filter] at hg
  exact ⟨g, hg.1, hg.2⟩

/-- Non-vacuous: one block, one AND gate — a valid semantic tower. -/
def andExample : SemanticTower 1 1 2 where
  gates := {0}
  wireFn := fun _ => fun x => Bool.and (x 0) (x 1)
  blockMask := fun _ => fun _ => true
  witness := fun _ => {0}
  wit_sub := fun _ => Finset.Subset.refl _
  wit_size := fun _ => by decide
  wit_semantic := fun _ _ _ => and_nonlinearOnBlock

end PallLean.Paper93.DeepMath.PathB.WitnessLocalization

#print axioms PallLean.Paper93.DeepMath.PathB.WitnessLocalization.isAffineFn_restrict
#print axioms PallLean.Paper93.DeepMath.PathB.WitnessLocalization.witness_mass_localizes
#print axioms PallLean.Paper93.DeepMath.PathB.WitnessLocalization.floor_localizes
#print axioms PallLean.Paper93.DeepMath.PathB.WitnessLocalization.localized_reason
#print axioms PallLean.Paper93.DeepMath.PathB.WitnessLocalization.affine_adversary_impossible
