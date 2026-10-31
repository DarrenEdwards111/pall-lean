import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMixtureAdversary

/-!
# Family independence: the demand that kills the mixture — and the mixture that kills it back

`MixtureAdversary` proved per-gate demands are capped at the floor `b`.  The residue was named:
demand generation must be a FAMILY property.  This file builds the natural first family demand,
proves it has real teeth, and then — honestly — proves it is not enough either.  Both directions
are machine-checked; the arms race is now a pair of theorems, not a suspicion.

## The demand

**`PairwiseIndep`** — no two witnesses of a block may be affinely equivalent on that block: for
distinct `g, g'` in block `i`'s witness set, their pointwise XOR must itself be nonlinear on
block `i`'s private territory.  (If two witnesses differ by an affine map of the block, one of
them is redundant witness mass.)

## Round 1 — the demand has teeth

**`mixTower_not_pairwiseIndep`** — the ⊕-mixture adversary FAILS the demand (`b ≥ 2`): all its
gates carry the SAME wire function, so every pairwise difference is constantly `false` — affine
on every block, under every outside-fixing.  The family demand rules out yesterday's adversary.

## Round 2 — the escalated mixture kills the demand

**`richTower`** — give each block a territory of 4 variables and use per-SLOT gadgets:
`G_o = ⊕ᵢ (x_{4i+2o} ∧ x_{4i+2o+1})` for slots `o ∈ {0,1}`.  Restricted to block `i`, gate
`G_o` becomes slot-`o`'s AND — so the two gates are witnesses for EVERY block, and their
difference restricts to `AND ⊕ AND` on four distinct variables — nonlinear
(`and_xor_and_not_affine`).  `richTower_pairwiseIndep`: the escalated adversary PASSES the
family demand with `|gates| = b = 2`, for every `k`.

* **`pairwise_indep_ceiling`** — the pin, again one level up: any bound valid for all
  pairwise-independent towers (at this layout) is `≤ 2`.  Family independence WITHIN a block
  cannot reach the `k`-multiplier either.
* **`family_k_multiplier_unreachable`** — pointed: `k·b` fails on a valid pairwise-independent
  tower for every `k ≥ 2`.

## Honest reading — the general principle, and where the demand must go next

The escalation generalizes: the ⊕-mixture is a UNIVERSAL RESTRICTION-REALIZER.  For any
prescribed family of per-block restriction behaviours `h_{i,j}`, the gates
`G_j = ⊕ᵢ h_{i,j}(x|_{block i})` realize all of them simultaneously (up to affine constants) —
fixing outside block `i` strips every other summand to a constant.  So ANY demand expressible
as "the witnesses' restrictions to each block, separately, satisfy P" — however collective
within the block — is satisfiable by `b` gates whenever it is satisfiable at all.  Per-block
demands (per-gate OR family) are structurally capped at the floor.

The residue is therefore relocated once more, and more sharply: a demand that generates the
`k`-multiplier must COUPLE blocks — it must constrain how one physical gate's restrictions to
DIFFERENT blocks co-vary (exactly what the ⊕-realizer exploits: its gates' restrictions are
maximally correlated across blocks).  That cross-block coupling demand is the remaining shape
of demand generation; note honestly that constraining cross-restriction correlation of the
minimal circuit's wires is precisely where naturality pressure returns, and nothing here
discharges it.  (`richTower` is stated at `b = 2` — general `b` is routine but index-heavy;
`b = 2` already breaks any coupling of the demand to `k`.)  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.FamilyIndependence

open PallLean.Paper93.DeepMath.PathB.AffineSemantics
open PallLean.Paper93.DeepMath.PathB.WitnessLocalization
open PallLean.Paper93.DeepMath.PathB.EntanglementRuler
open PallLean.Paper93.DeepMath.PathB.MixtureAdversary

/-- **The family demand.**  No two witnesses of a block are affinely equivalent on it: distinct
witnesses' pointwise XOR is itself nonlinear on the block's private territory. -/
def PairwiseIndep {k b n : ℕ} (C : EntangledTower k b n) : Prop :=
  ∀ i : Fin k, ∀ g ∈ C.witness i, ∀ g' ∈ C.witness i, g ≠ g' →
    NonlinearOnBlock (C.privMask i)
      (fun x => Bool.xor (C.wireFn g x) (C.wireFn g' x))

/-! ### Round 1: the demand kills the ⊕-mixture -/

/-- **Teeth (proved).**  The ⊕-mixture adversary fails the family demand: all its gates compute
the same wire, so every pairwise difference is constantly `false` — affine everywhere. -/
theorem mixTower_not_pairwiseIndep (k b : ℕ) (hk : 1 ≤ k) (hb : 2 ≤ b) :
    ¬ PairwiseIndep (mixTower k b) := by
  intro h
  have h01 := h ⟨0, hk⟩ 0
    (show (0 : ℕ) ∈ Finset.range b from Finset.mem_range.mpr (by omega)) 1
    (show (1 : ℕ) ∈ Finset.range b from Finset.mem_range.mpr (by omega)) (by omega)
  obtain ⟨ρ, hρ⟩ := h01
  apply hρ
  have hzero : (fun u => (fun x => Bool.xor ((mixTower k b).wireFn 0 x)
        ((mixTower k b).wireFn 1 x)) (glue ((mixTower k b).privMask ⟨0, hk⟩) ρ u))
      = (fun _ => false) :=
    funext (fun u => Bool.xor_self _)
  rw [hzero]
  exact isAffineFn_const false

/-! ### Round 2: the escalated mixture — per-slot gadgets -/

variable {k : ℕ}

/-- The first variable of block `i`'s slot-`o` gadget. -/
def pos0 (i : Fin k) (o : Fin 2) : Fin (4 * k) :=
  ⟨4 * i.val + 2 * o.val, by have := i.isLt; have := o.isLt; omega⟩

/-- The second variable of block `i`'s slot-`o` gadget. -/
def pos1 (i : Fin k) (o : Fin 2) : Fin (4 * k) :=
  ⟨4 * i.val + 2 * o.val + 1, by have := i.isLt; have := o.isLt; omega⟩

/-- Block `i`'s private territory: the four variables `{4i, …, 4i+3}`. -/
def richMask (i : Fin k) : Fin (4 * k) → Bool := fun v => decide (v.val / 4 = i.val)

/-- Slot-`o`'s AND in block `j`. -/
def richPairAnd (o : Fin 2) (w : Fin (4 * k) → Bool) (j : Fin k) : Bool :=
  Bool.and (w (pos0 j o)) (w (pos1 j o))

/-- The slot-`o` mixture: `⊕ⱼ (x_{4j+2o} ∧ x_{4j+2o+1})`. -/
def richFn (o : Fin 2) (w : Fin (4 * k) → Bool) : Bool :=
  ((List.finRange k).map (richPairAnd o w)).foldr Bool.xor false

/-- Restriction evaluation: gluing `false` outside block `i` strips every other summand — the
slot-`o` mixture restricts to block `i`'s slot-`o` AND. -/
theorem rich_restrict (o : Fin 2) (i : Fin k) (u : Fin (4 * k) → Bool) :
    richFn o (glue (richMask i) (fun _ => false) u)
      = Bool.and (u (pos0 i o)) (u (pos1 i o)) := by
  show ((List.finRange k).map (richPairAnd o (glue (richMask i) (fun _ => false) u))).foldr
      Bool.xor false = _
  apply foldr_xor_eq_single i _ _ ?hoff ?hon (List.finRange k)
    (List.nodup_finRange k) (List.mem_finRange i)
  case hoff =>
    intro j hji
    have h0 : richMask i (pos0 j o) = false := by
      apply decide_eq_false
      intro hc
      have hc' : (4 * j.val + 2 * o.val) / 4 = i.val := hc
      have ho := o.isLt
      exact hji (Fin.ext (by omega))
    show Bool.and (glue (richMask i) (fun _ => false) u (pos0 j o))
        (glue (richMask i) (fun _ => false) u (pos1 j o)) = false
    simp [glue, h0]
  case hon =>
    have ho := o.isLt
    have h0 : richMask i (pos0 i o) = true := by
      apply decide_eq_true
      show (4 * i.val + 2 * o.val) / 4 = i.val
      omega
    have h1 : richMask i (pos1 i o) = true := by
      apply decide_eq_true
      show (4 * i.val + 2 * o.val + 1) / 4 = i.val
      omega
    show Bool.and (glue (richMask i) (fun _ => false) u (pos0 i o))
        (glue (richMask i) (fun _ => false) u (pos1 i o)) = _
    simp [glue, h0, h1]

/-- `AND ⊕ AND` on four suitably distinct variables is not affine (explicit triple). -/
theorem and_xor_and_not_affine {n : ℕ} (p₁ p₂ q₁ q₂ : Fin n)
    (h12 : p₁ ≠ p₂) (hq1p1 : q₁ ≠ p₁) (hq1p2 : q₁ ≠ p₂)
    (hq2p1 : q₂ ≠ p₁) (hq2p2 : q₂ ≠ p₂) :
    ¬ IsAffineFn (fun u : Fin n → Bool =>
        Bool.xor (Bool.and (u p₁) (u p₂)) (Bool.and (u q₁) (u q₂))) := by
  intro haff
  have h := haff
    (fun v => if v = p₁ then true else if v = p₂ then true else false)
    (fun v => if v = p₁ then true else false)
    (fun v => if v = p₂ then true else false)
  simp [h12, Ne.symm h12, hq1p1, hq1p2, hq2p1, hq2p2] at h

/-- **The escalated adversary (proved, all `k`).**  Two per-slot mixture gates: witnesses for
EVERY block, pairwise-independent on every block, `|gates| = 2`. -/
def richTower (k : ℕ) : EntangledTower k 2 (4 * k) where
  gates := Finset.range 2
  wireFn := fun g => richFn ⟨g % 2, by omega⟩
  privMask := richMask
  priv_disjoint := by
    intro i j hij v hv
    have h1 : v.val / 4 = i.val := of_decide_eq_true hv
    apply decide_eq_false
    intro h2
    exact hij (Fin.ext (by omega))
  witness := fun _ => Finset.range 2
  wit_sub := fun _ => Finset.Subset.refl _
  wit_size := fun _ => le_of_eq (Finset.card_range 2).symm
  wit_semantic := by
    intro i g _
    refine ⟨fun _ => false, fun haff => ?_⟩
    rw [show (fun u => richFn (⟨g % 2, by omega⟩ : Fin 2)
          (glue (richMask i) (fun _ => false) u))
        = (fun u => Bool.and (u (pos0 i ⟨g % 2, by omega⟩)) (u (pos1 i ⟨g % 2, by omega⟩)))
      from funext (rich_restrict ⟨g % 2, by omega⟩ i)] at haff
    exact and_pair_not_affine _ _
      (Fin.ne_of_val_ne (by
        show 4 * i.val + 2 * (g % 2) ≠ 4 * i.val + 2 * (g % 2) + 1
        omega)) haff

/-- **The escalated adversary passes the family demand (proved).**  Distinct gates carry
distinct slots; their difference restricts to `AND ⊕ AND` on four distinct variables. -/
theorem richTower_pairwiseIndep (k : ℕ) : PairwiseIndep (richTower k) := by
  intro i g hg g' hg' hne
  have hglt : g < 2 := Finset.mem_range.mp hg
  have hglt' : g' < 2 := Finset.mem_range.mp hg'
  have hmod : g % 2 ≠ g' % 2 := by omega
  refine ⟨fun _ => false, fun haff => ?_⟩
  have hrw : (fun u => (fun x => Bool.xor ((richTower k).wireFn g x)
        ((richTower k).wireFn g' x)) (glue ((richTower k).privMask i) (fun _ => false) u))
      = (fun u => Bool.xor
          (Bool.and (u (pos0 i ⟨g % 2, by omega⟩)) (u (pos1 i ⟨g % 2, by omega⟩)))
          (Bool.and (u (pos0 i ⟨g' % 2, by omega⟩)) (u (pos1 i ⟨g' % 2, by omega⟩)))) := by
    funext u
    show Bool.xor (richFn _ (glue (richMask i) (fun _ => false) u))
        (richFn _ (glue (richMask i) (fun _ => false) u)) = _
    rw [rich_restrict, rich_restrict]
  rw [hrw] at haff
  exact and_xor_and_not_affine _ _ _ _
    (Fin.ne_of_val_ne (by
      show 4 * i.val + 2 * (g % 2) ≠ 4 * i.val + 2 * (g % 2) + 1
      omega))
    (Fin.ne_of_val_ne (by
      show 4 * i.val + 2 * (g' % 2) ≠ 4 * i.val + 2 * (g % 2)
      omega))
    (Fin.ne_of_val_ne (by
      show 4 * i.val + 2 * (g' % 2) ≠ 4 * i.val + 2 * (g % 2) + 1
      omega))
    (Fin.ne_of_val_ne (by
      show 4 * i.val + 2 * (g' % 2) + 1 ≠ 4 * i.val + 2 * (g % 2)
      omega))
    (Fin.ne_of_val_ne (by
      show 4 * i.val + 2 * (g' % 2) + 1 ≠ 4 * i.val + 2 * (g % 2) + 1
      omega))
    haff

/-- The escalated adversary's gate count. -/
theorem richTower_gates_card (k : ℕ) : (richTower k).gates.card = 2 :=
  Finset.card_range 2

/-- **THE PIN, one level up (proved).**  Any lower bound valid for all pairwise-independent
towers at this layout is `≤ 2`: within-block family independence cannot reach the
`k`-multiplier either. -/
theorem pairwise_indep_ceiling (k bound : ℕ)
    (h : ∀ C : EntangledTower k 2 (4 * k), PairwiseIndep C → bound ≤ C.gates.card) :
    bound ≤ 2 := by
  have hb := h (richTower k) (richTower_pairwiseIndep k)
  rwa [richTower_gates_card] at hb

/-- The disjoint bound `k·b` fails on a valid pairwise-independent tower for every `k ≥ 2`. -/
theorem family_k_multiplier_unreachable (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : EntangledTower k 2 (4 * k), PairwiseIndep C ∧ C.gates.card < k * 2 :=
  ⟨richTower k, richTower_pairwiseIndep k, by
    rw [richTower_gates_card]
    omega⟩

end PallLean.Paper93.DeepMath.PathB.FamilyIndependence

#print axioms PallLean.Paper93.DeepMath.PathB.FamilyIndependence.mixTower_not_pairwiseIndep
#print axioms PallLean.Paper93.DeepMath.PathB.FamilyIndependence.richTower_pairwiseIndep
#print axioms PallLean.Paper93.DeepMath.PathB.FamilyIndependence.pairwise_indep_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.FamilyIndependence.family_k_multiplier_unreachable
