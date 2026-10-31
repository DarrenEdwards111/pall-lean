import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWitnessLocalization
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOverlapFromSharedInputs

/-!
# The entanglement ruler: shared variables are inert currency for private demands

The missing invention was named as a ruler that measures how the tower's correlation obstructs
sharing.  This file builds the half of that ruler that is real mathematics today, and it has a
sharp punchline: **for private-territory demands, shared variables buy the adversary NOTHING.**

## The setting

Each block `i` owns a PRIVATE territory `privMask i` — pairwise disjoint variable regions
(`priv_disjoint`); everything else is the shared substrate, where the blocks' inputs entangle.
The semantic demand is as in `WitnessLocalization`, but pointed at the private part: a witness
for block `i` must be nonlinear on block `i`'s PRIVATE territory.

## The ruler

`depSet g` — the set of variables a gate's wire function actually depends on (flip-sensitivity).
The ruler measures a gate's service capacity as its **private reach**:

* **`no_private_reach_no_witness`** — a wire that depends on NO variable of a private territory
  is affine on it (its restrictions are constant), hence witnesses nothing there.  Built on the
  agreement lemma `indep_agree`: insensitivity coordinate-by-coordinate propagates to whole
  regions.
* **`witness_forces_reach`** — contrapositive: witnessing block `i` FORCES dependency on a
  variable of block `i`'s private territory.
* **`mult_le_depCard`** — THE RULER: a gate's multiplicity is at most its dependency count.
  Witnessed blocks inject into the dependency set — one private variable each, all distinct
  because private territories are disjoint.  No factor for the sharing profile: however
  entangled the blocks' shared substrate is, however global the gate, service capacity for
  private demands is paid ONLY in private-variable dependencies.
* **`entangled_reason`** — the cash-out: dependency count `≤ s` on every gate ⟹
  `k·b ≤ s·|gates|`.  Compare `OverlapFromSharedInputs` (`k·b ≤ s·t·|gates|`): the
  sharing-profile factor `t` is GONE.  Correlation is priced at zero.
* **`entangled_overlap`** — the overlap form: `overlap ≤ (s−1)·|gates|`.
* **`straddleExample`** — calibration: one gate CAN witness two blocks (nonlinear on both
  private territories) — sharing is not forbidden, it is PRICED: that gate provably pays with
  dependencies in both territories.

## Honest scope

The ruler closes the `t`-escape of the geometry brick for private demands: Uhlig-style capacity
from shared inputs is provably worthless against private nonlinearity.  What it does NOT do:
(i) it does not bound `depCard` — a global gate may depend on everything (`s ≈ n`); the
localization residue persists exactly as before; (ii) it does not prove the tower INDUCES
private-nonlinear demands with large `b` — that demand-generation claim is the standing
`wit_size`/`wit_semantic`-field caveat, and proving it for SAT's tower is `cost_super`'s
residue; (iii) where blocks have NO private territory (identical copies — Uhlig's regime), the
ruler is vacuous, exactly as it must be, since there sharing is genuinely free.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementRuler

open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.AffineSemantics
open PallLean.Paper93.DeepMath.PathB.TheReasonShared
open PallLean.Paper93.DeepMath.PathB.WitnessLocalization
open PallLean.Paper93.DeepMath.PathB.OverlapFromSharedInputs

variable {n : ℕ}

/-- Flip one coordinate of an assignment. -/
def flipAt (x : Fin n → Bool) (v : Fin n) : Fin n → Bool :=
  fun u => if u = v then ! x u else x u

/-- `F` **depends on** variable `v`: some flip of `v` changes the output. -/
def DependsOn (F : (Fin n → Bool) → Bool) (v : Fin n) : Prop :=
  ∃ x, F (flipAt x v) ≠ F x

instance (F : (Fin n → Bool) → Bool) (v : Fin n) : Decidable (DependsOn F v) := by
  unfold DependsOn
  infer_instance

/-- **The agreement lemma.**  If `F` depends on no variable of `D`, then `F` agrees on any two
assignments that agree outside `D` — coordinate insensitivity propagates to regions. -/
theorem indep_agree (F : (Fin n → Bool) → Bool) :
    ∀ D : Finset (Fin n), (∀ v ∈ D, ¬ DependsOn F v) →
      ∀ x y : Fin n → Bool, (∀ v, v ∉ D → x v = y v) → F x = F y := by
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro _ x y hagree
    have hxy : x = y := funext (fun v => hagree v (Finset.notMem_empty v))
    rw [hxy]
  | insert a s ha ih =>
    intro hdep x y hagree
    have hnd : ∀ w, F (flipAt w a) = F w := by
      intro w
      by_contra hne
      exact hdep a (Finset.mem_insert_self a s) ⟨w, hne⟩
    set z : Fin n → Bool := fun u => if u = a then y a else x u with hz
    have h1 : F x = F z := by
      by_cases hxy : x a = y a
      · have hzx : z = x := by
          funext u
          rw [hz]
          by_cases hu : u = a
          · subst hu; simp [hxy.symm]
          · simp [hu]
        rw [hzx]
      · have hya : y a = ! (x a) := by
          cases hxa : x a <;> cases hya' : y a <;> simp_all
        have hzf : z = flipAt x a := by
          funext u
          rw [hz]
          unfold flipAt
          by_cases hu : u = a
          · subst hu; simp [hya]
          · simp [hu]
        rw [hzf]
        exact (hnd x).symm
    have h2 : F z = F y := by
      apply ih (fun v hv => hdep v (Finset.mem_insert_of_mem hv))
      intro v hv
      by_cases hva : v = a
      · subst hva; rw [hz]; simp
      · have hvout : v ∉ insert a s := by
          intro hmem
          rcases Finset.mem_insert.mp hmem with h | h
          · exact hva h
          · exact hv h
        rw [hz]
        simp only [if_neg hva]
        exact hagree v hvout
    exact h1.trans h2

/-- No dependency inside a region ⟹ every restriction to that region is constant. -/
theorem restriction_constant_of_no_reach (F : (Fin n → Bool) → Bool) (blk ρ : Fin n → Bool)
    (h : ∀ v, blk v = true → ¬ DependsOn F v) (u u' : Fin n → Bool) :
    F (glue blk ρ u) = F (glue blk ρ u') := by
  apply indep_agree F (Finset.univ.filter (fun v => blk v = true))
  · intro v hv
    rw [Finset.mem_filter] at hv
    exact h v hv.2
  · intro v hv
    have hb : blk v = false := by
      by_cases hbv : blk v = true
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hbv⟩) hv
      · cases hbb : blk v
        · rfl
        · exact absurd hbb hbv
    show glue blk ρ u v = glue blk ρ u' v
    simp [glue, hb]

/-- **No private reach, no witness (proved).**  A wire depending on no variable of a private
territory is affine on it — its restrictions are constant — hence cannot witness it. -/
theorem no_private_reach_no_witness (F : (Fin n → Bool) → Bool) (blk : Fin n → Bool)
    (h : ∀ v, blk v = true → ¬ DependsOn F v) :
    ¬ NonlinearOnBlock blk F := by
  rintro ⟨ρ, hρ⟩
  apply hρ
  have hconst : (fun u => F (glue blk ρ u)) = (fun _ => F (glue blk ρ (fun _ => false))) :=
    funext (fun u => restriction_constant_of_no_reach F blk ρ h u (fun _ => false))
  rw [hconst]
  exact isAffineFn_const _

/-- A tower with **private territories**: pairwise disjoint variable regions per block, and the
semantic demand pointed at them — a witness for block `i` is nonlinear on block `i`'s PRIVATE
territory.  The shared substrate (everything outside all private territories) is where the
blocks entangle; the ruler will show it is inert. -/
structure EntangledTower (k b n : ℕ) where
  /-- the gates of the circuit -/
  gates : Finset ℕ
  /-- the wire function each gate computes -/
  wireFn : ℕ → (Fin n → Bool) → Bool
  /-- block `i`'s PRIVATE territory -/
  privMask : Fin k → Fin n → Bool
  /-- private territories are pairwise disjoint -/
  priv_disjoint : ∀ i j, i ≠ j → ∀ v, privMask i v = true → privMask j v = false
  /-- block `i`'s witness gates -/
  witness : Fin k → Finset ℕ
  /-- witnesses are real gates -/
  wit_sub : ∀ i, witness i ⊆ gates
  /-- each block needs at least `b` witness gates -/
  wit_size : ∀ i, b ≤ (witness i).card
  /-- the demand: a witness for block `i` is nonlinear on block `i`'s private territory -/
  wit_semantic : ∀ i, ∀ g ∈ witness i, NonlinearOnBlock (privMask i) (wireFn g)

/-- Forget the semantics: the underlying shared-witness circuit. -/
def toShared {k b n : ℕ} (C : EntangledTower k b n) : SharedCircuitForTarget k b :=
  ⟨C.gates, C.witness, C.wit_sub, C.wit_size⟩

/-- **Witnessing forces private reach (proved).**  A witness for block `i` depends on some
variable of block `i`'s private territory. -/
theorem witness_forces_reach {k b n : ℕ} (C : EntangledTower k b n) (i : Fin k) (g : ℕ)
    (hg : g ∈ C.witness i) :
    ∃ v, C.privMask i v = true ∧ DependsOn (C.wireFn g) v := by
  by_contra hno
  have h : ∀ v, C.privMask i v = true → ¬ DependsOn (C.wireFn g) v := by
    intro v hv hd
    exact hno ⟨v, hv, hd⟩
  exact no_private_reach_no_witness _ _ h (C.wit_semantic i g hg)

/-- The dependency set of a gate — what its wire function actually reads. -/
def depSet {k b n : ℕ} (C : EntangledTower k b n) (g : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => DependsOn (C.wireFn g) v)

/-- **THE RULER (proved).**  A gate's multiplicity is at most its dependency count: each
witnessed block contributes one private variable to the dependency set, and private territories
are disjoint, so the contributions are distinct.  NO sharing-profile factor — however entangled
the shared substrate, service capacity for private demands is paid only in private reach. -/
theorem mult_le_depCard {k b n : ℕ} (C : EntangledTower k b n) (g : ℕ) :
    mult (toShared C) g ≤ (depSet C g).card := by
  show ((Finset.univ : Finset (Fin k)).filter (fun i => g ∈ (toShared C).witness i)).card
      ≤ (depSet C g).card
  rcases Finset.eq_empty_or_nonempty
      ((Finset.univ : Finset (Fin k)).filter (fun i => g ∈ (toShared C).witness i)) with
    hemp | hne
  · rw [hemp]
    simp
  · obtain ⟨i₀, hi₀⟩ := hne
    rw [Finset.mem_filter] at hi₀
    obtain ⟨v₀, _, _⟩ := witness_forces_reach C i₀ g hi₀.2
    haveI : Inhabited (Fin n) := ⟨v₀⟩
    apply Finset.card_le_card_of_injOn
      (fun i => if h : g ∈ C.witness i then
        Classical.choose (witness_forces_reach C i g h) else default)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi
      have hi' : g ∈ C.witness i := hi
      dsimp only
      rw [dif_pos hi']
      obtain ⟨_, hd⟩ := Classical.choose_spec (witness_forces_reach C i g hi')
      simp only [depSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hd
    · intro i hi j hj hij
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
      have hi' : g ∈ C.witness i := hi
      have hj' : g ∈ C.witness j := hj
      dsimp only at hij
      rw [dif_pos hi', dif_pos hj'] at hij
      by_contra hne'
      obtain ⟨hvi, _⟩ := Classical.choose_spec (witness_forces_reach C i g hi')
      obtain ⟨hvj, _⟩ := Classical.choose_spec (witness_forces_reach C j g hj')
      rw [hij] at hvi
      have hfalse := C.priv_disjoint i j hne' _ hvi
      rw [hfalse] at hvj
      exact Bool.noConfusion hvj

/-- **The cash-out (proved).**  Dependency count `≤ s` on every gate ⟹ `k·b ≤ s·|gates|`.
The sharing-profile factor `t` of `OverlapFromSharedInputs` is GONE: correlation through the
shared substrate is priced at zero for private demands. -/
theorem entangled_reason {k b n : ℕ} (C : EntangledTower k b n) (s : ℕ)
    (hs : ∀ g ∈ C.gates, (depSet C g).card ≤ s) :
    k * b ≤ s * C.gates.card :=
  the_reason_shared (toShared C) s
    (fun g hg => le_trans (mult_le_depCard C g) (hs g hg))

/-- The overlap form of the ruler: `overlap ≤ (s−1)·|gates|`. -/
theorem entangled_overlap {k b n : ℕ} (C : EntangledTower k b n) (s : ℕ)
    (hs : ∀ g ∈ C.gates, (depSet C g).card ≤ s) :
    overlap (toShared C) ≤ (s - 1) * C.gates.card :=
  overlap_le_of_mult_le (toShared C) s
    (fun g hg => le_trans (mult_le_depCard C g) (hs g hg))

/-! ### Calibration: sharing is priced, not forbidden -/

/-- One wire straddling two private territories: `(x₀∧x₁) ⊕ (x₂∧x₃)`. -/
def straddleFn : (Fin 4 → Bool) → Bool :=
  fun x => Bool.xor (Bool.and (x 0) (x 1)) (Bool.and (x 2) (x 3))

/-- **The straddle example (proved).**  A single gate CAN witness two blocks — nonlinear on both
private territories `{0,1}` and `{2,3}` — so the ruler forbids nothing; it PRICES: by
`witness_forces_reach` this gate must (and does) pay with dependencies in both territories. -/
def straddleExample : EntangledTower 2 1 4 where
  gates := {0}
  wireFn := fun _ => straddleFn
  privMask := fun i => fun v =>
    if i.val = 0 then decide (v.val ≤ 1) else decide (2 ≤ v.val)
  priv_disjoint := by decide
  witness := fun _ => {0}
  wit_sub := fun _ => Finset.Subset.refl _
  wit_size := fun _ => by decide
  wit_semantic := by
    intro i g _
    refine ⟨fun _ => false, fun haff => ?_⟩
    fin_cases i
    · exact absurd
        (haff (fun _ => true) (fun v => decide (v.val = 0)) (fun v => decide (v.val = 1)))
        (by decide)
    · exact absurd
        (haff (fun _ => true) (fun v => decide (v.val = 2)) (fun v => decide (v.val = 3)))
        (by decide)

end PallLean.Paper93.DeepMath.PathB.EntanglementRuler

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuler.indep_agree
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuler.no_private_reach_no_witness
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuler.witness_forces_reach
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuler.mult_le_depCard
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuler.entangled_reason
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementRuler.entangled_overlap
