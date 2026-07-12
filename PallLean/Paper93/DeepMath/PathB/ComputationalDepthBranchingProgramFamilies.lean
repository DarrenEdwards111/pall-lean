import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBranchingProgramWidth
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukOrMultiplexer
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukElementDistinctness

/-!
# Branching-program width bounds for the OR-multiplexer and element distinctness

`hardF_bp_width_ge` gave an exponential oblivious-BP width bound for the parity-multiplexer.  Now that the
counting machinery (`bp_boundary_le`) is in place, the same bound follows for the other two hard families, because
each has the same function-level per-block subfunction count as its formula-size rung:

* `orMux_bp_width_ge` — the OR-multiplexer needs `2^b − 1 ≤ 2w` (exponential), via the same data-table fooling
  and its merge identity `orMux_merge`;
* `edFun_bp_width_ge` — element distinctness needs `m − 1 ≤ 2w`, via the pair-encoding fooling.

So all three explicit hard families clear **both** models — super-linear formula size and exponential BP width —
off the very same block boundary.  One function property, two models, three functions.

## Honest scope

Restricted (oblivious leveled BP, block read contiguously) lower bounds for explicit functions.  No separation,
no new complexity-class bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.NecHardOr
open PallLean.Paper93.DeepMath.PathB.NecHardED
open PallLean.Paper93.DeepMath.PathB.FunctionResidualObserver
open PallLean.Paper93.DeepMath.PathB.BranchingProgram

/-! ## OR-multiplexer -/

/-- Function-level per-block subfunction count for `orMux`: `≥ 2^{2^b − 1}` via `orMux_merge`. -/
theorem card_funResiduals_orMux_ge {b m : ℕ} (k : Fin m) :
    2 ^ (Dsize b - 1) ≤ (funResiduals (blockS k) (orMux (b := b) (m := m))).card := by
  classical
  rw [← filter_c0_false_card]
  refine Finset.card_le_card_of_injOn
    (fun t => (fun x => orMux (fun i => if i ∈ blockS k then x i else mkt t i))) ?_ ?_
  · intro t _
    exact Finset.mem_coe.mpr (mem_funRes.mpr ⟨mkt t, rfl⟩)
  · intro t ht t' ht' heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    funext c
    have hc := congrFun heq (wit k c)
    dsimp only at hc
    rw [orMux_merge k c t ht, orMux_merge k c t' ht'] at hc
    exact hc

/-- **Exponential width lower bound for `orMux`.**  Any oblivious width-`w` leveled BP computing `orMux` that
reads an address block in a contiguous level range needs `2^b − 1 ≤ 2w`. -/
theorem orMux_bp_width_ge {b m w : ℕ} (k : Fin m) (P : LevBP (nn b m) w)
    (hP : ∀ x, P.eval x = orMux x) (a s : ℕ) (has : a + s ≤ P.len)
    (hblock : ∀ ℓ, ℓ < P.len → (P.var ℓ ∈ blockS k ↔ a ≤ ℓ ∧ ℓ < a + s)) :
    Dsize b - 1 ≤ 2 * w := by
  have h1 := bp_boundary_le P (orMux (b := b) (m := m)) hP (blockS k) a s has hblock
  have h2 : Dsize b - 1 ≤ Nat.log 2 ((funResiduals (blockS k) (orMux (b := b) (m := m))).card) := by
    calc Dsize b - 1 = Nat.log 2 (2 ^ (Dsize b - 1)) := (Nat.log_pow (by norm_num) _).symm
      _ ≤ Nat.log 2 ((funResiduals (blockS k) (orMux (b := b) (m := m))).card) :=
        Nat.log_mono_right (card_funResiduals_orMux_ge k)
  omega

/-! ## Element distinctness -/

/-- Function-level per-block subfunction count for `edFun`: `≥ 2^{m − 1}` via the pair-encoding fooling. -/
theorem card_funResiduals_edFun_ge {b m : ℕ} (hb : 0 < b) (hbig : 2 * m ≤ Dsize b) (k : Fin m) :
    (Finset.univ.filter (fun s : Fin m → Bool => s k = false)).card
      ≤ (funResiduals (blockS k) (edFun (b := b) (m := m))).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun s => (fun x => edFun (fun i => if i ∈ blockS k then x i else outG hb (gPair hbig s) i))) ?_ ?_
  · intro s _
    exact Finset.mem_coe.mpr (mem_funRes.mpr ⟨outG hb (gPair hbig s), rfl⟩)
  · intro s hs s' hs' hgt
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hs hs'
    by_contra hne
    obtain ⟨k'', hk''⟩ : ∃ k'', s k'' ≠ s' k'' := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hk''k : k'' ≠ k := by
      intro h; subst h; rw [hs, hs'] at hk''; exact hk'' rfl
    have hval := congrFun hgt (wit k (gPair hbig s k''))
    dsimp only at hval
    rw [ed_collision hb hbig k k'' hk''k s,
      ed_all_distinct hb hbig k k'' hk''k s s' hk''] at hval
    exact absurd hval (by decide)

/-- **Exponential width lower bound for element distinctness.**  Any oblivious width-`w` leveled BP computing
`edFun` that reads an address block in a contiguous level range needs `m − 1 ≤ 2w`.  With `m ≈ 2^{b-1}` this is
exponential in the block length. -/
theorem edFun_bp_width_ge {b m w : ℕ} (hb : 0 < b) (hbig : 2 * m ≤ Dsize b) (hm : 0 < m) (k : Fin m)
    (P : LevBP (nn b m) w) (hP : ∀ x, P.eval x = edFun x) (a s : ℕ) (has : a + s ≤ P.len)
    (hblock : ∀ ℓ, ℓ < P.len → (P.var ℓ ∈ blockS k ↔ a ≤ ℓ ∧ ℓ < a + s)) :
    m - 1 ≤ 2 * w := by
  have h1 := bp_boundary_le P (edFun (b := b) (m := m)) hP (blockS k) a s has hblock
  have hcnt : 2 ^ (m - 1) ≤ (funResiduals (blockS k) (edFun (b := b) (m := m))).card := by
    rw [← filter_sk_false_card hm k]
    exact card_funResiduals_edFun_ge hb hbig k
  have h2 : m - 1 ≤ Nat.log 2 ((funResiduals (blockS k) (edFun (b := b) (m := m))).card) := by
    calc m - 1 = Nat.log 2 (2 ^ (m - 1)) := (Nat.log_pow (by norm_num) _).symm
      _ ≤ Nat.log 2 ((funResiduals (blockS k) (edFun (b := b) (m := m))).card) :=
        Nat.log_mono_right hcnt
  omega

end PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies

#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies.orMux_bp_width_ge
#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies.edFun_bp_width_ge
