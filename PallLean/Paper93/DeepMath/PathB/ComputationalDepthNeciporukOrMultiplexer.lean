import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBlockDecompositionMin

/-!
# Extending the Nečiporuk rung to a new hard family: the OR-multiplexer

The address-block rung was proved for `hardF`, the **parity**-multiplexer `⊕ₖ data[addr_k]`.  This file shows
the rung is not tied to the XOR combining: it holds verbatim for a genuinely different function, the
**OR-multiplexer** (existential storage access)

```text
  orMux x = [ ∃ block k : x reads a 1 at its addressed cell ]  =  ⋁ₖ data[addr_k].
```

`orMux` and `hardF` are different Boolean functions (existential vs. parity of the lookups), but they share the
*addressing* structure, and that is all the per-block residual count needs.  The key observation: when the other
blocks are driven to read the reserved cell `c0` (value `false`), the OR collapses to the single free block's
lookup, `orMux(block k → c, rest → c0) = data[c]` — exactly the `hardF` merge identity (`orMux_merge`).  Hence
the same data-table fooling family (`2^{2^b − 1}` tables with `c0` free) injects into the block's residuals, and:

* `orMux_blockBoundary_ge` — every address block forces boundary `≥ 2^b − 1`;
* `orMux_minBlockBoundary_ge` — so the min over the structured address-block class does too.

This is a real second hard family for the observer's Nečiporuk calibration.  Dually, the AND-multiplexer
`⋀ₖ data[addr_k]` gives the same bound with the reserved cell set to `true`; the whole "0/1-absorbing combining"
family (parity, OR, AND, threshold) inherits the rung.

## Honest scope

A second explicit hard family for the (restricted) Nečiporuk address-block rung — a restricted formula-size lower
bound, presented as such.  No separation, no new complexity-class bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NecHardOr

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open PallLean.Paper93.DeepMath.PathB.BlockDecompositionMin

variable {b m : ℕ}

/-- The **OR-multiplexer / existential storage access**: some address block reads a `1`. -/
noncomputable def orMux (x : Fin (nn b m) → Bool) : Bool :=
  decide (∃ k : Fin m, x (dataVar (addr x k)) = true)

/-- **The merge identity for `orMux`.**  Driving the other blocks to the reserved cell `c0` (value `false`)
collapses the OR to the free block's lookup: `orMux(block k → c, rest → c0) = data[c]`. -/
theorem orMux_merge (k : Fin m) (c : Fin (Dsize b)) (t : Fin (Dsize b) → Bool)
    (hc0 : t c0 = false) :
    orMux (fun i => if i ∈ blockS k then wit k c i else mkt t i) = t c := by
  set M : Fin (nn b m) → Bool := (fun i => if i ∈ blockS k then wit k c i else mkt t i) with hM
  have hmd : ∀ v : Fin (Dsize b), M (dataVar (m := m) v) = t v := by
    intro v; rw [hM]; simp only [if_neg (dataVar_not_mem k v)]; exact mkt_dataVar t v
  have haddr_self : addr M k = c := by
    unfold addr
    have he : (fun j => M (addrBitVar (m := m) k j)) = (e b).symm c := by
      funext j; rw [hM]; simp only [if_pos (addrBitVar_mem k j)]; exact wit_addrBitVar k c j
    rw [he, Equiv.apply_symm_apply]
  have haddr_other : ∀ k' : Fin m, k' ≠ k → addr M k' = c0 := by
    intro k' hk'
    unfold addr
    have he : (fun j => M (addrBitVar (m := m) k' j)) = (fun _ => false) := by
      funext j; rw [hM]; simp only [if_neg (addrBitVar_ne_mem hk' j)]; exact mkt_addrBitVar t k' j
    rw [he]; rfl
  have hval : ∀ k' : Fin m, M (dataVar (addr M k')) = (if k' = k then t c else false) := by
    intro k'
    by_cases h : k' = k
    · subst h; rw [haddr_self, hmd]; simp
    · rw [haddr_other k' h, hmd, hc0]; simp [h]
  unfold orMux
  have hbody : (∃ k' : Fin m, M (dataVar (addr M k')) = true) ↔ (t c = true) := by
    constructor
    · rintro ⟨k', hk'⟩
      rw [hval k'] at hk'
      by_cases h : k' = k
      · rw [if_pos h] at hk'; exact hk'
      · rw [if_neg h] at hk'; exact absurd hk' (by decide)
    · intro h
      exact ⟨k, by rw [hval k, if_pos rfl]; exact h⟩
  cases htc : t c
  · simp only [decide_eq_false_iff_not]
    rw [hbody, htc]
    decide
  · simp only [decide_eq_true_eq]
    rw [hbody]
    exact htc

/-- **`2^{2^b − 1}` distinct residuals per address block.**  The `c0`-free data tables inject into the block's
residuals via `orMux_merge` — the same fooling family as for `hardF`. -/
theorem card_blockResiduals_orMux_ge (k : Fin m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = orMux x) :
    (Finset.univ.filter (fun t : Fin (Dsize b) → Bool => t c0 = false)).card
      ≤ (blockResiduals (blockS k) F).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun t => (fun x => BFormula.eval F (fun i => if i ∈ blockS k then x i else mkt t i)))
    ?_ ?_
  · intro t _
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨mkt t, Finset.mem_univ _, rfl⟩)
  · intro t ht t' ht' hgt
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    funext c
    have hc : BFormula.eval F (fun i => if i ∈ blockS k then wit k c i else mkt t i)
            = BFormula.eval F (fun i => if i ∈ blockS k then wit k c i else mkt t' i) :=
      congrFun hgt (wit k c)
    rw [hF, hF, orMux_merge k c t ht, orMux_merge k c t' ht'] at hc
    exact hc

/-- **The address-block rung for `orMux`.**  Every address block forces boundary `≥ 2^b − 1`. -/
theorem orMux_blockBoundary_ge (k : Fin m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = orMux x) :
    Dsize b - 1 ≤ formulaBlockBoundary (blockS k) F := by
  have h1 : 2 ^ (Dsize b - 1) ≤ (blockResiduals (blockS k) F).card := by
    rw [← filter_c0_false_card]
    exact card_blockResiduals_orMux_ge k F hF
  unfold formulaBlockBoundary
  calc Dsize b - 1 = Nat.log 2 (2 ^ (Dsize b - 1)) := (Nat.log_pow (by norm_num) _).symm
    _ ≤ Nat.log 2 ((blockResiduals (blockS k) F).card) := Nat.log_mono_right h1

/-- **The min over the structured address-block class forces boundary `≥ 2^b − 1` for `orMux` too.**  So the
Nečiporuk rung is not special to the parity combining — a second explicit hard family clears it. -/
theorem orMux_minBlockBoundary_ge (hm : 0 < m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = orMux x) :
    Dsize b - 1 ≤ minBlockBoundary hm F := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  unfold minBlockBoundary
  apply Finset.le_inf'
  intro k _
  exact orMux_blockBoundary_ge k F hF

/-! ## The explicit formula-size lower bound -/

/-- **Nečiporuk formula-size lower bound for the OR-multiplexer.**  Summing the per-block bound `2^b − 1`
over the `m` address blocks (the data block contributes `≥ 0`) and plugging into the general Nečiporuk bound
gives, for any `B₂` formula `F` computing `orMux`,
`m·(2^b − 1) ≤ 2·clog₂(|Tok|+1)·litCount F + 2·(m + 1)` — the same explicit super-linear bound as `hardF`. -/
theorem orMux_litCount_lower (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = orMux x) :
    m * (Dsize b - 1) ≤
      2 * Nat.clog 2 (Fintype.card (NF.Tok (nn b m)) + 1) * BFormula.litCount F
        + 2 * (m + 1) := by
  classical
  have hnec := neciporuk_formula_lower_bound
    (Finset.univ : Finset (Option (Fin m))) (blkS (b := b) (m := m)) F blkS_disj blkS_cover
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin] at hnec
  have hconst : ∑ _k : Fin m, (Dsize b - 1) = m * (Dsize b - 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hper : ∀ k : Fin m,
      Dsize b - 1 ≤ Nat.log 2 ((blockResiduals (blkS (some k)) F).card) := by
    intro k
    rw [blkS_some]
    exact orMux_blockBoundary_ge k F hF
  have hge : m * (Dsize b - 1)
      ≤ ∑ k : Fin m, Nat.log 2 ((blockResiduals (blkS (some k)) F).card) :=
    hconst ▸ Finset.sum_le_sum (fun k _ => hper k)
  have hlow : m * (Dsize b - 1)
      ≤ ∑ o : Option (Fin m), Nat.log 2 ((blockResiduals (blkS o) F).card) := by
    rw [Fintype.sum_option]
    exact le_trans hge (Nat.le_add_left _ _)
  exact le_trans hlow hnec

end PallLean.Paper93.DeepMath.PathB.NecHardOr

#print axioms PallLean.Paper93.DeepMath.PathB.NecHardOr.orMux_merge
#print axioms PallLean.Paper93.DeepMath.PathB.NecHardOr.orMux_litCount_lower
#print axioms PallLean.Paper93.DeepMath.PathB.NecHardOr.orMux_blockBoundary_ge
#print axioms PallLean.Paper93.DeepMath.PathB.NecHardOr.orMux_minBlockBoundary_ge
