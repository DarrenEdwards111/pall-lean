import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBlockDecompositionMin

/-!
# The dual: a partial address block (dropping `d` bits) still forces `≥ 2^{b−d} − 1`

`BlockDecompositionMinBoundedData` used that *adding* a variable to the free block at most **halves** the residual
count (a lower bound on how fast boundary can drop when we enlarge).  This file is the dual: it uses that adding a
variable at most **squares** the residual count — a residual on `insert v S` is determined by its two `x_v`-slices,
each a residual on `S`.  Removing `d` address bits from a block therefore costs at most a factor `2^d` in the log,
and combined with the base bound `boundary(blockS k) ≥ 2^b − 1` the arithmetic gives, for any subset `S` of block
`k`'s address bits,

```text
  formulaBlockBoundary S F ≥ 2^{|S|} − 1     (hardF_partial_blockBoundary_ge).
```

With `|S| = b − d` (dropping `d` of the `b` address bits) this is `2^{b−d} − 1`: a partial address block still
multiplexes over its `2^{b−d}` reachable cells.  The first three lemmas are general observer-boundary facts (no
`hardF`), reusable beyond this family.

## Honest scope

A quantitative extension of the address-block min-realized rung to *partial* blocks.  Still a restricted class
(subsets of a single address block), not every decomposition; the general min stays `= CookLevinFrontierHyp`.  No
separation, no new complexity-class bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinPartial

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open scoped BigOperators

/-! ## General: one extra free variable at most squares the residual count -/

/-- Membership characterization of `blockResiduals`, proven once so the `Finset.image` unfolding is isolated. -/
theorem mem_blockRes {n : ℕ} {S : Finset (Fin n)} {F : BFormula n} {g : (Fin n → Bool) → Bool} :
    g ∈ blockResiduals S F ↔
      ∃ α : Fin n → Bool, (fun x => BFormula.eval F (fun i => if i ∈ S then x i else α i)) = g := by
  classical
  constructor
  · intro h
    rw [blockResiduals] at h
    obtain ⟨α, -, hα⟩ := Finset.mem_image.mp h
    exact ⟨α, hα⟩
  · rintro ⟨α, rfl⟩
    rw [blockResiduals]
    exact Finset.mem_image.mpr ⟨α, Finset.mem_univ _, rfl⟩

/-- **Adding a variable to the free block at most squares the residual count.**  A residual on `insert v S` is
determined by its two `x_v`-slices, each a residual on `S`, so the slice map injects into
`blockResiduals S F × blockResiduals S F`. -/
theorem blockResiduals_card_insert_le_sq {n : ℕ} (v : Fin n) (S : Finset (Fin n)) (F : BFormula n) :
    (blockResiduals (insert v S) F).card ≤ (blockResiduals S F).card ^ 2 := by
  classical
  by_cases hv : v ∈ S
  · rw [Finset.insert_eq_self.mpr hv, sq]
    have hne : (blockResiduals S F).Nonempty := by
      simp only [blockResiduals]; exact Finset.univ_nonempty.image _
    have h1 : 1 ≤ (blockResiduals S F).card := Finset.card_pos.mpr hne
    nlinarith [h1]
  · have slice_eq : ∀ (c : Bool) (β : Fin n → Bool),
        (fun x : Fin n → Bool =>
            BFormula.eval F (fun i => if i ∈ insert v S then (Function.update x v c) i else β i))
          = (fun x : Fin n → Bool =>
              BFormula.eval F (fun i => if i ∈ S then x i else (Function.update β v c) i)) := by
      intro c β
      funext x
      congr 1
      funext i
      by_cases hiv : i = v
      · subst hiv
        rw [if_pos (Finset.mem_insert_self i S), Function.update_self, if_neg hv, Function.update_self]
      · simp only [Function.update_of_ne hiv]
        by_cases hiS : i ∈ S
        · rw [if_pos (Finset.mem_insert_of_mem hiS), if_pos hiS]
        · rw [if_neg (fun h => (Finset.mem_insert.mp h).elim hiv hiS), if_neg hiS]
    have hcard : (blockResiduals (insert v S) F).card
        ≤ (blockResiduals S F ×ˢ blockResiduals S F).card := by
      apply Finset.card_le_card_of_injOn
        (fun g => (fun x : Fin n → Bool => g (Function.update x v false),
                   fun x : Fin n → Bool => g (Function.update x v true)))
      · intro g hg
        obtain ⟨β, rfl⟩ := mem_blockRes.mp hg
        exact Finset.mk_mem_product
          (mem_blockRes.mpr ⟨Function.update β v false, (slice_eq false β).symm⟩)
          (mem_blockRes.mpr ⟨Function.update β v true, (slice_eq true β).symm⟩)
      · intro g _ g' _ heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨h0, h1⟩ := heq
        funext x
        cases hb : x v
        · have hx : Function.update x v false = x := by
            funext j; by_cases hjv : j = v
            · subst hjv; rw [Function.update_self, hb]
            · rw [Function.update_of_ne hjv]
          calc g x = g (Function.update x v false) := by rw [hx]
            _ = g' (Function.update x v false) := congrFun h0 x
            _ = g' x := by rw [hx]
        · have hx : Function.update x v true = x := by
            funext j; by_cases hjv : j = v
            · subst hjv; rw [Function.update_self, hb]
            · rw [Function.update_of_ne hjv]
          calc g x = g (Function.update x v true) := by rw [hx]
            _ = g' (Function.update x v true) := congrFun h1 x
            _ = g' x := by rw [hx]
    calc (blockResiduals (insert v S) F).card
        ≤ (blockResiduals S F ×ˢ blockResiduals S F).card := hcard
      _ = (blockResiduals S F).card ^ 2 := by rw [Finset.card_product, sq]

/-- **Adding a variable at most doubles the boundary (plus one).** -/
theorem formulaBlockBoundary_insert_le {n : ℕ} (v : Fin n) (S : Finset (Fin n)) (F : BFormula n) :
    formulaBlockBoundary (insert v S) F ≤ 2 * formulaBlockBoundary S F + 1 := by
  classical
  have hcard := blockResiduals_card_insert_le_sq v S F
  have hne : (blockResiduals S F).Nonempty := by
    simp only [blockResiduals]; exact Finset.univ_nonempty.image _
  have hne2 : (blockResiduals (insert v S) F).Nonempty := by
    simp only [blockResiduals]; exact Finset.univ_nonempty.image _
  unfold formulaBlockBoundary
  have h1 : (blockResiduals S F).card < 2 ^ (Nat.log 2 ((blockResiduals S F).card) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : (blockResiduals (insert v S) F).card < 2 ^ (2 * Nat.log 2 ((blockResiduals S F).card) + 2) := by
    calc (blockResiduals (insert v S) F).card ≤ (blockResiduals S F).card ^ 2 := hcard
      _ < (2 ^ (Nat.log 2 ((blockResiduals S F).card) + 1)) ^ 2 := by
          apply Nat.pow_lt_pow_left h1; norm_num
      _ = 2 ^ (2 * Nat.log 2 ((blockResiduals S F).card) + 2) := by rw [← pow_mul]; congr 1; ring
  have h3 : Nat.log 2 ((blockResiduals (insert v S) F).card)
      < 2 * Nat.log 2 ((blockResiduals S F).card) + 2 :=
    Nat.log_lt_of_lt_pow (Finset.card_ne_zero.mpr hne2) h2
  omega

/-- **Iterating: adding a whole set `D` to the free block.** -/
theorem formulaBlockBoundary_union_le {n : ℕ} (S D : Finset (Fin n)) (F : BFormula n) :
    formulaBlockBoundary (S ∪ D) F + 1 ≤ 2 ^ D.card * (formulaBlockBoundary S F + 1) := by
  classical
  induction D using Finset.induction with
  | empty => simp
  | @insert v D hv ih =>
      rw [Finset.union_insert, Finset.card_insert_of_notMem hv]
      have hstep := formulaBlockBoundary_insert_le v (S ∪ D) F
      calc formulaBlockBoundary (insert v (S ∪ D)) F + 1
          ≤ 2 * (formulaBlockBoundary (S ∪ D) F + 1) := by omega
        _ ≤ 2 * (2 ^ D.card * (formulaBlockBoundary S F + 1)) := by omega
        _ = 2 ^ (D.card + 1) * (formulaBlockBoundary S F + 1) := by rw [pow_succ]; ring

/-! ## `hardF`: the partial address block -/

variable {b m : ℕ}

/-- The address-bit indexing of a block is injective, so `blockS k` has exactly `b` variables. -/
theorem addrBitVar_injective (k : Fin m) : Function.Injective (addrBitVar (m := m) (b := b) k) := by
  intro j j' h
  have hval : (addrBitVar (m := m) k j).val = (addrBitVar (m := m) k j').val := congrArg Fin.val h
  simp only [addrBitVar] at hval
  exact Fin.ext (by omega)

theorem blockS_card (k : Fin m) : (blockS (b := b) (m := m) k).card = b := by
  rw [blockS, Finset.card_image_of_injective _ (addrBitVar_injective k), Finset.card_univ,
    Fintype.card_fin]

/-- **A partial address block still forces `≥ 2^{|S|} − 1`.**  For any subset `S` of block `k`'s address bits
(dropping `d = b − |S|` bits), the boundary is `≥ 2^{|S|} − 1 = 2^{b−d} − 1`. -/
theorem hardF_partial_blockBoundary_ge (k : Fin m) (S : Finset (Fin (nn b m)))
    (hS : S ⊆ blockS k) (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    2 ^ S.card - 1 ≤ formulaBlockBoundary S F := by
  have hbase := hardF_blockBoundary_ge k F hF
  have hd : Dsize b = 2 ^ b := dsize_eq
  have hbpos : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hSb : S.card ≤ b := by
    have := Finset.card_le_card hS; rw [blockS_card] at this; exact this
  have hunion : S ∪ (blockS k \ S) = blockS k := Finset.union_sdiff_of_subset hS
  have hdc : (blockS k \ S).card = b - S.card := by rw [Finset.card_sdiff_of_subset hS, blockS_card]
  have hstep := formulaBlockBoundary_union_le S (blockS k \ S) F
  rw [hunion, hdc] at hstep
  have hb2 : 2 ^ b ≤ formulaBlockBoundary (blockS k) F + 1 := by omega
  have h2b : 2 ^ b = 2 ^ (b - S.card) * 2 ^ S.card := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (b - S.card) := pow_pos (by norm_num) _
  have hchain : 2 ^ (b - S.card) * 2 ^ S.card
      ≤ 2 ^ (b - S.card) * (formulaBlockBoundary S F + 1) := by
    rw [← h2b]; exact le_trans hb2 hstep
  have hfin : 2 ^ S.card ≤ formulaBlockBoundary S F + 1 := Nat.le_of_mul_le_mul_left hchain hpos
  omega

end PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinPartial

#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinPartial.formulaBlockBoundary_insert_le
#print axioms PallLean.Paper93.DeepMath.PathB.BlockDecompositionMinPartial.hardF_partial_blockBoundary_ge
