import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBlockDecompositionMin

/-!
# A genuinely different Nečiporuk hard family: element distinctness

`hardF` (parity-multiplexer) and `orMux` (existential storage access) both *address* into a shared data table.
This file gives the classic *second* Nečiporuk-hard function, structurally different: **element distinctness**,
which uses no data cells at all —

```text
  edFun x  =  [ all m block-addresses  addr x 0, …, addr x (m-1)  are distinct ].
```

The per-block argument is different too.  On block `k`, driving the other `m−1` blocks to a set of distinct
addresses `T`, the residual of `edFun` becomes the *set-indicator* `a ↦ [a ∉ T]` (a function of block `k`'s
address `a`).  Distinct `T` give distinct residuals (symmetric-difference), so many realizable `T` force many
residuals.  We realize them with a **pair-encoding**: block `k'` chooses between its private pair of addresses
`2k'` and `2k'+1` according to a bit `s(k')`.  This yields `2^{m−1}` distinct residuals, hence:

* `ed_blockBoundary_ge` — every address block forces boundary `≥ m − 1`;
* `ed_minBlockBoundary_ge` — so the min over the structured class does too.

With `m` up to `2^{b-1}` (the pair-encoding needs `2m ≤ 2^b`) this is `≥ 2^{b-1} − 1`, super-logarithmic in the
input size `nn ≈ 2^b` — a real second explicit hard family for the observer's Nečiporuk calibration, proved by a
subset/fooling family rather than a data-table one.

## Honest scope

A second, structurally different explicit hard family for the (restricted) Nečiporuk address-block rung — a
restricted formula-size lower bound, presented as such.  No separation, no new complexity-class bound.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NecHardED

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open PallLean.Paper93.DeepMath.PathB.BlockDecompositionMin

variable {b m : ℕ}

/-- **Element distinctness**: all `m` block-addresses are pairwise distinct. -/
noncomputable def edFun (x : Fin (nn b m) → Bool) : Bool :=
  decide (∀ k1 k2 : Fin m, k1 ≠ k2 → addr x k1 ≠ addr x k2)

/-! ## A multi-block address setter -/

/-- Set every block `k'`'s address bits to encode `g k'` (data cells → `false`). -/
noncomputable def outG (hb : 0 < b) (g : Fin m → Fin (Dsize b)) : Fin (nn b m) → Bool :=
  fun i => if h : i.val < m * b then
    ((e b).symm (g ⟨i.val / b, (Nat.div_lt_iff_lt_mul hb).mpr h⟩)) ⟨i.val % b, Nat.mod_lt _ hb⟩
  else false

theorem outG_addrBitVar (hb : 0 < b) (g : Fin m → Fin (Dsize b)) (k' : Fin m) (j : Fin b) :
    outG hb g (addrBitVar (m := m) k' j) = ((e b).symm (g k')) j := by
  have hlt : (addrBitVar (m := m) k' j).val < m * b := by
    show k'.val * b + j.val < m * b
    have e1 : (k'.val + 1) * b ≤ m * b := by gcongr; exact k'.isLt
    have e2 : (k'.val + 1) * b = k'.val * b + b := by ring
    have := j.isLt; omega
  have hdiv : (addrBitVar (m := m) k' j).val / b = k'.val := by
    show (k'.val * b + j.val) / b = k'.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have hmod : (addrBitVar (m := m) k' j).val % b = j.val := by
    show (k'.val * b + j.val) % b = j.val
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  unfold outG
  rw [dif_pos hlt]
  exact congrArg₂ (fun (kk : Fin m) (jj : Fin b) => (e b).symm (g kk) jj) (Fin.ext hdiv) (Fin.ext hmod)

theorem addr_outG_combined (hb : 0 < b) (g : Fin m → Fin (Dsize b)) (k : Fin m)
    (c : Fin (Dsize b)) (k' : Fin m) (hk' : k' ≠ k) :
    addr (fun i => if i ∈ blockS k then wit k c i else outG hb g i) k' = g k' := by
  unfold addr
  have he : (fun j => (if addrBitVar (m := m) k' j ∈ blockS k then wit k c (addrBitVar k' j)
      else outG hb g (addrBitVar k' j))) = (e b).symm (g k') := by
    funext j
    rw [if_neg (addrBitVar_ne_mem hk' j)]
    exact outG_addrBitVar hb g k' j
  rw [he, Equiv.apply_symm_apply]

theorem addr_wit_combined (hb : 0 < b) (g : Fin m → Fin (Dsize b)) (k : Fin m) (c : Fin (Dsize b)) :
    addr (fun i => if i ∈ blockS k then wit k c i else outG hb g i) k = c := by
  unfold addr
  have he : (fun j => (if addrBitVar (m := m) k j ∈ blockS k then wit k c (addrBitVar k j)
      else outG hb g (addrBitVar k j))) = (e b).symm c := by
    funext j
    rw [if_pos (addrBitVar_mem k j)]
    exact wit_addrBitVar k c j
  rw [he, Equiv.apply_symm_apply]

/-! ## The pair-encoding fooling family -/

/-- Block `k'` addresses its private pair `{2k', 2k'+1}` according to the bit `s k'`. -/
def gPair (hbig : 2 * m ≤ Dsize b) (s : Fin m → Bool) (k' : Fin m) : Fin (Dsize b) :=
  ⟨2 * k'.val + (if s k' then 1 else 0), by
    have h1 := k'.isLt
    have h2 : (if s k' then 1 else 0) ≤ 1 := by split <;> omega
    omega⟩

theorem gPair_val (hbig : 2 * m ≤ Dsize b) (s : Fin m → Bool) (k' : Fin m) :
    (gPair hbig s k').val = 2 * k'.val + (if s k' then 1 else 0) := rfl

/-- Distinct blocks get distinct pair-addresses (private pairs). -/
theorem gPair_injective (hbig : 2 * m ≤ Dsize b) (s : Fin m → Bool) :
    Function.Injective (gPair hbig s) := by
  intro k1 k2 h
  have hv : 2 * k1.val + (if s k1 then (1 : ℕ) else 0) = 2 * k2.val + (if s k2 then 1 else 0) := by
    simpa [gPair] using congrArg Fin.val h
  have hf : (if s k1 then (1 : ℕ) else 0) ≤ 1 := by split <;> omega
  have hg : (if s k2 then (1 : ℕ) else 0) ≤ 1 := by split <;> omega
  exact Fin.ext (by omega)

/-- Two pair-addresses coincide only when both the block and the chosen bit agree. -/
theorem gPair_eq (hbig : 2 * m ≤ Dsize b) (s s' : Fin m → Bool) (k1 k2 : Fin m)
    (h : gPair hbig s k1 = gPair hbig s' k2) : k1 = k2 ∧ s k1 = s' k2 := by
  have hv : 2 * k1.val + (if s k1 then (1 : ℕ) else 0) = 2 * k2.val + (if s' k2 then 1 else 0) := by
    simpa [gPair] using congrArg Fin.val h
  have hf : (if s k1 then (1 : ℕ) else 0) ≤ 1 := by split <;> omega
  have hg : (if s' k2 then (1 : ℕ) else 0) ≤ 1 := by split <;> omega
  have hkv : k1.val = k2.val := by omega
  refine ⟨Fin.ext hkv, ?_⟩
  by_contra hcon
  have hbit : (if s k1 then (1 : ℕ) else 0) = (if s' k2 then 1 else 0) := by omega
  rcases Bool.eq_false_or_eq_true (s k1) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (s' k2) with h2 | h2 <;>
    simp_all

/-! ## The two merge values -/

/-- **Collision.**  Probing block `k` with the same address block `k''` uses (`k''` reads its own address),
so `edFun` is `false`. -/
theorem ed_collision (hb : 0 < b) (hbig : 2 * m ≤ Dsize b) (k k'' : Fin m) (hk'' : k'' ≠ k)
    (s : Fin m → Bool) :
    edFun (fun i => if i ∈ blockS k then wit k (gPair hbig s k'') i else outG hb (gPair hbig s) i)
      = false := by
  unfold edFun
  rw [decide_eq_false_iff_not]
  intro hall
  have h1 : addr (fun i => if i ∈ blockS k then wit k (gPair hbig s k'') i else outG hb (gPair hbig s) i) k
      = gPair hbig s k'' := addr_wit_combined hb (gPair hbig s) k (gPair hbig s k'')
  have h2 : addr (fun i => if i ∈ blockS k then wit k (gPair hbig s k'') i else outG hb (gPair hbig s) i) k''
      = gPair hbig s k'' := addr_outG_combined hb (gPair hbig s) k (gPair hbig s k'') k'' hk''
  exact hall k k'' (Ne.symm hk'') (by rw [h1, h2])

/-- **All distinct.**  Probing block `k` (address `gPair s k''`) against the *other* family `gPair s'`, when
`s k'' ≠ s' k''`, keeps every pair distinct, so `edFun` is `true`. -/
theorem ed_all_distinct (hb : 0 < b) (hbig : 2 * m ≤ Dsize b) (k k'' : Fin m) (hk'' : k'' ≠ k)
    (s s' : Fin m → Bool) (hs : s k'' ≠ s' k'') :
    edFun (fun i => if i ∈ blockS k then wit k (gPair hbig s k'') i else outG hb (gPair hbig s') i)
      = true := by
  unfold edFun
  rw [decide_eq_true_eq]
  set M : Fin (nn b m) → Bool :=
    (fun i => if i ∈ blockS k then wit k (gPair hbig s k'') i else outG hb (gPair hbig s') i) with hM
  have hself : addr M k = gPair hbig s k'' := addr_wit_combined hb (gPair hbig s') k (gPair hbig s k'')
  have hother : ∀ k' : Fin m, k' ≠ k → addr M k' = gPair hbig s' k' := fun k' hk' =>
    addr_outG_combined hb (gPair hbig s') k (gPair hbig s k'') k' hk'
  -- gPair s k'' differs from every gPair s' k' (k' ≠ k)
  have hne : ∀ k' : Fin m, k' ≠ k → gPair hbig s k'' ≠ gPair hbig s' k' := by
    intro k' _ heq
    obtain ⟨hkk, hss⟩ := gPair_eq hbig s s' k'' k' heq
    subst hkk
    exact hs hss
  intro k1 k2 hk12
  by_cases h1 : k1 = k
  · subst h1
    rw [hself, hother k2 (Ne.symm hk12)]
    exact hne k2 (Ne.symm hk12)
  · by_cases h2 : k2 = k
    · subst h2
      rw [hself, hother k1 h1]
      exact fun h => hne k1 h1 h.symm
    · rw [hother k1 h1, hother k2 h2]
      exact fun h => hk12 (gPair_injective hbig s' h)

/-! ## The parameter-family count -/

/-- `#{s : Fin m → Bool | s k = false} = 2^{m−1}` (fix one coordinate). -/
theorem filter_sk_false_card (hm : 0 < m) (k : Fin m) :
    (Finset.univ.filter (fun s : Fin m → Bool => s k = false)).card = 2 ^ (m - 1) := by
  classical
  have hbij : (Finset.univ.filter (fun s : Fin m → Bool => s k = false)).card
            = (Finset.univ.filter (fun s : Fin m → Bool => s k = true)).card := by
    apply Finset.card_bij'
      (fun (a : Fin m → Bool) _ => Function.update a k true)
      (fun (a : Fin m → Bool) _ => Function.update a k false)
    · intro a _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Function.update_self]⟩
    · intro a _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Function.update_self]⟩
    · intro a ha
      have ha2 : a k = false := (Finset.mem_filter.mp ha).2
      funext x; by_cases hx : x = k
      · subst hx; rw [Function.update_self]; exact ha2.symm
      · rw [Function.update_of_ne hx, Function.update_of_ne hx]
    · intro a ha
      have ha2 : a k = true := (Finset.mem_filter.mp ha).2
      funext x; by_cases hx : x = k
      · subst hx; rw [Function.update_self]; exact ha2.symm
      · rw [Function.update_of_ne hx, Function.update_of_ne hx]
  have hadd := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → Bool)))
    (fun s : Fin m → Bool => s k = false)
  have hneg : (Finset.univ.filter (fun s : Fin m → Bool => ¬ s k = false))
            = (Finset.univ.filter (fun s : Fin m → Bool => s k = true)) := by
    apply Finset.filter_congr
    intro t _
    cases h : t k <;> simp [h]
  have huniv : (Finset.univ : Finset (Fin m → Bool)).card = 2 ^ m := by
    rw [Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool]
  have hpow : (2 : ℕ) ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 from by omega]
    rw [pow_succ]; ring
  rw [hneg, ← hbij, huniv] at hadd
  omega

/-! ## The per-block rung -/

/-- **`2^{m−1}` distinct residuals per address block.**  The pair-encoded settings inject into the block's
residuals: distinct bit-vectors give distinct set-indicator residuals. -/
theorem card_blockResiduals_ed_ge (hb : 0 < b) (hbig : 2 * m ≤ Dsize b) (k : Fin m)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = edFun x) :
    (Finset.univ.filter (fun s : Fin m → Bool => s k = false)).card
      ≤ (blockResiduals (blockS k) F).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun s => (fun x => BFormula.eval F
      (fun i => if i ∈ blockS k then x i else outG hb (gPair hbig s) i)))
    ?_ ?_
  · intro s _
    exact Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨outG hb (gPair hbig s), Finset.mem_univ _, rfl⟩)
  · intro s hs s' hs' hgt
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hs hs'
    by_contra hne
    obtain ⟨k'', hk''⟩ : ∃ k'', s k'' ≠ s' k'' := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hk''k : k'' ≠ k := by
      intro h; subst h; rw [hs, hs'] at hk''; exact hk'' rfl
    have hval := congrFun hgt (wit k (gPair hbig s k''))
    dsimp only at hval
    rw [hF, hF, ed_collision hb hbig k k'' hk''k s,
      ed_all_distinct hb hbig k k'' hk''k s s' hk''] at hval
    exact absurd hval (by decide)

/-- **The address-block rung for element distinctness.**  Every address block forces boundary `≥ m − 1`. -/
theorem ed_blockBoundary_ge (hb : 0 < b) (hbig : 2 * m ≤ Dsize b) (hm : 0 < m) (k : Fin m)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = edFun x) :
    m - 1 ≤ formulaBlockBoundary (blockS k) F := by
  have h1 : 2 ^ (m - 1) ≤ (blockResiduals (blockS k) F).card := by
    rw [← filter_sk_false_card hm k]
    exact card_blockResiduals_ed_ge hb hbig k F hF
  unfold formulaBlockBoundary
  calc m - 1 = Nat.log 2 (2 ^ (m - 1)) := (Nat.log_pow (by norm_num) _).symm
    _ ≤ Nat.log 2 ((blockResiduals (blockS k) F).card) := Nat.log_mono_right h1

/-- **The min over the structured address-block class forces boundary `≥ m − 1` for `edFun` too.**  A second,
structurally different explicit hard family clears the Nečiporuk rung — via a subset/fooling family, not a
data-table one. -/
theorem ed_minBlockBoundary_ge (hb : 0 < b) (hbig : 2 * m ≤ Dsize b) (hm : 0 < m)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = edFun x) :
    m - 1 ≤ minBlockBoundary hm F := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  unfold minBlockBoundary
  apply Finset.le_inf'
  intro k _
  exact ed_blockBoundary_ge hb hbig hm k F hF

/-! ## The explicit formula-size lower bound -/

/-- **Nečiporuk formula-size lower bound for element distinctness.**  Summing the per-block bound
`m − 1` over the `m` address blocks (the data block contributes `≥ 0`) and plugging into the general
Nečiporuk bound `neciporuk_formula_lower_bound` gives, for any `B₂` formula `F` computing `edFun`,
`m·(m − 1) ≤ 2·clog₂(|Tok|+1)·litCount F + 2·(m + 1)`.  With `m ≈ 2^{b-1}` this is quadratic in the
number of blocks (super-linear in the input length `nn ≈ 2^b`). -/
theorem ed_litCount_lower (hb : 0 < b) (hbig : 2 * m ≤ Dsize b) (hm : 0 < m)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = edFun x) :
    m * (m - 1) ≤
      2 * Nat.clog 2 (Fintype.card (NF.Tok (nn b m)) + 1) * BFormula.litCount F
        + 2 * (m + 1) := by
  classical
  have hnec := neciporuk_formula_lower_bound
    (Finset.univ : Finset (Option (Fin m))) (blkS (b := b) (m := m)) F blkS_disj blkS_cover
  rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin] at hnec
  have hconst : ∑ _k : Fin m, (m - 1) = m * (m - 1) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hper : ∀ k : Fin m,
      m - 1 ≤ Nat.log 2 ((blockResiduals (blkS (some k)) F).card) := by
    intro k
    rw [blkS_some]
    exact ed_blockBoundary_ge hb hbig hm k F hF
  have hge : m * (m - 1)
      ≤ ∑ k : Fin m, Nat.log 2 ((blockResiduals (blkS (some k)) F).card) :=
    hconst ▸ Finset.sum_le_sum (fun k _ => hper k)
  have hlow : m * (m - 1)
      ≤ ∑ o : Option (Fin m), Nat.log 2 ((blockResiduals (blkS o) F).card) := by
    rw [Fintype.sum_option]
    exact le_trans hge (Nat.le_add_left _ _)
  exact le_trans hlow hnec

end PallLean.Paper93.DeepMath.PathB.NecHardED

#print axioms PallLean.Paper93.DeepMath.PathB.NecHardED.ed_collision
#print axioms PallLean.Paper93.DeepMath.PathB.NecHardED.ed_all_distinct
#print axioms PallLean.Paper93.DeepMath.PathB.NecHardED.ed_blockBoundary_ge
#print axioms PallLean.Paper93.DeepMath.PathB.NecHardED.ed_minBlockBoundary_ge
#print axioms PallLean.Paper93.DeepMath.PathB.NecHardED.ed_litCount_lower
