import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunction

/-!
# Nečiporuk concrete hard function (Stage 2): the explicit super-linear formula-size lower bound

Stage 1 (`ComputationalDepthNeciporukHardFunction`) built the multi-block shared-data lookup `hardF`
and the per-block subfunction count `(filter (· c0 = false)).card ≤ #blockResiduals(blockS k, F)`.
This file finishes the wiring:

* `filter_c0_false_card` — the parameter family count: `#{t : t c0 = false} = 2^{2^b − 1}` (one
  coordinate fixed; the two halves are equinumerous via a flip at `c0`).
* `log_card_blockResiduals_hardF_ge` — hence `log₂ #blockResiduals(blockS k, F) ≥ 2^b − 1`.
* `blkS` — the variable partition of `Fin nn` into `m` address blocks + a data block (the complement),
  indexed by `Option (Fin m)`; `blkS_disj`/`blkS_cover` discharge the partition hypotheses.
* `hardF_litCount_lower` — plugging into `neciporuk_formula_lower_bound`:
      `m·(2^b − 1) ≤ 2·clog₂(|Tok|+1)·litCount F + 2·(m + 1)`
  for **any** B₂ formula `F` computing `hardF` — a genuine, fully proved Nečiporuk formula-size lower
  bound for an explicit function.

Choosing `b ≈ log₂ m` and `m ≈ n / b` makes the data region `2^b ≈ m` and `nn ≈ 2 m·b ≈ n`, giving
`litCount F ≳ m·2^b / log n ≈ n² / log² n`.  Honest ceiling: `n²/log²n` formula size (classic
Nečiporuk), **not** P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace NecHard

open scoped BigOperators

variable {b m : ℕ}

/-- The data region has exactly `2^b` cells. -/
theorem dsize_eq : Dsize b = 2 ^ b := by
  show Fintype.card (Fin b → Bool) = 2 ^ b
  rw [Fintype.card_pi_const, Fintype.card_bool]

/-! ## The parameter-family count: `#{t : t c0 = false} = 2^{2^b − 1}` -/

/-- **One coordinate fixed halves the cube.**  The number of data tables with the reserved cell
`false` is `2^{2^b − 1}`: a flip at `c0` bijects `{t c0 = false}` with `{t c0 = true}`, and the two
exhaust the `2^{2^b}` tables. -/
theorem filter_c0_false_card :
    (Finset.univ.filter (fun t : Fin (Dsize b) → Bool => t c0 = false)).card
      = 2 ^ (Dsize b - 1) := by
  classical
  -- |{t c0 = false}| = |{t c0 = true}| via the flip at c0.
  have hbij : (Finset.univ.filter (fun t : Fin (Dsize b) → Bool => t c0 = false)).card
            = (Finset.univ.filter (fun t : Fin (Dsize b) → Bool => t c0 = true)).card := by
    apply Finset.card_bij'
      (fun (a : Fin (Dsize b) → Bool) _ => Function.update a c0 true)
      (fun (a : Fin (Dsize b) → Bool) _ => Function.update a c0 false)
    · intro a _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Function.update_self]⟩
    · intro a _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [Function.update_self]⟩
    · intro a ha
      have ha2 : a c0 = false := (Finset.mem_filter.mp ha).2
      funext x; by_cases hx : x = c0
      · subst hx; rw [Function.update_self]; exact ha2.symm
      · rw [Function.update_of_ne hx, Function.update_of_ne hx]
    · intro a ha
      have ha2 : a c0 = true := (Finset.mem_filter.mp ha).2
      funext x; by_cases hx : x = c0
      · subst hx; rw [Function.update_self]; exact ha2.symm
      · rw [Function.update_of_ne hx, Function.update_of_ne hx]
  -- the two halves exhaust all 2^(2^b) tables.
  have hadd := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (Dsize b) → Bool)))
    (fun t : Fin (Dsize b) → Bool => t c0 = false)
  have hneg : (Finset.univ.filter (fun t : Fin (Dsize b) → Bool => ¬ t c0 = false))
            = (Finset.univ.filter (fun t : Fin (Dsize b) → Bool => t c0 = true)) := by
    apply Finset.filter_congr
    intro t _
    cases h : t c0 <;> simp [h]
  have huniv : (Finset.univ : Finset (Fin (Dsize b) → Bool)).card = 2 ^ Dsize b := by
    rw [Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool]
  have hpow : (2 : ℕ) ^ Dsize b = 2 * 2 ^ (Dsize b - 1) := by
    have hpos : 0 < Dsize b := Fintype.card_pos
    conv_lhs => rw [show Dsize b = (Dsize b - 1) + 1 from by omega]
    rw [pow_succ]; ring
  rw [hneg, ← hbij, huniv] at hadd
  omega

/-! ## The per-block log bound -/

/-- **`log₂ #blockResiduals(blockS k) ≥ 2^b − 1`.**  Each address block of the explicit function has
at least `2^{2^b − 1}` distinct subfunctions, so its log-count is at least `2^b − 1`. -/
theorem log_card_blockResiduals_hardF_ge (k : Fin m) (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
    Dsize b - 1 ≤ Nat.log 2 ((blockResiduals (blockS k) F).card) := by
  have h1 : 2 ^ (Dsize b - 1) ≤ (blockResiduals (blockS k) F).card := by
    rw [← filter_c0_false_card]
    exact card_blockResiduals_hardF_ge k F hF
  calc Dsize b - 1 = Nat.log 2 (2 ^ (Dsize b - 1)) := (Nat.log_pow (by norm_num) _).symm
    _ ≤ Nat.log 2 ((blockResiduals (blockS k) F).card) := Nat.log_mono_right h1

/-! ## The variable partition: `m` address blocks + the data block (their complement) -/

/-- The data block: every variable not in any address block. -/
noncomputable def dataBlk : Finset (Fin (nn b m)) :=
  Finset.univ \ Finset.univ.biUnion (fun k : Fin m => blockS k)

/-- The partition of `Fin nn`, indexed by `Option (Fin m)`: `some k ↦ blockS k`, `none ↦ dataBlk`. -/
noncomputable def blkS (o : Option (Fin m)) : Finset (Fin (nn b m)) :=
  o.elim dataBlk blockS

@[simp] theorem blkS_some (k : Fin m) : blkS (b := b) (some k) = blockS k := rfl
@[simp] theorem blkS_none : blkS (b := b) (m := m) none = dataBlk := rfl

/-- **The blocks cover all variables.**  Every variable is either in some address block or, by
construction, in the data block (the complement). -/
theorem blkS_cover :
    (Finset.univ : Finset (Option (Fin m))).biUnion (blkS (b := b)) = Finset.univ := by
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  intro i _
  rw [Finset.mem_biUnion]
  by_cases h : i ∈ Finset.univ.biUnion (fun k : Fin m => blockS k)
  · rw [Finset.mem_biUnion] at h
    obtain ⟨k, _, hk⟩ := h
    exact ⟨some k, Finset.mem_univ _, hk⟩
  · refine ⟨none, Finset.mem_univ _, ?_⟩
    rw [blkS_none, dataBlk]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩

/-- **The blocks are pairwise disjoint.**  Distinct address blocks are disjoint
(`addrBitVar_ne_mem`); each address block is disjoint from the data block (its complement). -/
theorem blkS_disj :
    ((Finset.univ : Finset (Option (Fin m))) : Set (Option (Fin m))).PairwiseDisjoint
      (blkS (b := b) (m := m)) := by
  intro o _ o' _ hne
  rcases o with _ | k <;> rcases o' with _ | k'
  · exact absurd rfl hne
  · show Disjoint dataBlk (blockS k')
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [dataBlk] at hi
    exact (Finset.mem_sdiff.mp hi).2
      (Finset.mem_biUnion.mpr ⟨k', Finset.mem_univ _, hi'⟩)
  · show Disjoint (blockS k) dataBlk
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [dataBlk] at hi'
    exact (Finset.mem_sdiff.mp hi').2
      (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hi⟩)
  · show Disjoint (blockS k) (blockS k')
    rw [Finset.disjoint_left]
    intro i hi hi'
    obtain ⟨j', _, hj'⟩ := Finset.mem_image.mp hi'
    have hkk : k ≠ k' := fun h => hne (congrArg some h)
    rw [← hj'] at hi
    exact addrBitVar_ne_mem (Ne.symm hkk) j' hi

/-! ## The explicit super-linear formula-size lower bound -/

/-- **Nečiporuk lower bound for the explicit function.**  For any `B₂` formula `F` computing `hardF`,
  `m·(2^b − 1) ≤ 2·clog₂(|Tok|+1)·litCount F + 2·(m + 1)`.
Summing the per-block bound `log₂ #blockResiduals(blockS k) ≥ 2^b − 1` over the `m` address blocks
(the data block contributes `≥ 0`) and plugging into `neciporuk_formula_lower_bound`. -/
theorem hardF_litCount_lower (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = hardF x) :
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
    exact log_card_blockResiduals_hardF_ge k F hF
  have hge : m * (Dsize b - 1)
      ≤ ∑ k : Fin m, Nat.log 2 ((blockResiduals (blkS (some k)) F).card) :=
    hconst ▸ Finset.sum_le_sum (fun k _ => hper k)
  have hlow : m * (Dsize b - 1)
      ≤ ∑ o : Option (Fin m), Nat.log 2 ((blockResiduals (blkS o) F).card) := by
    rw [Fintype.sum_option]
    exact le_trans hge (Nat.le_add_left _ _)
  exact le_trans hlow hnec

end NecHard

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.filter_c0_false_card
#print axioms PallLean.Paper93.DeepMath.PathB.NecHard.hardF_litCount_lower
