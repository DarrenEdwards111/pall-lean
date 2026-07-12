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

/-! ## Formula-size asymptotic wrappers (super-linear) -/

/-- Explicit clog form of the OR-multiplexer formula-size bound (alphabet count resolved via `NF.card_Tok_eq`). -/
theorem orMux_litCount_lower_explicit {b m : ℕ} (F : BFormula (nn b m))
    (hF : ∀ x, BFormula.eval F x = orMux x) :
    m * (Dsize b - 1) ≤
      2 * Nat.clog 2 (2 * nn b m + 17) * BFormula.litCount F + 2 * (m + 1) := by
  have h := orMux_litCount_lower F hF
  rwa [NF.card_Tok_eq, show 16 + 2 * nn b m + 1 = 2 * nn b m + 17 from by ring] at h

/-- **`orMux` has super-linear formula size.**  For every `C` there is a `b` such that any `B₂` formula computing
`orMux` on the balanced family (`m = 2^b`, `N = 2^b·(b+1)` variables) has more than `C·N` literals. -/
theorem orMux_superlinear (C : ℕ) :
    ∃ b : ℕ, ∀ (F : BFormula (nn b (2 ^ b))),
      (∀ x, BFormula.eval F x = orMux x) →
      C * nn b (2 ^ b) < BFormula.litCount F := by
  obtain ⟨b, hb5, hbig⟩ := expBeatsQuad (8 * C + 4)
  refine ⟨b, fun F hF => ?_⟩
  have hdb : Dsize b = 2 ^ b := dsize_eq
  have hN : nn b (2 ^ b) = 2 ^ b * (b + 1) := by unfold nn; rw [hdb]; ring
  have hpb32 : (32 : ℕ) ≤ 2 ^ b := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb5
  have hclog : Nat.clog 2 (2 * nn b (2 ^ b) + 17) ≤ 2 * b := by
    apply Nat.clog_le_of_le_pow
    rw [hN, show (2 : ℕ) ^ (2 * b) = 2 ^ b * 2 ^ b from by rw [two_mul, pow_add]]
    have h4b2 : 4 * b ^ 2 < 2 ^ b := by nlinarith [hbig, Nat.zero_le (C * b ^ 2)]
    have h5b : 5 * b ≤ b ^ 2 := by nlinarith [hb5]
    have h2b3 : 2 * b + 3 ≤ 2 ^ b := by nlinarith [h4b2, h5b, hb5]
    have hmul : 2 ^ b * (2 * b + 3) ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul_left _ h2b3
    nlinarith [hmul, hpb32]
  have hexp := orMux_litCount_lower_explicit (b := b) (m := 2 ^ b) F hF
  rw [hdb] at hexp
  have hcL : 2 * Nat.clog 2 (2 * nn b (2 ^ b) + 17) * BFormula.litCount F
        ≤ 4 * b * BFormula.litCount F := by
    have hle : 2 * Nat.clog 2 (2 * nn b (2 ^ b) + 17) ≤ 4 * b := by omega
    exact Nat.mul_le_mul hle (le_refl _)
  have hexpB : 2 ^ b * (2 ^ b - 1) ≤ 4 * b * BFormula.litCount F + 2 * (2 ^ b + 1) := by omega
  have hid : 2 ^ b * (2 ^ b - 1) + 2 ^ b = 2 ^ b * 2 ^ b := by
    have h1 : 2 ^ b - 1 + 1 = 2 ^ b := Nat.succ_pred_eq_of_pos (by positivity)
    calc 2 ^ b * (2 ^ b - 1) + 2 ^ b
        = 2 ^ b * (2 ^ b - 1) + 2 ^ b * 1 := by ring
      _ = 2 ^ b * (2 ^ b - 1 + 1) := by rw [Nat.mul_add]
      _ = 2 ^ b * 2 ^ b := by rw [h1]
  have hexpC : 2 ^ b * 2 ^ b
        ≤ 4 * b * BFormula.litCount F + 2 * (2 ^ b + 1) + 2 ^ b := by omega
  have hbb : b ≤ b ^ 2 := by nlinarith [hb5]
  have hQbig : 4 * C * b * (b + 1) + 4 ≤ 2 ^ b := by
    have key : 4 * C * b * (b + 1) + 4 ≤ (8 * C + 4) * b ^ 2 := by
      nlinarith [hbb, hb5, Nat.zero_le C]
    omega
  have hprod : (4 * C * b * (b + 1) + 4) * 2 ^ b ≤ 2 ^ b * 2 ^ b :=
    Nat.mul_le_mul hQbig (le_refl _)
  have hgoaleq : C * nn b (2 ^ b) = C * (2 ^ b * (b + 1)) := by rw [hN]
  rw [hgoaleq]
  have hbig2 : 4 * b * (C * (2 ^ b * (b + 1))) < 4 * b * BFormula.litCount F := by
    nlinarith [hexpC, hprod, hpb32]
  exact lt_of_mul_lt_mul_left hbig2 (Nat.zero_le _)

/-- Explicit clog form of the element-distinctness formula-size bound. -/
theorem ed_litCount_lower_explicit {b m : ℕ} (hb : 0 < b) (hbig : 2 * m ≤ Dsize b) (hm : 0 < m)
    (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = edFun x) :
    m * (m - 1) ≤
      2 * Nat.clog 2 (2 * nn b m + 17) * BFormula.litCount F + 2 * (m + 1) := by
  have h := ed_litCount_lower hb hbig hm F hF
  rwa [NF.card_Tok_eq, show 16 + 2 * nn b m + 1 = 2 * nn b m + 17 from by ring] at h

/-- **`edFun` has super-linear formula size.**  For every `C` there is a `b` such that any `B₂` formula computing
`edFun` on the pair-encoding balanced family (`m = 2^{b-1}`, `N = 2^{b-1}·(b+2)` variables) has more than `C·N`
literals. -/
theorem edFun_superlinear (C : ℕ) :
    ∃ c : ℕ, ∀ (F : BFormula (nn (c + 1) (2 ^ c))),
      (∀ x, BFormula.eval F x = edFun x) →
      C * nn (c + 1) (2 ^ c) < BFormula.litCount F := by
  obtain ⟨c, hc5, hcbig⟩ := expBeatsQuad (32 * C + 4)
  refine ⟨c, fun F hF => ?_⟩
  have hMpos : 0 < 2 ^ c := by positivity
  have hdb : Dsize (c + 1) = 2 * 2 ^ c := by rw [dsize_eq, pow_succ]; ring
  have hN : nn (c + 1) (2 ^ c) = 2 ^ c * (c + 3) := by unfold nn; rw [hdb]; ring
  have hb : 0 < c + 1 := by omega
  have hbig : 2 * 2 ^ c ≤ Dsize (c + 1) := by rw [hdb]
  have hc32 : (32 : ℕ) ≤ 2 ^ c := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) hc5
  have h4c : 4 * c ^ 2 < 2 ^ c := by nlinarith [hcbig, Nat.zero_le C, sq_nonneg c]
  -- clog(2N+17) ≤ 2c+2
  have hclog : Nat.clog 2 (2 * nn (c + 1) (2 ^ c) + 17) ≤ 2 * c + 2 := by
    apply Nat.clog_le_of_le_pow
    have hpow : (2 : ℕ) ^ (2 * c + 2) = 4 * (2 ^ c) ^ 2 := by
      rw [pow_add, mul_comm 2 c, pow_mul]; ring
    rw [hN, hpow]
    nlinarith [h4c, hc5, hMpos]
  -- the explicit bound with m = 2^c and multiplier 4(c+1)
  have hexp := ed_litCount_lower_explicit hb hbig hMpos F hF
  have hcL : 2 * Nat.clog 2 (2 * nn (c + 1) (2 ^ c) + 17) * BFormula.litCount F
        ≤ 4 * (c + 1) * BFormula.litCount F := by
    have hle : 2 * Nat.clog 2 (2 * nn (c + 1) (2 ^ c) + 17) ≤ 4 * (c + 1) := by omega
    exact Nat.mul_le_mul hle (le_refl _)
  have hexpB : 2 ^ c * (2 ^ c - 1)
        ≤ 4 * (c + 1) * BFormula.litCount F + 2 * (2 ^ c + 1) :=
    le_trans hexp (Nat.add_le_add_right hcL _)
  have hid : 2 ^ c * (2 ^ c - 1) + 2 ^ c = 2 ^ c * 2 ^ c := by
    have h1 : 2 ^ c - 1 + 1 = 2 ^ c := Nat.succ_pred_eq_of_pos hMpos
    calc 2 ^ c * (2 ^ c - 1) + 2 ^ c = 2 ^ c * (2 ^ c - 1) + 2 ^ c * 1 := by ring
      _ = 2 ^ c * (2 ^ c - 1 + 1) := by rw [Nat.mul_add]
      _ = 2 ^ c * 2 ^ c := by rw [h1]
  have hexpC : 2 ^ c * 2 ^ c
        ≤ 4 * (c + 1) * BFormula.litCount F + 2 * (2 ^ c + 1) + 2 ^ c := by
    rw [← hid]
    exact Nat.add_le_add_right hexpB _
  -- 2^c dominates the quadratic quantity 4(c+1)C(c+3)
  have hQbig : 4 * (c + 1) * C * (c + 3) + 4 ≤ 2 ^ c := by
    have hcc : (c + 1) * (c + 3) ≤ 8 * c ^ 2 := by nlinarith [hc5]
    have h4 : (4 : ℕ) ≤ 4 * c ^ 2 := by nlinarith [hc5]
    have key : 4 * (c + 1) * C * (c + 3) + 4 ≤ (32 * C + 4) * c ^ 2 := by
      calc 4 * (c + 1) * C * (c + 3) + 4
          = 4 * C * ((c + 1) * (c + 3)) + 4 := by ring
        _ ≤ 4 * C * (8 * c ^ 2) + 4 * c ^ 2 :=
            Nat.add_le_add (Nat.mul_le_mul (le_refl (4 * C)) hcc) h4
        _ = (32 * C + 4) * c ^ 2 := by ring
    omega
  have hprod : (4 * (c + 1) * C * (c + 3) + 4) * 2 ^ c ≤ 2 ^ c * 2 ^ c :=
    Nat.mul_le_mul hQbig (le_refl _)
  have hgoaleq : C * nn (c + 1) (2 ^ c) = C * (2 ^ c * (c + 3)) := by rw [hN]
  rw [hgoaleq]
  have hbig2 : 4 * (c + 1) * (C * (2 ^ c * (c + 3))) < 4 * (c + 1) * BFormula.litCount F := by
    nlinarith [hexpC, hprod, hc32]
  exact lt_of_mul_lt_mul_left hbig2 (Nat.zero_le _)

/-! ## Asymptotic wrappers: the width is unbounded (exponential) -/

/-- **`hardF` has unbounded oblivious-BP width.**  For every constant `C` there is a depth parameter `b` such
that *any* oblivious width-`w` leveled BP computing `hardF` (reading its address block contiguously) has `w > C`.
So the width is not `O(1)` — in fact `w ≥ (2^b − 1)/2`, exponential in `b`. -/
theorem hardF_bp_width_unbounded (C : ℕ) :
    ∃ b : ℕ, ∀ (w : ℕ) (P : LevBP (nn b 1) w),
      (∀ x, P.eval x = hardF x) → ∀ (a s : ℕ), a + s ≤ P.len →
      (∀ ℓ, ℓ < P.len → (P.var ℓ ∈ blockS (0 : Fin 1) ↔ a ≤ ℓ ∧ ℓ < a + s)) →
      C < w := by
  refine ⟨C + 2, fun w P hP a s has hblock => ?_⟩
  have h := hardF_bp_width_ge (0 : Fin 1) P hP a s has hblock
  rw [dsize_eq] at h
  have hc : C < 2 ^ C := Nat.lt_two_pow_self
  have he : (2 : ℕ) ^ (C + 2) = 4 * 2 ^ C := by rw [pow_add]; ring
  omega

/-- **`orMux` has unbounded oblivious-BP width** (exponential), by the same argument. -/
theorem orMux_bp_width_unbounded (C : ℕ) :
    ∃ b : ℕ, ∀ (w : ℕ) (P : LevBP (nn b 1) w),
      (∀ x, P.eval x = orMux x) → ∀ (a s : ℕ), a + s ≤ P.len →
      (∀ ℓ, ℓ < P.len → (P.var ℓ ∈ blockS (0 : Fin 1) ↔ a ≤ ℓ ∧ ℓ < a + s)) →
      C < w := by
  refine ⟨C + 2, fun w P hP a s has hblock => ?_⟩
  have h := orMux_bp_width_ge (0 : Fin 1) P hP a s has hblock
  rw [dsize_eq] at h
  have hc : C < 2 ^ C := Nat.lt_two_pow_self
  have he : (2 : ℕ) ^ (C + 2) = 4 * 2 ^ C := by rw [pow_add]; ring
  omega

/-- **`edFun` has unbounded oblivious-BP width** (exponential), via the pair-encoding family `m = 2^{b-1}`. -/
theorem edFun_bp_width_unbounded (C : ℕ) :
    ∃ b m : ℕ, 0 < m ∧ ∀ (w : ℕ) (k : Fin m) (P : LevBP (nn b m) w),
      (∀ x, P.eval x = edFun x) → ∀ (a s : ℕ), a + s ≤ P.len →
      (∀ ℓ, ℓ < P.len → (P.var ℓ ∈ blockS k ↔ a ≤ ℓ ∧ ℓ < a + s)) →
      C < w := by
  refine ⟨C + 2, 2 ^ (C + 1), by positivity, fun w k P hP a s has hblock => ?_⟩
  have hb : 0 < C + 2 := by omega
  have hbig : 2 * 2 ^ (C + 1) ≤ Dsize (C + 2) := by
    have h1 : Dsize (C + 2) = 2 ^ (C + 2) := dsize_eq
    have h2 : (2 : ℕ) ^ (C + 2) = 2 * 2 ^ (C + 1) := by rw [pow_succ]; ring
    omega
  have hm : 0 < 2 ^ (C + 1) := by positivity
  have h := edFun_bp_width_ge hb hbig hm k P hP a s has hblock
  have hc : C < 2 ^ C := Nat.lt_two_pow_self
  have he : (2 : ℕ) ^ (C + 1) = 2 * 2 ^ C := by rw [pow_succ]; ring
  omega

end PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies

#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies.orMux_bp_width_ge
#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies.hardF_bp_width_unbounded
#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies.edFun_bp_width_unbounded
#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies.edFun_bp_width_ge
#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies.orMux_superlinear
#print axioms PallLean.Paper93.DeepMath.PathB.BranchingProgramFamilies.edFun_superlinear
