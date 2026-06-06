import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukBranching

/-!
# The constant-per-leaf subfunction bound: `s_i ≤ 2·16^{leavesIn(S)}`

Assembling the contraction (`SpineContraction`) and the branching bound (`Branching`) under the
invariant `4·|Qset F| ≤ 4^{2·leavesIn(S,F)}` (for `leavesIn ≥ 1`) gives the genuine **constant**
per-leaf bound — no `log n` factor:

  `card (blockResiduals S F) ≤ 2 · 16^{leavesIn S F}`.

This is the bound underlying the *optimal* Nečiporuk `n²/log n` (the previous formalisation charged
`clog₂(|Tok n|) ≈ log n` bits per leaf; this charges a constant `4`).

* `Qset_card_lit_le_four` — `|Qset (lit i∈S b)| ≤ 4` (residuals factor through coordinate `i`).
* `Qset_card_le_pow` — `1 ≤ leavesIn S F ⇒ 4·|Qset F| ≤ 4^{2·leavesIn S F}` (induction: contraction
  preserves it on pass-through nodes, branching preserves it via `4·4^{2ℓa}/4 · 4^{2ℓb}/4 = 4^{2ℓ}/4`).
* `card_blockResiduals_le_pow` — `s_i ≤ 2·16^{leavesIn S F}`, i.e. `log₂ s_i ≤ 1 + 4·leavesIn`.

The last remaining piece for `n²/log n` is to rewire `neciporuk_formula_lower_bound` to use this bound
(constant per leaf) instead of the `clog(|Tok|)·leavesIn` charge, then re-derive the `hardF` bound.
-/

namespace PallLean.Paper93.DeepMath.PathB

open BFormula

variable {n : ℕ}

/-- `|Qset (lit i b)| ≤ 4` when `i ∈ S`: every closure element depends on its argument only through
coordinate `i`, hence is one of the 4 functions of one bit. -/
theorem Qset_card_lit_le_four (S : Finset (Fin n)) {i : Fin n} (hi : i ∈ S) (b : Bool) :
    (Qset S (BFormula.lit i b)).card ≤ 4 := by
  classical
  have hfac : ∀ ψ ∈ Qset S (BFormula.lit i b), ∀ x y, x i = y i → ψ x = ψ y := by
    intro ψ hψ x y hxy
    simp only [Qset, Finset.mem_image, Finset.mem_univ, true_and] at hψ
    obtain ⟨⟨h, α⟩, rfl⟩ := hψ
    show h (BFormula.eval (BFormula.lit i b) (fun j => if j ∈ S then x j else α j))
       = h (BFormula.eval (BFormula.lit i b) (fun j => if j ∈ S then y j else α j))
    simp only [BFormula.eval, if_pos hi, hxy]
  have hinj : Set.InjOn (fun ψ : (Fin n → Bool) → Bool => (fun v => ψ (fun _ => v)))
      (Qset S (BFormula.lit i b) : Set _) := by
    intro ψ hψ χ hχ hpq
    simp only [Finset.mem_coe] at hψ hχ
    funext x
    have hψx : ψ x = ψ (fun _ => x i) := hfac ψ hψ x (fun _ => x i) (by simp)
    have hχx : χ x = χ (fun _ => x i) := hfac χ hχ x (fun _ => x i) (by simp)
    rw [hψx, hχx]; exact congrFun hpq (x i)
  calc (Qset S (BFormula.lit i b)).card
      = ((Qset S (BFormula.lit i b)).image (fun ψ => fun v => ψ (fun _ => v))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset (Bool → Bool)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 4 := by decide

/-- **The closing invariant.**  For a block-reading formula, `4·|Qset F| ≤ 4^{2·leavesIn S F}`. -/
theorem Qset_card_le_pow (S : Finset (Fin n)) :
    ∀ (F : BFormula n), 1 ≤ BFormula.leavesIn S F →
      4 * (Qset S F).card ≤ 4 ^ (2 * BFormula.leavesIn S F)
  | BFormula.lit i b, hpos => by
      by_cases hi : i ∈ S
      · have hl : BFormula.leavesIn S (BFormula.lit i b) = 1 := by simp [BFormula.leavesIn, hi]
        calc 4 * (Qset S (BFormula.lit i b)).card
            ≤ 4 * 4 := Nat.mul_le_mul (le_refl 4) (Qset_card_lit_le_four S hi b)
          _ = 4 ^ (2 * 1) := by norm_num
          _ = 4 ^ (2 * BFormula.leavesIn S (BFormula.lit i b)) := by rw [hl]
      · simp only [BFormula.leavesIn, if_neg hi] at hpos; omega
  | BFormula.cst c, hpos => by simp only [BFormula.leavesIn] at hpos; omega
  | BFormula.un u t, hpos => by
      have ht : 1 ≤ BFormula.leavesIn S t := by simpa only [BFormula.leavesIn] using hpos
      calc 4 * (Qset S (BFormula.un u t)).card
          ≤ 4 * (Qset S t).card :=
            Nat.mul_le_mul (le_refl 4) (Finset.card_le_card (Qset_un_subset S u t))
        _ ≤ 4 ^ (2 * BFormula.leavesIn S t) := Qset_card_le_pow S t ht
        _ = 4 ^ (2 * BFormula.leavesIn S (BFormula.un u t)) := rfl
  | BFormula.bin g a b, hpos => by
      rcases Nat.eq_zero_or_pos (BFormula.leavesIn S a) with ha0 | hapos
      · have hbpos : 1 ≤ BFormula.leavesIn S b := by
          simp only [BFormula.leavesIn] at hpos; omega
        calc 4 * (Qset S (BFormula.bin g a b)).card
            ≤ 4 * (Qset S b).card :=
              Nat.mul_le_mul (le_refl 4) (Finset.card_le_card (Qset_bin_left_free S g a b ha0))
          _ ≤ 4 ^ (2 * BFormula.leavesIn S b) := Qset_card_le_pow S b hbpos
          _ = 4 ^ (2 * BFormula.leavesIn S (BFormula.bin g a b)) := by
              congr 1; simp only [BFormula.leavesIn]; omega
      · rcases Nat.eq_zero_or_pos (BFormula.leavesIn S b) with hb0 | hbpos
        · calc 4 * (Qset S (BFormula.bin g a b)).card
              ≤ 4 * (Qset S a).card :=
                Nat.mul_le_mul (le_refl 4) (Finset.card_le_card (Qset_bin_right_free S g a b hb0))
            _ ≤ 4 ^ (2 * BFormula.leavesIn S a) := Qset_card_le_pow S a hapos
            _ = 4 ^ (2 * BFormula.leavesIn S (BFormula.bin g a b)) := by
                congr 1; simp only [BFormula.leavesIn]; omega
        · calc 4 * (Qset S (BFormula.bin g a b)).card
              ≤ 4 * (4 * ((Qset S a).card * (Qset S b).card)) :=
                Nat.mul_le_mul (le_refl 4) (Qset_card_bin_le S g a b)
            _ = (4 * (Qset S a).card) * (4 * (Qset S b).card) := by ring
            _ ≤ 4 ^ (2 * BFormula.leavesIn S a) * 4 ^ (2 * BFormula.leavesIn S b) :=
                Nat.mul_le_mul (Qset_card_le_pow S a hapos) (Qset_card_le_pow S b hbpos)
            _ = 4 ^ (2 * BFormula.leavesIn S (BFormula.bin g a b)) := by
                rw [← pow_add]; congr 1; simp only [BFormula.leavesIn]; ring

/-- **Constant-per-leaf block-subfunction bound.**  `s_i ≤ 2·16^{leavesIn S F}`, i.e.
`log₂ s_i ≤ 1 + 4·leavesIn` — no `log n` factor. -/
theorem card_blockResiduals_le_pow (S : Finset (Fin n)) (F : BFormula n) :
    (blockResiduals S F).card ≤ 2 * 16 ^ (BFormula.leavesIn S F) := by
  rcases Nat.eq_zero_or_pos (BFormula.leavesIn S F) with h0 | hpos
  · calc (blockResiduals S F).card ≤ (Qset S F).card :=
          Finset.card_le_card (blockResiduals_subset_Qset S F)
      _ ≤ 2 := Qset_card_le_two_of_leavesIn_zero h0
      _ = 2 * 16 ^ (BFormula.leavesIn S F) := by rw [h0]; norm_num
  · have h1 : 4 * (Qset S F).card ≤ 4 ^ (2 * BFormula.leavesIn S F) := Qset_card_le_pow S F hpos
    have h2 : (4 : ℕ) ^ (2 * BFormula.leavesIn S F) = 16 ^ (BFormula.leavesIn S F) := by
      rw [pow_mul]; norm_num
    have h3 : (Qset S F).card ≤ 16 ^ (BFormula.leavesIn S F) := by omega
    calc (blockResiduals S F).card ≤ (Qset S F).card :=
          Finset.card_le_card (blockResiduals_subset_Qset S F)
      _ ≤ 16 ^ (BFormula.leavesIn S F) := h3
      _ ≤ 2 * 16 ^ (BFormula.leavesIn S F) := by omega

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Qset_card_le_pow
#print axioms PallLean.Paper93.DeepMath.PathB.card_blockResiduals_le_pow
