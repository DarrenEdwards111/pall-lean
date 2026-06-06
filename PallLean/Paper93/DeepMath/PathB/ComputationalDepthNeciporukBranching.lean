import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukSpineContraction

/-!
# The branching bound: `|Qset (bin g a b)| ≤ 4·|Qset a|·|Qset b|`

The spine contraction (`SpineContraction`) handles *pass-through* (degree-2) nodes — `Qset` does not
grow there.  The complementary case is a **branching** node: `bin g a b` where both children read `S`.
There the two channels genuinely combine.  But each closure element of `bin g a b` is
`x ↦ h (g (φa x) (φb x))`, which is determined by the triple `(h, φa, φb)` with `φa` a residual of `a`,
`φb` a residual of `b`, and `h : Bool → Bool` ranging over a 4-element set.  Hence
  `|Qset (bin g a b)| ≤ 4 · |blockResiduals a| · |blockResiduals b| ≤ 4 · |Qset a| · |Qset b|`.

This is the last missing inequality for the `n²/log N` core: combined with the contraction under the
invariant `|Qset F| ≤ 4^{2·leavesIn − 1}` (`leavesIn ≥ 1`), the branching step preserves it
(`4 · 4^{2ℓa−1} · 4^{2ℓb−1} = 4^{2(ℓa+ℓb)−1}`).
-/

namespace PallLean.Paper93.DeepMath.PathB

open BFormula

variable {n : ℕ}

/-- **Branching bound.**  At a binary gate the closure grows by at most a factor `4` times the product
of the children's closures (each parent closure element `x ↦ h (g (φa x) (φb x))` is fixed by the
triple `(h, φa, φb)`). -/
theorem Qset_card_bin_le (S : Finset (Fin n)) (g : Bool → Bool → Bool) (a b : BFormula n) :
    (Qset S (BFormula.bin g a b)).card ≤ 4 * ((Qset S a).card * (Qset S b).card) := by
  classical
  have hsub : Qset S (BFormula.bin g a b) ⊆
      ((Finset.univ : Finset (Bool → Bool)) ×ˢ (blockResiduals S a ×ˢ blockResiduals S b)).image
        (fun t => fun x => t.1 (g (t.2.1 x) (t.2.2 x))) := by
    intro ψ hψ
    simp only [Qset, Finset.mem_image, Finset.mem_univ, true_and] at hψ
    obtain ⟨⟨h, α⟩, hψ⟩ := hψ
    rw [Finset.mem_image]
    refine ⟨(h, (fun x => BFormula.eval a (fun i => if i ∈ S then x i else α i),
                 fun x => BFormula.eval b (fun i => if i ∈ S then x i else α i))), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.mem_product]
      refine ⟨?_, ?_⟩ <;>
        · simp only [blockResiduals, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨α, rfl⟩
    · rw [← hψ]; funext x; simp only [BFormula.eval]
  calc (Qset S (BFormula.bin g a b)).card
      ≤ (((Finset.univ : Finset (Bool → Bool)) ×ˢ
            (blockResiduals S a ×ˢ blockResiduals S b)).image _).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Bool → Bool)) ×ˢ
            (blockResiduals S a ×ˢ blockResiduals S b)).card := Finset.card_image_le
    _ = (Finset.univ : Finset (Bool → Bool)).card *
          ((blockResiduals S a).card * (blockResiduals S b).card) := by
        rw [Finset.card_product, Finset.card_product]
    _ = 4 * ((blockResiduals S a).card * (blockResiduals S b).card) := by
        rw [show (Finset.univ : Finset (Bool → Bool)).card = 4 from by decide]
    _ ≤ 4 * ((Qset S a).card * (Qset S b).card) :=
        Nat.mul_le_mul (le_refl 4)
          (Nat.mul_le_mul (Finset.card_le_card (blockResiduals_subset_Qset S a))
            (Finset.card_le_card (blockResiduals_subset_Qset S b)))

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Qset_card_bin_le
