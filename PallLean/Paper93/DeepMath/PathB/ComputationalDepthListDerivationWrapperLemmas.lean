import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationRecombination
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationFatCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationVars

/-!
# Supporting lemmas for the size–width recursion wrapper

* `LDeriv.monoAxiom` / `RefutableWidth_mono` — relax the axiom predicate.
* `exists_restrict_fat_decay_var` — the per-round decay literal, additionally
  certified to occur in the derivation (so the variable measure strictly drops).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {Lit : Type*} [DecidableEq Lit] {compl : Lit → Lit}

/-- A derivation over `P` is a derivation over any larger `Q`. -/
theorem monoAxiom {P Q : ResolutionClause Lit → Prop} (h : ∀ C, P C → Q C)
    {L : List (ResolutionClause Lit)} (hd : LDeriv compl P L) : LDeriv compl Q L := by
  induction hd with
  | nil => exact LDeriv.nil
  | @cons C L just _ ih =>
    refine LDeriv.cons ?_ ih
    rcases just with ha | hr | hw
    · exact Or.inl (h _ ha)
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hw)

/-- Refutability in width `w` is monotone in the axiom predicate. -/
theorem RefutableWidth_mono {P Q : ResolutionClause Lit → Prop} {w : ℕ}
    (h : ∀ C, P C → Q C) (hr : RefutableWidth compl P w) : RefutableWidth compl Q w := by
  obtain ⟨L, hL, hmt, hw⟩ := hr
  exact ⟨L, monoAxiom h hL, hmt, hw⟩

variable {Edge : Type*} [DecidableEq Edge] [Fintype Edge] [Nonempty Edge]

/-- **Decay literal, with occurrence certificate.**  When the fat set is nonempty,
some literal `ℓ` both forces the per-round fat-count decay and *occurs* in the
derivation (so restricting it strictly shrinks the variable set). -/
theorem exists_restrict_fat_decay_var (d : ℕ) (L : List (ResolutionClause (TLit Edge)))
    (hd : 0 < d) (hpos : 0 < (fatSet d L).card) :
    ∃ ℓ : TLit Edge,
      Fintype.card (TLit Edge) * (fatSet d (restrictList tcompl ℓ L)).card
        ≤ (Fintype.card (TLit Edge) - d) * (fatSet d L).card ∧ ℓ.1 ∈ varsOf L := by
  obtain ⟨ℓ, hℓ⟩ := exists_popular_literal (fatSet d L) (fun C hC => (mem_fatSet.mp hC).2)
  set n := Fintype.card (TLit Edge)
  -- the decay, as in `fat_count_decreases`
  have hdecay : n * ((fatSet d L).filter (fun C => ℓ ∉ C)).card ≤ (n - d) * (fatSet d L).card := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := fatSet d L) (p := fun C => ℓ ∈ C)
    have hdist : n * ((fatSet d L).filter (fun C => ℓ ∈ C)).card
        + n * ((fatSet d L).filter (fun C => ℓ ∉ C)).card = n * (fatSet d L).card := by
      rw [← Nat.mul_add, hsplit]
    have hnd : (n - d) * (fatSet d L).card = n * (fatSet d L).card - d * (fatSet d L).card :=
      Nat.sub_mul _ _ _
    omega
  refine ⟨ℓ, le_trans (Nat.mul_le_mul_left _ (fatSet_restrictList_card_le d ℓ L)) hdecay, ?_⟩
  -- ℓ occurs: the popular literal lies in some fat clause
  have hposc : 0 < ((fatSet d L).filter (fun C => ℓ ∈ C)).card := by
    by_contra hc
    push_neg at hc
    interval_cases (((fatSet d L).filter (fun C => ℓ ∈ C)).card)
    simp only [Nat.mul_zero] at hℓ
    have : 0 < d * (fatSet d L).card := Nat.mul_pos hd hpos
    omega
  obtain ⟨C, hC⟩ := Finset.card_pos.mp hposc
  rw [Finset.mem_filter] at hC
  exact mem_varsOf.mpr ⟨C, (mem_fatSet.mp hC.1).1, ℓ, hC.2, rfl⟩

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.monoAxiom
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.exists_restrict_fat_decay_var
