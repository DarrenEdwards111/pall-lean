import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFatClauseAveraging

/-!
# The per-round fat-count decay of the restriction recursion

This is the bridge that turns the restriction-with-removal (`LDeriv.restrict`)
into the multiplicative decay step (`fat_count_decreases`) of the fat-clause
method.  The number of distinct **fat** clauses (width `> d`) in a derivation list
is the potential `a` that the recursion drives to zero.

`exists_restrict_fat_decay`: some literal `ℓ` restricts the derivation so that the
fat count obeys the per-round drop
`|Lit|·fat(restrictList ℓ L) ≤ (|Lit|-d)·fat(L)`.

Combined with `decay_pow` / `exists_decay_zero`, iterating these restrictions
drives the fat count to `0`, leaving a refutation of width `≤ d`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

open PallLean.Paper93.DeepMath.PathB.RestrictionClauseAlgebra

variable {Lit : Type*} [DecidableEq Lit] {compl : Lit → Lit}

/-- The set of distinct fat clauses (width `> d`) appearing in the list `L`. -/
def fatSet (d : ℕ) (L : List (ResolutionClause Lit)) : Finset (ResolutionClause Lit) :=
  L.toFinset.filter (fun C => d < ResolutionClause.width C)

theorem mem_fatSet {d : ℕ} {L : List (ResolutionClause Lit)} {C : ResolutionClause Lit} :
    C ∈ fatSet d L ↔ C ∈ L ∧ d < ResolutionClause.width C := by
  simp [fatSet, List.mem_toFinset]

/-- Each fat clause of the restricted list comes (via `restrictClause`) from a fat
clause of `L` that survives `ℓ` — so the restricted fat set embeds into the image
of the `ℓ`-free fat clauses. -/
theorem fatSet_restrictList_subset (d : ℕ) (ℓ : Lit) (L : List (ResolutionClause Lit)) :
    fatSet d (restrictList compl ℓ L)
      ⊆ ((fatSet d L).filter (fun C => ℓ ∉ C)).image (restrictClause compl ℓ) := by
  intro X hX
  rw [mem_fatSet] at hX
  obtain ⟨hXmem, hXwide⟩ := hX
  obtain ⟨C, hC, hℓC, hCX⟩ := (mem_restrictList compl ℓ L X).mp hXmem
  refine Finset.mem_image.mpr ⟨C, ?_, hCX⟩
  refine Finset.mem_filter.mpr ⟨mem_fatSet.mpr ⟨hC, ?_⟩, hℓC⟩
  -- `C` is fat: its width dominates the restricted clause's width
  have : ResolutionClause.width X ≤ ResolutionClause.width C := by
    rw [← hCX]; exact restrictClause_width_le compl ℓ C
  omega

/-- The restricted fat count is at most the count of `ℓ`-free fat clauses. -/
theorem fatSet_restrictList_card_le (d : ℕ) (ℓ : Lit) (L : List (ResolutionClause Lit)) :
    (fatSet d (restrictList compl ℓ L)).card
      ≤ ((fatSet d L).filter (fun C => ℓ ∉ C)).card :=
  le_trans (Finset.card_le_card (fatSet_restrictList_subset d ℓ L))
    (Finset.card_image_le)

variable [Fintype Lit] [Nonempty Lit]

/-- **Per-round fat-count decay.**  Some literal `ℓ` restricts `L` so that the fat
count drops by the popular-literal factor: `n·fat(L|ℓ) ≤ (n-d)·fat(L)`, where
`n = |Lit|`.  This is exactly the hypothesis of `decay_pow` / `exists_decay_zero`. -/
theorem exists_restrict_fat_decay (d : ℕ) (L : List (ResolutionClause Lit)) :
    ∃ ℓ : Lit, Fintype.card Lit * (fatSet d (restrictList compl ℓ L)).card
      ≤ (Fintype.card Lit - d) * (fatSet d L).card := by
  obtain ⟨ℓ, hℓ⟩ := fat_count_decreases (fatSet d L)
    (fun C hC => (mem_fatSet.mp hC).2)
  refine ⟨ℓ, le_trans (Nat.mul_le_mul_left _ (fatSet_restrictList_card_le d ℓ L)) hℓ⟩

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.fatSet_restrictList_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.exists_restrict_fat_decay
