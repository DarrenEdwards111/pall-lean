import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinResolutionWidth

/-!
# The variable-count termination measure

The recursion wrapper of the general size–width method terminates because **both**
branches of a restriction remove a whole variable: restricting `(e,b) := true`
satisfies (and removes) every clause containing `(e,b)` and erases the only other
literal on edge `e`, namely `(e, b+1) = compl (e,b)`.  So edge `e` disappears from
every surviving clause.

`varsOf L` is the set of edges occurring in the clause list `L`; restriction can
only shrink it, and *strictly* shrinks it when the restricted edge occurs.  This is
the well-founded measure for the recursion.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {Edge : Type*} [DecidableEq Edge]

/-- In `ZMod 2`, two distinct values differ by one. -/
theorem zmod2_ne_add_one : ∀ a b : ZMod 2, a ≠ b → a = b + 1 := by decide

/-- The only literals on edge `ℓ.1` are `ℓ` and `tcompl ℓ`. -/
theorem lit_edge_eq {m ℓ : TLit Edge} (h : m.1 = ℓ.1) : m = ℓ ∨ m = tcompl ℓ := by
  by_cases hb : m.2 = ℓ.2
  · left
    exact Prod.ext h hb
  · right
    exact Prod.ext h (zmod2_ne_add_one m.2 ℓ.2 hb)

/-- The set of edges occurring in a clause list. -/
def varsOf (L : List (ResolutionClause (TLit Edge))) : Finset Edge :=
  L.toFinset.biUnion (fun C => C.image Prod.fst)

theorem mem_varsOf {L : List (ResolutionClause (TLit Edge))} {e : Edge} :
    e ∈ varsOf L ↔ ∃ C, C ∈ L ∧ ∃ m ∈ C, m.1 = e := by
  simp only [varsOf, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_image]

/-- The restricted edge no longer occurs after restriction. -/
theorem not_mem_varsOf_restrictList (ℓ : TLit Edge)
    (L : List (ResolutionClause (TLit Edge))) :
    ℓ.1 ∉ varsOf (restrictList tcompl ℓ L) := by
  rw [mem_varsOf]
  rintro ⟨C', hC', m, hm, hme⟩
  obtain ⟨C, _, hℓC, hCe⟩ := (mem_restrictList tcompl ℓ L C').mp hC'
  rw [← hCe] at hm
  have hm' := Finset.mem_of_mem_erase hm
  have hne : m ≠ tcompl ℓ := Finset.ne_of_mem_erase hm
  rcases lit_edge_eq hme with h | h
  · exact hℓC (h ▸ hm')
  · exact hne h

/-- Restriction can only shrink the variable set. -/
theorem varsOf_restrictList_subset (ℓ : TLit Edge)
    (L : List (ResolutionClause (TLit Edge))) :
    varsOf (restrictList tcompl ℓ L) ⊆ varsOf L := by
  intro e he
  rw [mem_varsOf] at he ⊢
  obtain ⟨C', hC', m, hm, hme⟩ := he
  obtain ⟨C, hC, _, hCe⟩ := (mem_restrictList tcompl ℓ L C').mp hC'
  rw [← hCe] at hm
  exact ⟨C, hC, m, Finset.mem_of_mem_erase hm, hme⟩

/-- **The termination measure strictly decreases.**  If the restricted edge occurs
in `L`, the variable set shrinks. -/
theorem varsOf_restrictList_card_lt (ℓ : TLit Edge)
    (L : List (ResolutionClause (TLit Edge))) (hmem : ℓ.1 ∈ varsOf L) :
    (varsOf (restrictList tcompl ℓ L)).card < (varsOf L).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (varsOf_restrictList_subset ℓ L) |>.mpr ⟨ℓ.1, hmem, ?_⟩
  exact not_mem_varsOf_restrictList ℓ L

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.varsOf_restrictList_card_lt
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.lit_edge_eq
