import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTRefutation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResolutionWidthSize

/-!
# Tree → `ResolutionDerivation` size conversion

The size route to the depth-3 lower bound (`tseitin_no_small_refutation`) consumes a
`ResolutionDerivation` of `∅` of size `≤ 2^D`.  The collapse produces a `DTRef` (decision-tree
refutation).  This file converts a `DTRef` into a tree-like `ResolutionDerivation`, tracking size.

The conversion is the standard decision-tree → tree-like-resolution map: a leaf (axiom clause `⊆ F`)
becomes an `ax` step; a node branching on `ℓ` resolves its two children on `ℓ` (their derived clauses
lie in `insert ℓ F` and `insert (compl ℓ) F`, so the resolvent lands back in `F`).

* `dtRef_to_resolutionDerivation` — from `Labeled Axiom t` and `Refutes compl t F`, a
  `ResolutionDerivation` of some clause `C ⊆ F` with `size + 1 ≤ 2 · t.leaves`.
* `dtRef_resolution_refutation` — at `F = ∅`: a `ResolutionDerivation` of `∅` with `size + 1 ≤ 2·leaves`.
* `dtRef_resolution_size_le` — combined with `leaves ≤ 2^depth`: a `ResolutionDerivation` of `∅` with
  `size ≤ 2^(depth+1)`.

So a shallow refuting decision tree (depth `d`) yields a resolution refutation of size `≤ 2^(d+1)` —
exactly the input `tseitin_no_small_refutation` needs.  This closes the tree → `ResolutionDerivation`
bridge; the only remaining input to the depth-3 lower bound is the *shallowness* of `d` (the switching
depth bound, the fenced Obligation 1).  AC⁰/depth-3; `Depth3CollapseModel.collapse` and P vs NP
untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

variable {Lit : Type*} [DecidableEq Lit] {compl : Lit → Lit} {Axiom : ResolutionClause Lit → Prop}

/-- **Decision-tree refutation → tree-like resolution derivation.**  From `Labeled Axiom t` and
`Refutes compl t F`, build a `ResolutionDerivation` of some clause `C ⊆ F`, with
`size + 1 ≤ 2 · t.leaves` (a leaf is one `ax`; a node resolves its two children on the branch
literal). -/
theorem dtRef_to_resolutionDerivation (compl : Lit → Lit) (Axiom : ResolutionClause Lit → Prop) :
    ∀ (t : DTRef Lit) (F : ResolutionClause Lit),
      DTRef.Labeled Axiom t → DTRef.Refutes compl t F →
      ∃ (C : ResolutionClause Lit) (D : ResolutionDerivation compl Axiom C),
        C ⊆ F ∧ D.size + 1 ≤ 2 * t.leaves := by
  intro t
  induction t with
  | leaf C =>
    intro F hlab href
    exact ⟨C, ResolutionDerivation.ax hlab, href, by
      simp [DTRef.leaves, ResolutionDerivation.size]⟩
  | node ℓ t0 t1 ih0 ih1 =>
    intro F hlab href
    obtain ⟨hlab0, hlab1⟩ := hlab
    obtain ⟨href0, href1⟩ := href
    obtain ⟨C0, D0, hsub0, hsize0⟩ := ih0 (insert ℓ F) hlab0 href0
    obtain ⟨C1, D1, hsub1, hsize1⟩ := ih1 (insert (compl ℓ) F) hlab1 href1
    refine ⟨ResolutionClause.resolvent compl C0 C1 ℓ,
      ResolutionDerivation.resolve D0 D1 ℓ, ?_, ?_⟩
    · rw [ResolutionClause.resolvent]
      refine Finset.union_subset ?_ ?_
      · exact (Finset.erase_subset_erase ℓ hsub0).trans (DTRef.erase_insert_subset ℓ F)
      · exact (Finset.erase_subset_erase (compl ℓ) hsub1).trans
          (DTRef.erase_insert_subset (compl ℓ) F)
    · simp only [ResolutionDerivation.size, DTRef.leaves]
      omega

/-- **Refutation form.**  At `F = ∅`, the derived clause is `∅`: a `ResolutionDerivation` of `∅` with
`size + 1 ≤ 2 · t.leaves`. -/
theorem dtRef_resolution_refutation {t : DTRef Lit} (hlab : DTRef.Labeled Axiom t)
    (href : DTRef.Refutes compl t (∅ : ResolutionClause Lit)) :
    ∃ D : ResolutionDerivation compl Axiom (∅ : ResolutionClause Lit), D.size + 1 ≤ 2 * t.leaves := by
  obtain ⟨C, D, hsub, hsize⟩ := dtRef_to_resolutionDerivation compl Axiom t ∅ hlab href
  obtain rfl : C = ∅ := Finset.subset_empty.mp hsub
  exact ⟨D, hsize⟩

/-- **Size bound from depth.**  A depth-`d` refuting decision tree yields a resolution refutation of
`∅` of size `≤ 2^(d+1)` (`size + 1 ≤ 2·leaves ≤ 2·2^depth = 2^(depth+1)`). -/
theorem dtRef_resolution_size_le {t : DTRef Lit} (hlab : DTRef.Labeled Axiom t)
    (href : DTRef.Refutes compl t (∅ : ResolutionClause Lit)) :
    ∃ D : ResolutionDerivation compl Axiom (∅ : ResolutionClause Lit),
      D.size ≤ 2 ^ (t.depth + 1) := by
  obtain ⟨D, hsize⟩ := dtRef_resolution_refutation hlab href
  refine ⟨D, ?_⟩
  have hl : t.leaves ≤ 2 ^ t.depth := DTRef.leaves_le_two_pow_depth t
  have h2 : 2 ^ (t.depth + 1) = 2 * 2 ^ t.depth := by rw [pow_succ, Nat.mul_comm]
  omega

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.dtRef_to_resolutionDerivation
#print axioms PallLean.Paper93.DeepMath.PathB.dtRef_resolution_size_le
