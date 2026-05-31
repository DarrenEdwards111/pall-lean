import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationRecursion

/-!
# Size–width for list derivations: a small-width refutation after restrictions

Combining the recursion engine (`exists_restrictSeq_width_le`) with preservation
of validity and of the empty clause along the restrictions yields the downward
half of the size–width method: from a refutation with bounded fat-clause count,
finitely many popular-literal restrictions produce a **width-`≤d` refutation** (of
the correspondingly restricted axioms).

The complement must be fixed-point-free (`x ≠ compl x`) and involutive — both true
for the Tseitin complement `tcompl`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

variable {Lit : Type*} [DecidableEq Lit] [Fintype Lit] [Nonempty Lit] {compl : Lit → Lit}
  {Axiom : ResolutionClause Lit → Prop}

/-- **Validity is preserved.**  Every round of the restriction recursion is again a
list derivation, over a (round-dependent) restricted axiom predicate. -/
theorem restrictSeq_exists_LDeriv (hℓ : ∀ x, x ≠ compl x) (hinv : ∀ x, compl (compl x) = x)
    {L₀ : List (ResolutionClause Lit)} (hLD : LDeriv compl Axiom L₀) (d : ℕ) :
    ∀ k, ∃ A, LDeriv compl A (restrictSeq compl d L₀ k)
  | 0 => ⟨Axiom, hLD⟩
  | k + 1 => by
    obtain ⟨A, hA⟩ := restrictSeq_exists_LDeriv hℓ hinv hLD d k
    exact ⟨_, hA.restrict (hℓ _) hinv⟩

/-- **The refutation is preserved.**  The empty clause survives every round. -/
theorem restrictSeq_empty_mem {L₀ : List (ResolutionClause Lit)}
    (hmt : (∅ : ResolutionClause Lit) ∈ L₀) (d : ℕ) :
    ∀ k, (∅ : ResolutionClause Lit) ∈ restrictSeq compl d L₀ k
  | 0 => hmt
  | k + 1 => mem_restrictList_empty (restrictSeq_empty_mem hmt d k)

/-- **Downward size–width (list form).**  From a list-derivation refutation `L₀`,
with `1 ≤ d ≤ |Lit|-1`, finitely many popular-literal restrictions produce a
refutation in which *every* clause has width `≤ d`: there is a round `k` and a
restricted axiom predicate `A` with `restrictSeq … k` a valid `LDeriv` over `A`,
containing `∅`, all of whose clauses have width `≤ d`. -/
theorem exists_small_width_refutation (hℓ : ∀ x, x ≠ compl x) (hinv : ∀ x, compl (compl x) = x)
    {L₀ : List (ResolutionClause Lit)} (hLD : LDeriv compl Axiom L₀)
    (hmt : (∅ : ResolutionClause Lit) ∈ L₀) (d : ℕ) (hd1 : 1 ≤ d)
    (hdn : d + 1 ≤ Fintype.card Lit) :
    ∃ (k : ℕ) (A : ResolutionClause Lit → Prop),
      LDeriv compl A (restrictSeq compl d L₀ k) ∧
      (∅ : ResolutionClause Lit) ∈ restrictSeq compl d L₀ k ∧
      (∀ C ∈ restrictSeq compl d L₀ k, ResolutionClause.width C ≤ d) := by
  obtain ⟨k, hk⟩ := exists_restrictSeq_width_le (compl := compl) d L₀ hd1 hdn
  obtain ⟨A, hA⟩ := restrictSeq_exists_LDeriv hℓ hinv hLD d k
  exact ⟨k, A, hA, restrictSeq_empty_mem hmt d k, hk⟩

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.restrictSeq_exists_LDeriv
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.exists_small_width_refutation
