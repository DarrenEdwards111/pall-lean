import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationFatCount

/-!
# The restriction recursion drives the fat count to zero

Iterating the per-round restriction of `exists_restrict_fat_decay` — at each step
pick the literal that forces the multiplicative decay `n·a_{k+1} ≤ (n-d)·a_k` —
drives the fat-clause count to `0` after finitely many rounds
(`exists_decay_zero`).  A list with empty fat set has **all** clauses of width
`≤ d`.

So: starting from any derivation list `L₀`, finitely many popular-literal
restrictions yield a list with every clause of width `≤ d` — the small-width
residual the size–width method produces.  (Validity / refutation are preserved
through each restriction by `LDeriv.restrict` / `mem_restrictList_empty`, applied
along the same chosen literals.)
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

variable {Lit : Type*} [DecidableEq Lit] [Fintype Lit] [Nonempty Lit] {compl : Lit → Lit}

/-- The literal chosen at round `k` to force the fat-count decay, and the iterated
restriction list.  Defined by mutual recursion on the round. -/
noncomputable def restrictSeq (compl : Lit → Lit) (d : ℕ) (L₀ : List (ResolutionClause Lit)) :
    ℕ → List (ResolutionClause Lit)
  | 0 => L₀
  | k + 1 =>
    restrictList compl
      (Classical.choose (exists_restrict_fat_decay (compl := compl) d (restrictSeq compl d L₀ k)))
      (restrictSeq compl d L₀ k)

/-- The fat count along the recursion. -/
noncomputable def fatSeq (compl : Lit → Lit) (d : ℕ) (L₀ : List (ResolutionClause Lit)) (k : ℕ) :
    ℕ :=
  (fatSet d (restrictSeq compl d L₀ k)).card

/-- The recursion realises the multiplicative-decay step. -/
theorem fatSeq_step (d : ℕ) (L₀ : List (ResolutionClause Lit)) (k : ℕ) :
    Fintype.card Lit * fatSeq compl d L₀ (k + 1)
      ≤ (Fintype.card Lit - d) * fatSeq compl d L₀ k := by
  have hspec := Classical.choose_spec
    (exists_restrict_fat_decay (compl := compl) d (restrictSeq compl d L₀ k))
  simpa [fatSeq, restrictSeq] using hspec

/-- A list whose fat set is empty has every clause of width `≤ d`. -/
theorem width_le_of_fatSet_empty {d : ℕ} {L : List (ResolutionClause Lit)}
    (h : fatSet d L = ∅) {C : ResolutionClause Lit} (hC : C ∈ L) :
    ResolutionClause.width C ≤ d := by
  by_contra hlt
  push_neg at hlt
  exact absurd (mem_fatSet.mpr ⟨hC, hlt⟩) (by rw [h]; simp)

/-- **The recursion terminates.**  With `1 ≤ d ≤ |Lit|-1`, finitely many
popular-literal restrictions make the fat set empty: some `restrictSeq` round has
**all** clauses of width `≤ d`. -/
theorem exists_restrictSeq_width_le (d : ℕ) (L₀ : List (ResolutionClause Lit))
    (hd1 : 1 ≤ d) (hdn : d + 1 ≤ Fintype.card Lit) :
    ∃ k : ℕ, ∀ C ∈ restrictSeq compl d L₀ k, ResolutionClause.width C ≤ d := by
  obtain ⟨k, hk⟩ := exists_decay_zero (fatSeq compl d L₀)
    (fatSeq_step (compl := compl) d L₀) hd1 hdn
  refine ⟨k, ?_⟩
  have hempty : fatSet d (restrictSeq compl d L₀ k) = ∅ :=
    Finset.card_eq_zero.mp hk
  exact fun C hC => width_le_of_fatSet_empty hempty hC

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.fatSeq_step
#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.exists_restrictSeq_width_le
