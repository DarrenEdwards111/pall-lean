import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationWrapperLemmas
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthListDerivationRecursion

/-!
# The general (DAG) size–width recursion (BSW upper bound)

The recursion wrapper combining every component: from a refutation of `F` (axioms
`Ax`) whose fat-clause count satisfies `(n-d)^b · fatCount < n^b`, `F` is refutable
in width `wF + d + b`.  Proved by strong induction on the variable count
`(varsOf L).card`:

* **base** (fat count `0`): every clause already has width `≤ d`;
* **step**: pick the decay literal `ℓ` (occurs, by `exists_restrict_fat_decay_var`);
  the `ℓ:=true` branch decays the fat count (`b → b-1`, paying `+1`), the
  `¬ℓ:=true` branch keeps `b` (paying `+0`); both drop the variable `ℓ.1`, so the
  IH applies; `asym_recombination` glues them at width `wF + d + b`.

Only the lifting branch pays `+1`, so the width is `d + b`, not `d + n`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace LDeriv

open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open PallLean.Paper93.DeepMath.PathB.TseitinRestriction

variable {Edge : Type*} [DecidableEq Edge] [Fintype Edge] [Nonempty Edge]

/-- **General size–width recursion.**  If `F` (axioms `Ax`, widths `≤ wF`) has a
refutation `L` with `(n-d)^b · (#fat clauses) < n^b` (`n = |literals|`), then `F`
is refutable in width `wF + d + b`. -/
theorem size_width_recursion (d : ℕ) (hd : 0 < d) :
    ∀ (ν : ℕ) (Ax L : List (ResolutionClause (TLit Edge))) (b wF : ℕ),
      (varsOf L).card ≤ ν →
      LDeriv tcompl (· ∈ Ax) L → (∅ : ResolutionClause (TLit Edge)) ∈ L →
      (∀ C ∈ Ax, ResolutionClause.width C ≤ wF) →
      (Fintype.card (TLit Edge) - d) ^ b * (fatSet d L).card < Fintype.card (TLit Edge) ^ b →
      RefutableWidth tcompl (· ∈ Ax) (wF + d + b) := by
  intro ν
  induction ν using Nat.strong_induction_on with
  | _ ν ih =>
    intro Ax L b wF hν hLD hmt hAx hinv
    set n := Fintype.card (TLit Edge) with hn_def
    have hn : 0 < n := Fintype.card_pos
    by_cases hb0 : (fatSet d L).card = 0
    · -- base: no fat clauses, every clause has width ≤ d
      refine ⟨L, hLD, hmt, fun C hC => ?_⟩
      have : ResolutionClause.width C ≤ d :=
        width_le_of_fatSet_empty (Finset.card_eq_zero.mp hb0) hC
      omega
    · -- step
      have hpos : 0 < (fatSet d L).card := Nat.pos_of_ne_zero hb0
      have hbne : b ≠ 0 := by
        rintro rfl; simp only [pow_zero, one_mul] at hinv; omega
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      obtain ⟨ℓ, hdecay, hℓvar⟩ := exists_restrict_fat_decay_var d L hd hpos
      -- ℓ:=true branch
      have hLD1 : LDeriv tcompl (· ∈ restrictList tcompl ℓ Ax) (restrictList tcompl ℓ L) := by
        refine monoAxiom (fun C' hC' => (mem_restrictList tcompl ℓ Ax C').mpr hC')
          (LDeriv.restrict (ne_tcompl ℓ) tcompl_tcompl hLD)
      have hmt1 : (∅ : ResolutionClause (TLit Edge)) ∈ restrictList tcompl ℓ L :=
        mem_restrictList_empty hmt
      have hAx1 : ∀ C ∈ restrictList tcompl ℓ Ax, ResolutionClause.width C ≤ wF := by
        intro C hC
        obtain ⟨C', hC', _, hCe⟩ := (mem_restrictList tcompl ℓ Ax C).mp hC
        rw [← hCe]
        exact le_trans (RestrictionClauseAlgebra.restrictClause_width_le tcompl ℓ C') (hAx C' hC')
      have hinv1 : (n - d) ^ b' * (fatSet d (restrictList tcompl ℓ L)).card < n ^ b' := by
        have key : n * ((n - d) ^ b' * (fatSet d (restrictList tcompl ℓ L)).card)
            < n * n ^ b' := by
          calc n * ((n - d) ^ b' * (fatSet d (restrictList tcompl ℓ L)).card)
              = (n - d) ^ b' * (n * (fatSet d (restrictList tcompl ℓ L)).card) := by ring
            _ ≤ (n - d) ^ b' * ((n - d) * (fatSet d L).card) :=
                Nat.mul_le_mul_left _ hdecay
            _ = (n - d) ^ (b' + 1) * (fatSet d L).card := by ring
            _ < n ^ (b' + 1) := hinv
            _ = n * n ^ b' := by ring
        exact lt_of_mul_lt_mul_left key (Nat.zero_le n)
      have hvar1 : (varsOf (restrictList tcompl ℓ L)).card < (varsOf L).card :=
        varsOf_restrictList_card_lt ℓ L hℓvar
      have hr1 : RefutableWidth tcompl (· ∈ restrictList tcompl ℓ Ax) (wF + d + b') :=
        ih _ (lt_of_lt_of_le hvar1 hν) _ _ b' wF (le_refl _) hLD1 hmt1 hAx1 hinv1
      -- ¬ℓ:=true branch
      have hedge : (tcompl ℓ).1 = ℓ.1 := rfl
      have hLD0 : LDeriv tcompl (· ∈ restrictList tcompl (tcompl ℓ) Ax)
          (restrictList tcompl (tcompl ℓ) L) := by
        refine monoAxiom (fun C' hC' => (mem_restrictList tcompl (tcompl ℓ) Ax C').mpr hC')
          (LDeriv.restrict (by rw [tcompl_tcompl]; exact (ne_tcompl ℓ).symm) tcompl_tcompl hLD)
      have hmt0 : (∅ : ResolutionClause (TLit Edge)) ∈ restrictList tcompl (tcompl ℓ) L :=
        mem_restrictList_empty hmt
      have hAx0 : ∀ C ∈ restrictList tcompl (tcompl ℓ) Ax, ResolutionClause.width C ≤ wF := by
        intro C hC
        obtain ⟨C', hC', _, hCe⟩ := (mem_restrictList tcompl (tcompl ℓ) Ax C).mp hC
        rw [← hCe]
        exact le_trans (RestrictionClauseAlgebra.restrictClause_width_le tcompl (tcompl ℓ) C')
          (hAx C' hC')
      have hinv0 : (n - d) ^ (b' + 1) * (fatSet d (restrictList tcompl (tcompl ℓ) L)).card
          < n ^ (b' + 1) := by
        have hfat0 : (fatSet d (restrictList tcompl (tcompl ℓ) L)).card ≤ (fatSet d L).card :=
          le_trans (fatSet_restrictList_card_le d (tcompl ℓ) L) (Finset.card_filter_le _ _)
        exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hfat0) hinv
      have hvar0 : (varsOf (restrictList tcompl (tcompl ℓ) L)).card < (varsOf L).card :=
        varsOf_restrictList_card_lt (tcompl ℓ) L (hedge ▸ hℓvar)
      have hr0 : RefutableWidth tcompl (· ∈ restrictList tcompl (tcompl ℓ) Ax)
          (wF + d + (b' + 1)) :=
        ih _ (lt_of_lt_of_le hvar0 hν) _ _ (b' + 1) wF (le_refl _) hLD0 hmt0 hAx0 hinv0
      -- recombine
      have h1' : RefutableWidth tcompl (restrictedAxiom tcompl Ax ℓ) (wF + d + b') :=
        RefutableWidth_mono (fun C hC => (mem_restrictList tcompl ℓ Ax C).mp hC) hr1
      have h0' : RefutableWidth tcompl (restrictedAxiom tcompl Ax (tcompl ℓ)) (wF + d + (b' + 1)) :=
        RefutableWidth_mono (fun C hC => (mem_restrictList tcompl (tcompl ℓ) Ax C).mp hC) hr0
      have hrec := asym_recombination Ax ℓ hAx h1' h0'
      have heq : max (max (wF + d + (b' + 1)) (wF + d + b' + 1)) wF = wF + d + (b' + 1) := by omega
      rw [heq] at hrec
      exact hrec

end LDeriv

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.LDeriv.size_width_recursion
