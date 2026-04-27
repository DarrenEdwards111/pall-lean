import PallLean.Paper93.DeepMath.PathB.KeepFOBProjectedLowerBound
import PallLean.Step4Compiler

/-!
# Strict first-of-block / keepFOB bridge

This file isolates the type-correct bridge between coordinate restriction of
the ambient Cook-Levin `embedded_Q` sheet and the existing flat `keepFOB`
projected lower-bound polynomial.

The exact `keepFOB` projection keeps every flat index divisible by `3`, whose
cardinality is `(n + 2) / 3`.  Therefore exact identification with the existing
`satDeciderGaugeKeepFOBProjection` uses the ceil-sized first-of-block inclusion.
The floor-sized `Fin (n / 3)` semantic minor target remains a stricter target
and cannot be definitionally equal to the existing keepFOB projection unless an
extra divisibility hypothesis or a floor-only projection is supplied.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Enumeration of all flat Cook-Levin first-of-block variables kept by
`PiStarConcrete.keepFOB`. -/
noncomputable def keepFOBInclusion (n : ℕ) :
    Fin ((n + 2) / 3) → Fin n :=
  fun b => ⟨3 * b.val, by omega⟩

/-- The all-firsts keepFOB inclusion is injective. -/
theorem keepFOBInclusion_injective (n : ℕ) :
    Function.Injective (keepFOBInclusion n) := by
  intro a b h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp [keepFOBInclusion] at hval
  omega

/-- The range of `keepFOBInclusion` is exactly the flat `keepFOB` predicate. -/
theorem keepFOBInclusion_range_iff (n : ℕ) (i : Fin n) :
    (∃ b : Fin ((n + 2) / 3), keepFOBInclusion n b = i) ↔
      PiStarConcrete.keepFOB i := by
  constructor
  · rintro ⟨b, rfl⟩
    exact dvd_mul_right 3 b.val
  · intro hi
    rcases hi with ⟨k, hk⟩
    refine ⟨⟨k, by omega⟩, ?_⟩
    apply Fin.ext
    simp [keepFOBInclusion, hk]

/-- Generic coordinate-restriction identity for a projection whose kept
coordinates are exactly the range of `g`.

The left side restricts an ambient embedding `rename u p` to the coordinates
`u ∘ g`, then re-expands to the ambient space.  The result is the same as
first killing all source variables outside `range g` by `piZero`, then
embedding by `u`. -/
theorem rename_restrict_rename_eq_rename_piZero_of_range
    {k n m : ℕ}
    (u : Fin n → Fin m) (hu : Function.Injective u)
    (g : Fin k → Fin n) (hg : Function.Injective g)
    (hrange : ∀ i : Fin n,
      (∃ j : Fin k, g j = i) ↔ PiStarConcrete.keepFOB i)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.rename (fun j => u (g j))
      (MultilinearSPDP.restrictPoly ℚ
        (fun j => u (g j)) (hu.comp hg)
        (MvPolynomial.rename u p)) =
    MvPolynomial.rename u
      (PiStarConcrete.piZero PiStarConcrete.keepFOB p) := by
  classical
  let f : Fin k → Fin m := fun j => u (g j)
  have hf : Function.Injective f := hu.comp hg
  change
    ((MvPolynomial.rename f).comp
        ((MultilinearSPDP.restrictPoly ℚ f hf).comp (MvPolynomial.rename u))) p =
      ((MvPolynomial.rename u).comp
        (PiStarConcrete.substAlgHom PiStarConcrete.keepFOB (0 : Fin n → ℚ))) p
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  by_cases hi : PiStarConcrete.keepFOB i
  · rcases (hrange i).2 hi with ⟨j, hj⟩
    have hfi : ∃ j : Fin k, f j = u i := ⟨j, by simp [f, hj]⟩
    simp [AlgHom.comp_apply, f, MultilinearSPDP.restrictPoly_X, hfi, hi,
      PiStarConcrete.substAlgHom, PiStarConcrete.substFn, Classical.choose_spec hfi]
  · have hnfi : ¬ ∃ j : Fin k, f j = u i := by
      rintro ⟨j, hj⟩
      have hgi : g j = i := hu hj
      exact hi ((hrange i).1 ⟨j, hgi⟩)
    simp [AlgHom.comp_apply, f, MultilinearSPDP.restrictPoly_X, hnfi, hi,
      PiStarConcrete.substAlgHom, PiStarConcrete.substFn]

/-- Exact type-correct identification of the ambient coordinate-restricted
Cook-Levin `embedded_Q` sheet with the existing flat keepFOB projected
compiled polynomial, re-embedded into the UV ambient variables. -/
theorem partitioned_cookLevin_embedded_Q_keepFOB_restrict_eq
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    let σ := PaperFaithfulCompilation.cookLevinUVSplit M n
    let g := keepFOBInclusion n
    let f : Fin ((n + 2) / 3) → Fin σ.total := fun i => σ.inlU (g i)
    MvPolynomial.rename f
      (MultilinearSPDP.restrictPoly ℚ f
        ((PaperFaithfulCompilation.inlU_injective σ).comp
          (keepFOBInclusion_injective n))
        (Step4Compiler.Step247.partitioned_output_cookLevin
          M n hn2 htb hns).embedded_Q) =
    MvPolynomial.rename σ.inlU
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns
        (PaperFaithfulSeparation.compiledPoly
          (PaperFaithfulSeparation.cook_levin_compilation
            M n hn2 htb hns))) := by
  classical
  dsimp
  rw [Step4Compiler.Step247.partitioned_output_cookLevin_embedded_Q_eq
    M n hn2 htb hns]
  unfold satDeciderGaugeKeepFOBProjection
  rw [rename_restrict_rename_eq_rename_piZero_of_range
    (PaperFaithfulCompilation.cookLevinUVSplit M n).inlU
    (PaperFaithfulCompilation.inlU_injective
      (PaperFaithfulCompilation.cookLevinUVSplit M n))
    (keepFOBInclusion n) (keepFOBInclusion_injective n)
    (keepFOBInclusion_range_iff n)]
  rw [lemma124_Q_times_Phi_135_eq_compiledPoly M n hn2 htb hns]
  rfl

/-- The existing flat keepFOB projected lower bound transports to the ambient
UV rank lower bound for the exact all-firsts coordinate restriction of
`embedded_Q`. -/
theorem partitioned_cookLevin_embedded_Q_keepFOB_renamed_lower_bound
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Nat.choose (n / 3) (Nat.log 2 n) ≤
      MultilinearSPDP.mlBlockedSpdpRank
        (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
        (Nat.log 2 n) (Nat.log 2 n)
        (MvPolynomial.rename
          (fun i : Fin ((n + 2) / 3) =>
            (PaperFaithfulCompilation.cookLevinUVSplit M n).inlU
              (keepFOBInclusion n i))
          (MultilinearSPDP.restrictPoly ℚ
            (fun i : Fin ((n + 2) / 3) =>
              (PaperFaithfulCompilation.cookLevinUVSplit M n).inlU
                (keepFOBInclusion n i))
            ((PaperFaithfulCompilation.inlU_injective
              (PaperFaithfulCompilation.cookLevinUVSplit M n)).comp
                (keepFOBInclusion_injective n))
            (Step4Compiler.Step247.partitioned_output_cookLevin
              M n hn2 htb hns).embedded_Q)) := by
  classical
  let σ := PaperFaithfulCompilation.cookLevinUVSplit M n
  let q : MvPolynomial (Fin σ.numU) ℚ :=
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns
      (PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation
          M n hn2 htb hns))
  have hflat :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        MultilinearSPDP.mlBlockedSpdpRank
          (MultilinearSPDP.pullbackPartition
            (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
            σ.inlU)
          (Nat.log 2 n) (Nat.log 2 n) q := by
    simpa [σ, q,
      PaperFaithfulCompilation.pullback_eq_cook_levin_partition
        M n hn2 htb hns] using
      (satDeciderGaugeKeepFOBProjection_projected_compiled_lower_bound
        M n hn hn2 htb hns)
  have hemb :=
    PaperFaithfulCompilation.embed_rank_preservation σ
      (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
      (Nat.log 2 n) (Nat.log 2 n) q
  have hamb :
      Nat.choose (n / 3) (Nat.log 2 n) ≤
        MultilinearSPDP.mlBlockedSpdpRank
          (PaperFaithfulCompilation.extendedCookLevinPartition M n hn2)
          (Nat.log 2 n) (Nat.log 2 n)
          (MvPolynomial.rename σ.inlU q) := by
    simpa [PaperFaithfulCompilation.CoupledSheetPoly.embed, q] using
      (le_trans hflat hemb)
  have heq :=
    partitioned_cookLevin_embedded_Q_keepFOB_restrict_eq
      M n hn2 htb hns
  dsimp at heq
  rw [heq]
  exact hamb

end PallLean.Paper93.DeepMath.PathB
