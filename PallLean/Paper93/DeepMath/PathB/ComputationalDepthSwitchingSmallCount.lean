import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBadCount

/-!
# Sharper count: `|Bad| ≤ |Short| · #{small subsets}`

**STATUS: REAL.  THE PATH-VARIABLE SET IS SMALL (≤ s), SHARPENING THE COUNT.**

The path fixes at most one variable per step, so the path-variable set has at most `s`
elements.  Replacing the `2ⁿ` (all subsets) factor by the count of subsets of size `≤ s`
sharpens the switching count to

  `|Bad| ≤ |Short| · #{S ⊆ Fin n : |S| ≤ s}`,

a bound polynomial in `n` for fixed `s` (vs the exponential `2ⁿ`).

* `pathLits_length_le`: the path has at most `s` literals;
* `pathvarset_card_le`: the path-variable set has at most `s` elements;
* `bad_card_le_smallsets`: the sharpened count.

The `(2w)^s` form is a further (clause-relative) tightening; this is the size-`≤ s`
subset bound, the genuine "few stars" content.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The path has at most `s` literals (at most one per step). -/
theorem pathLits_length_le (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    (pathLits cs ρ s).length ≤ s := by
  induction s with
  | zero => simp [pathLits]
  | succ k ih =>
    cases hal : activeLit cs (actPath cs ρ k) with
    | none =>
      have hpl : pathLits cs ρ (k + 1) = pathLits cs ρ k := by simp only [pathLits, hal]
      rw [hpl]; omega
    | some ℓ =>
      have hpl : pathLits cs ρ (k + 1) = ℓ :: pathLits cs ρ k := by simp only [pathLits, hal]
      rw [hpl, List.length_cons]; omega

/-- The path-variable set has at most `s` elements. -/
theorem pathvarset_card_le (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    ((pathLits cs ρ s).map litVar).toFinset.card ≤ s := by
  calc ((pathLits cs ρ s).map litVar).toFinset.card
      ≤ ((pathLits cs ρ s).map litVar).length := List.toFinset_card_le _
    _ = (pathLits cs ρ s).length := by rw [List.length_map]
    _ ≤ s := pathLits_length_le cs ρ s

/-- **Sharpened switching count.**  The factor is the number of subsets of size `≤ s`
(polynomial in `n` for fixed `s`), not `2ⁿ`. -/
theorem bad_card_le_smallsets {cs : List (Clause n)} {s : ℕ}
    {Bad Short : Finset (Restriction n)}
    (hmem : ∀ ρ ∈ Bad, complete ρ (pathLits cs ρ s) ∈ Short) :
    Bad.card ≤ Short.card *
      ((Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ s)).card := by
  classical
  have hsub : ∀ ρ ∈ Bad,
      (fun ρ => (complete ρ (pathLits cs ρ s), ((pathLits cs ρ s).map litVar).toFinset)) ρ
        ∈ Short ×ˢ ((Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ s)) := by
    intro ρ hρ
    refine Finset.mem_product.mpr ⟨hmem ρ hρ, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), pathvarset_card_le cs ρ s⟩
  have hinj : Set.InjOn
      (fun ρ => (complete ρ (pathLits cs ρ s), ((pathLits cs ρ s).map litVar).toFinset)) ↑Bad := by
    intro ρ _ σ _ heq
    exact bad_inj' (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  calc Bad.card
      ≤ (Short ×ˢ ((Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ s))).card :=
        Finset.card_le_card_of_injOn _ hsub hinj
    _ = Short.card *
          ((Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ s)).card := by
        rw [Finset.card_product]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.bad_card_le_smallsets
