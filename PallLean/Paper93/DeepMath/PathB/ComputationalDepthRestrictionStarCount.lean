import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRestrictionCardinality
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic

/-!
# Star-count layer of the restriction universe

**STATUS: REAL.  THE BINOMIAL-RATIO BALANCE REMAINS THE ANALYTIC CORE.**

Counts restrictions by number of free coordinates ("stars"):

  `|{ρ : stars ρ = t}| = C(N, t) · 2^(N - t)`.

Proof: partition by the free set `freeVars ρ`; each fibre `{freeVars ρ = S}` has
`2^(N - |S|) = 2^(N - t)` restrictions (`card_freeVars_eq`), and there are
`C(N, t)` free sets of size `t`.

This is the layer the switching inequality compares: bad restrictions of the
`t`-star universe inject into the `(t-s)`-star layer (times the label factor).
The ratio bound `C(N, t-s)·2^(N-t+s)·((2^w)^m)^numTerms < C(N, t)·2^(N-t)`
— choosing the star parameter `t ≈ pN` — is the remaining analytic core, left as
its own theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

variable {N : ℕ}

/-- The restrictions with exactly `t` free coordinates. -/
def restrictionsWithStars (N t : ℕ) : Finset (Restriction N) :=
  Finset.univ.filter (fun ρ => stars ρ = t)

/-- **The star-count layer: `|{stars = t}| = C(N, t) · 2^(N - t)`.** -/
theorem card_stars_eq (t : ℕ) :
    (restrictionsWithStars N t).card = N.choose t * 2 ^ (N - t) := by
  unfold restrictionsWithStars
  have hmem : Set.MapsTo (fun ρ : Restriction N => freeVars ρ)
      ↑(Finset.univ.filter (fun ρ : Restriction N => stars ρ = t))
      ↑(Finset.powersetCard t (Finset.univ : Finset (Fin N))) := by
    intro ρ hρ
    rw [Finset.mem_coe, Finset.mem_filter] at hρ
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by simpa [stars] using hρ.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  have hfib : ∀ S ∈ Finset.powersetCard t (Finset.univ : Finset (Fin N)),
      ((Finset.univ.filter (fun ρ : Restriction N => stars ρ = t)).filter
        (fun ρ => freeVars ρ = S)).card = 2 ^ (N - t) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hset : (Finset.univ.filter (fun ρ : Restriction N => stars ρ = t)).filter
          (fun ρ => freeVars ρ = S)
        = Finset.univ.filter (fun ρ : Restriction N => freeVars ρ = S) := by
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by show (freeVars ρ).card = t; rw [h]; exact hS.2, h⟩
    rw [hset, card_freeVars_eq, hS.2]
  have hsum : (∑ S ∈ Finset.powersetCard t (Finset.univ : Finset (Fin N)),
      ((Finset.univ.filter (fun ρ : Restriction N => stars ρ = t)).filter
        (fun ρ => freeVars ρ = S)).card)
      = ∑ _S ∈ Finset.powersetCard t (Finset.univ : Finset (Fin N)), 2 ^ (N - t) :=
    Finset.sum_congr rfl hfib
  rw [hsum, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  simp

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.card_stars_eq
