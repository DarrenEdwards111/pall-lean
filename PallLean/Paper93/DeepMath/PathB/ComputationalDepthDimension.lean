import Mathlib

/-!
# The dimension argument for the Razborov–Smolensky lower bound (PROVED backbone)

The lower bound `MOD_q ∉ AC⁰[p]` is closed by a **dimension/counting** argument.  Sketch: if an `AC⁰[p]` circuit
for `MOD_q` were approximated on a large set `A ⊆ {0,1}ⁿ` by a degree-`m` `𝔽_p`-polynomial, then *every* function
`A → 𝔽_p` would be realised by a degree-`m` polynomial (the Smolensky "boosting" step, using the OR
approximation).  The realisation map sends the coefficient space of degree-`≤m` multilinear polynomials onto
`𝔽_p^A`, forcing

  `|A| ≤ dim(degree-≤m multilinear polynomials) = Σ_{i≤m} C(n,i)`.

For `m` small this is `< 2ⁿ`, contradicting `|A|` large.  This file proves the two self-contained backbones:

  `card_subsets_card_le` — **the dimension count**: the number of multilinear monomials of degree `≤ m` in `n`
        variables (subsets of size `≤ m`) is exactly `Σ_{i≤m} C(n,i)`.
  `card_le_of_surjective` — **the counting core**: a surjection from a coefficient space `M → 𝔽` onto `A → 𝔽`
        (`|𝔽| ≥ 2`) forces `|A| ≤ |M|` — the engine that turns "every function on `A` is low-degree" into the
        dimension bound on `|A|`.

The "boosting" step that produces the surjection (`MOD_q` approximated ⇒ every function on `A` is low-degree)
remains the genuine target; this lays the exact counting foundation it feeds.
-/

namespace PallLean.Paper93.DeepMath.PathB.Dimension

/-- The number of size-`i` subsets of `Fin n` (degree-`i` multilinear monomials) is `C(n,i)`. -/
theorem card_subsets_card_eq (n i : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin n) => S.card = i)).card = n.choose i := by
  have hset : Finset.univ.filter (fun S : Finset (Fin n) => S.card = i)
      = (Finset.univ : Finset (Fin n)).powersetCard i := by
    ext S
    simp [Finset.mem_powersetCard, Finset.subset_univ]
  rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **The dimension count.**  The number of multilinear monomials of degree `≤ m` in `n` variables (subsets of
size `≤ m`) is `Σ_{i≤m} C(n,i)` — the dimension of the space of degree-`≤m` multilinear polynomials. -/
theorem card_subsets_card_le (n m : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ m)).card
      = ∑ i ∈ Finset.range (m + 1), n.choose i := by
  have hmem : Set.MapsTo (fun S : Finset (Fin n) => S.card)
      (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ m) : Set (Finset (Fin n)))
      (Finset.range (m + 1)) := by
    intro S hS
    rw [Finset.mem_coe, Finset.mem_filter] at hS
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le hS.2
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  have hfiber : (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ m)).filter
        (fun S => S.card = i)
      = Finset.univ.filter (fun S : Finset (Fin n) => S.card = i) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro S _
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  rw [hfiber, card_subsets_card_eq]

/-- `Σ_{i≤n} C(n,i) = 2ⁿ`: the full dimension equals the number of functions on the cube (sanity check that the
degree-`≤m` count is a genuine fraction of `2ⁿ`). -/
theorem card_subsets_card_le_self (n : ℕ) :
    (Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ n)).card = 2 ^ n := by
  rw [card_subsets_card_le, Nat.sum_range_choose]

/-- **The counting core of the dimension argument.**  If the coefficient space `M → 𝔽` of low-degree
polynomials surjects onto the function space `A → 𝔽` (i.e. every function on `A` is realised), and `|𝔽| ≥ 2`,
then `|A| ≤ |M|`.  Composed with `card_subsets_card_le` (`|M| = Σ_{i≤m} C(n,i)`), this bounds `|A|` by the
dimension. -/
theorem card_le_of_surjective {A M F : Type*}
    [Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M] [Fintype F]
    (hF : 1 < Fintype.card F) (φ : (M → F) → (A → F)) (hsurj : Function.Surjective φ) :
    Fintype.card A ≤ Fintype.card M := by
  have h := Fintype.card_le_of_surjective φ hsurj
  rw [Fintype.card_fun, Fintype.card_fun] at h
  exact (Nat.pow_le_pow_iff_right hF).mp h

end PallLean.Paper93.DeepMath.PathB.Dimension

#print axioms PallLean.Paper93.DeepMath.PathB.Dimension.card_subsets_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.Dimension.card_le_of_surjective
