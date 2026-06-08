import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapseAt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowSurvivor
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reduces

/-!
# AC⁰ reduction, foundation 27: one fully-assembled reduction round (branch only)

The unit the multi-round loop iterates, with every piece wired together: the conditional switching primitive
(brick 25) hands down a restriction `ρ` **extending the base `τ`** that keeps the survivors above `k` and
makes every bottom gate shallow; the restriction-given collapse (brick 26) turns the `OR`-of-`AND`-of-`DNF`
layer into an `OR`-of-`CNF`s `EquivOn ρ`; and the spine (brick 20) packages that equivalence as a one-step
`Reduces` valid on `ρ`'s subcube, with the output clauses well-formed for the next round.

* `one_round_or` — from base `τ` and the conditional union-bound budget, produce `ρ` (extending `τ`,
  `k < stars ρ`) and a `Reduces` step collapsing the layer, with `Consistent`/`Nodup`/width-`<s` outputs.

So a single round of the AC⁰ depth reduction is now a closed theorem assembled end-to-end from the
probabilistic core, the collapse, and the spine — on a *nested* subcube whose survivors are tracked.

## Honest scope

This is one round.  Iterating to depth `2` requires threading the *shape* between rounds: the collapse
absorbs two levels (`AND`-of-`DNF` → `CNF`), so the output `OR`-of-`CNF`s is a different shape than the next
round consumes, and the recursion passes through `d` distinct layer shapes (or a uniform encoding of them).
That structural threading — not any new probabilistic content — is what remains for an unconditional
`parity ∉ AC⁰`.  We state one round honestly and do not pretend the chaining is free.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **One reduction round (`OR`-layer), fully assembled.**  Given the base `τ` and the conditional
union-bound budget, there is a restriction `ρ` extending `τ` with more than `k` survivors such that the
`OR`-of-`AND`-of-`DNF` layer `Reduces` (on `ρ`'s subcube) to an `OR`-of-`CNF`s with well-formed clauses. -/
theorem one_round_or {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s k : ℕ) (hF : n < F)
    (τ : Fin n → Option Bool)
    (gates : List (Finset (List (Clause n)))) (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hcons : ∀ g ∈ Gtot, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ Gtot, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ Gtot, ∀ T ∈ g, T.lits.length ≤ w)
    (hsmall : (Gtot.card : ℚ)
          * ((2 * p / (1 - p)) ^ s
              * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ))
        + (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
        < ((1 - p) / 2) ^ (n - stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ k < stars ρ
      ∧ (∀ x, DTree.agreeRestriction ρ x →
          Reduces x (gOr (gates.map (fun G => gAnd (G.toList.map dnf))))
            (gOr (gates.map (fun G => cnf (G.toList.flatMap
              (fun g => dtreeToCNF (canonicalDTree g w F ρ)))))))
      ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)),
          Consistent C ∧ (C.lits.map litVarOf).Nodup ∧ C.lits.length < s) := by
  obtain ⟨ρ, hext, hshallowG, hstarsρ⟩ :=
    exists_shallow_survivor_extends hp0 hp3 w F s k τ Gtot hcons hnd hw hsmall
  have hstarsF : stars ρ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  have hshallow : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s :=
    fun G hG g hg => hshallowG g (hsub G hG hg)
  have hndgates : ∀ G ∈ gates, ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup :=
    fun G hG g hg => hnd g (hsub G hG hg)
  obtain ⟨hequiv, hwidth, hwf⟩ := collapse_or_layer_at w F s gates ρ hstarsF hndgates hshallow
  exact ⟨ρ, hext, hstarsρ, fun x hx => Reduces.head hequiv hx,
    fun G hG C hC => ⟨(hwf G hG C hC).1, (hwf G hG C hC).2, hwidth G hG C hC⟩⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.one_round_or
