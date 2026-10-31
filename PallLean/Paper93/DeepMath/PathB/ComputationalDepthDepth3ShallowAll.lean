import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PNormalize

/-!
# AC⁰ reduction, foundation 6: a restriction collapsing all bottom gates (branch only)

The probabilistic heart of one collapse round: a *single* restriction makes **every** bottom gate's
canonical tree shallow.  Each gate is bad (deep) with p-biased weight `≤ cap = (2p/(1-p))^s · (4^w+1)^F`
(brick 60); a union bound over the gates caps the total bad weight at `#gates · cap`, so once that is
`< 1` some restriction is good for all gates simultaneously.

* `exists_shallow_all` — if `#gates · cap < 1` then there is a restriction making every gate's canonical
  tree have depth `< s`.

This is the existence step the substitution (brick 70) + merge (brick 69) act on to realise one collapse
round; iterating it down to depth 2 (brick 35) is the remaining structural induction.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **A restriction collapsing all bottom gates.**  If the union bound `#gates · cap < 1` holds, some
restriction makes every gate's canonical tree shallow. -/
theorem exists_shallow_all {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ)
    (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hsmall : (G.card : ℚ)
        * ((2 * p / (1 - p)) ^ s
            * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ)) < 1) :
    ∃ ρ : Fin n → Option Bool, ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s := by
  classical
  by_contra hcon
  push_neg at hcon
  set cap : ℚ := (2 * p / (1 - p)) ^ s
    * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) with hcap
  have hpw_nonneg : ∀ ρ : Fin n → Option Bool, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 (by linarith) ρ
  have key : (1 : ℚ) ≤ (G.card : ℚ) * cap := by
    calc (1 : ℚ) = ∑ ρ : Fin n → Option Bool, pweight p ρ := (pweight_sum_eq_one p).symm
      _ ≤ ∑ ρ : Fin n → Option Bool, ∑ g ∈ G,
            (if s ≤ (canonicalDTree g w F ρ).depth then pweight p ρ else 0) := by
        apply Finset.sum_le_sum
        intro ρ _
        obtain ⟨g, hg, hgρ⟩ := hcon ρ
        have hnn : ∀ g' ∈ G,
            (0 : ℚ) ≤ (if s ≤ (canonicalDTree g' w F ρ).depth then pweight p ρ else 0) := by
          intro g' _
          split
          · exact hpw_nonneg ρ
          · exact le_refl 0
        have hsingle := Finset.single_le_sum hnn hg
        rwa [if_pos hgρ] at hsingle
      _ = ∑ g ∈ G, ∑ ρ : Fin n → Option Bool,
            (if s ≤ (canonicalDTree g w F ρ).depth then pweight p ρ else 0) := Finset.sum_comm
      _ ≤ ∑ _g ∈ G, cap := by
        apply Finset.sum_le_sum
        intro g hg
        rw [← Finset.sum_filter]
        exact descent_switching_le hp0 hp3 g (hcons g hg) (hnd g hg) w (hw g hg) F s
          (fun σ hσ => (Finset.mem_filter.mp hσ).2)
      _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_shallow_all
