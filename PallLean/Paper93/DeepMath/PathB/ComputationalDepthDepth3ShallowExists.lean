import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PNormalize

/-!
# Block-DT model, foundation 61: branching holography, step 4s — a shallow restriction exists (branch only)

The lower-bound bridge: the switching probability bound (brick 60) is a *union/averaging* statement, so
when the bad weight is `< 1` it cannot account for the whole probability mass — some restriction is good
(shallow).  This is the form the AC⁰ lower bound consumes: "after a random restriction the canonical tree
is shallow with positive probability, hence for some restriction."

* `exists_shallow_restriction` — if `(2p/(1-p))^s · (4^w+1)^F < 1` then `∃ ρ, depth (canonicalDTree …) < s`.

Combined with "parity restricted to `ℓ` free coordinates needs decision-tree depth `ℓ`" (the matching
lower bound), this is the switching step of `parity ∉ AC⁰`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **A shallow restriction exists.**  If the switching bound is `< 1`, the bad set cannot be everything:
some restriction `ρ` makes the canonical tree shallow (`depth < s`). -/
theorem exists_shallow_restriction {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F s : ℕ)
    (hsmall : (2 * p / (1 - p)) ^ s
        * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) < 1) :
    ∃ ρ : Fin n → Option Bool, (canonicalDTree cs w F ρ).depth < s := by
  by_contra hcon
  push_neg at hcon
  have hbad : ∀ σ ∈ (Finset.univ : Finset (Fin n → Option Bool)),
      s ≤ (canonicalDTree cs w F σ).depth := fun σ _ => hcon σ
  have h := descent_switching_le hp0 hp3 cs hcons hnd w hw F s hbad
  rw [pweight_sum_eq_one] at h
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_shallow_restriction
