import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShallowAll
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PWeightExtends

/-!
# AC⁰ reduction, foundation 23: subcube-relative switching existence (branch only)

The conditional form of `exists_shallow_all` (brick 6): a restriction making every bottom gate shallow
that moreover **extends a fixed base `τ`**.  The union bound is run on the conditional measure — total mass
`((1-p)/2)^(n - stars τ)` (brick 22) instead of `1` — while each gate's bad weight is still capped by the
unconditional `descent_switching_le` (brick 60), which holds for *any* bad set, including one inside the
extension box.  So if `#gates · cap < ((1-p)/2)^(n - stars τ)` then some good restriction extends `τ`.

* `exists_shallow_all_extends` — `#gates · cap < ((1-p)/2)^(n - stars τ)` ⟹ `∃ ρ`, `Extends τ ρ` and every
  gate's canonical tree is shallow under `ρ`.

This is the primitive the multi-round coordinate budget needs: applying it with `τ` = the previous round's
restriction keeps every later round inside the earlier subcube, so the survivor sets *nest* and the final
common subcube is a single restriction whose stars can be tracked.

## Honest scope

This delivers the *shallowness on `τ`'s subcube*.  Driving the coordinate budget to a contradiction still
needs a **survivor lower bound** — that a good extending restriction keeps `stars ρ` large (a conditional
star-tail concentration, the dual of bricks 63–64 on the `τ`-free coordinates).  That concentration is not
proved here; we do not paper over it.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Subcube-relative switching existence.**  If the conditional union bound
`#gates · cap < ((1-p)/2)^(n - stars τ)` holds, some restriction *extending `τ`* makes every gate's
canonical tree shallow. -/
theorem exists_shallow_all_extends {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (w F s : ℕ)
    (τ : Fin n → Option Bool) (G : Finset (List (Clause n)))
    (hcons : ∀ g ∈ G, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ G, ∀ T ∈ g, T.lits.length ≤ w)
    (hsmall : (G.card : ℚ)
        * ((2 * p / (1 - p)) ^ s
            * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ))
        < ((1 - p) / 2) ^ (n - stars τ)) :
    ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s := by
  classical
  by_contra hcon
  push_neg at hcon
  set cap : ℚ := (2 * p / (1 - p)) ^ s
    * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) with hcap
  have hp1 : p ≤ 1 := by linarith
  have hpw_nonneg : ∀ ρ : Fin n → Option Bool, 0 ≤ pweight p ρ :=
    fun ρ => pweight_nonneg hp0 hp1 ρ
  have key : ((1 - p) / 2) ^ (n - stars τ) ≤ (G.card : ℚ) * cap := by
    calc ((1 - p) / 2) ^ (n - stars τ) = ∑ σ ∈ extBox τ, pweight p σ := (pweight_sum_extends p τ).symm
      _ ≤ ∑ σ ∈ extBox τ, ∑ g ∈ G,
            (if s ≤ (canonicalDTree g w F σ).depth then pweight p σ else 0) := by
        apply Finset.sum_le_sum
        intro σ hσ
        rw [mem_extBox] at hσ
        obtain ⟨g, hg, hgσ⟩ := hcon σ hσ
        have hnn : ∀ g' ∈ G,
            (0 : ℚ) ≤ (if s ≤ (canonicalDTree g' w F σ).depth then pweight p σ else 0) := by
          intro g' _
          split
          · exact hpw_nonneg σ
          · exact le_refl 0
        have hsingle := Finset.single_le_sum hnn hg
        rwa [if_pos hgσ] at hsingle
      _ = ∑ g ∈ G, ∑ σ ∈ extBox τ,
            (if s ≤ (canonicalDTree g w F σ).depth then pweight p σ else 0) := Finset.sum_comm
      _ ≤ ∑ _g ∈ G, cap := by
        apply Finset.sum_le_sum
        intro g hg
        rw [← Finset.sum_filter]
        exact descent_switching_le hp0 hp3 g (hcons g hg) (hnd g hg) w (hw g hg) F s
          (fun σ hσ => (Finset.mem_filter.mp hσ).2)
      _ = (G.card : ℚ) * cap := by rw [Finset.sum_const, nsmul_eq_mul]
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.exists_shallow_all_extends
