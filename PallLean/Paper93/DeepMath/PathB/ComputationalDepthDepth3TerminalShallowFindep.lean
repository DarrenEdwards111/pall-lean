import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3OneRoundFindep

/-!
# Block-DT model, route-2 step [165]: the m-FREE block-level terminal switching (option (b))

The terminal step of the depth-`d` argument: the bottom `DNF` `cs`, reached at the common base `σ`,
must be made shallow so the parity capstone fires.  The m-ful engine `parity_not_altO` discharges its
terminal `hterm` over the **bit-level** tree `canonicalDT` (base `2wm`).  Here we give the m-free,
**block-level** terminal over `canonicalDTree` (base `4w+1`, no clause count `m`), built directly from
the m-free conditional survivor [164] at the singleton gate set `{cs}`.

No `canonicalDT ↔ canonicalDTree` depth bridge is needed: `TightParity` shows the relativized parity
bound is generic over decision trees, so the block-level capstone `tower_not_parity` /
`iterated_not_parity` consumes exactly `(canonicalDTree cs w F σ').depth < stars σ'`.

* `terminal_shallow_of_survivor_findep` — under the m-free conditional budget at base `σ`, some `σ'`
  extends `σ`, has `stars σ' < F`, and makes `(canonicalDTree cs w F σ').depth < stars σ'`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The m-free block-level terminal switching.**  For a single bottom `DNF` `cs` at base `σ` with
`s ≤ stars σ` available, the m-free conditional budget yields `σ'` extending `σ` whose surviving block
tree is shallow: `(canonicalDTree cs w F σ').depth < stars σ'`.  The deep-cap is the m-free geometric
`geom = (r')^s/(1-r')`, `r' = (2p/(1-p))(4w+1)`; `stars σ' < F` follows from `hF : n < F`. -/
theorem terminal_shallow_of_survivor_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w : ℕ} [NeZero w] (F s : ℕ) (hF : n < F) (hs : 1 ≤ s)
    (cs : List (Clause n)) (σ : Fin n → Option Bool)
    (hcons : ∀ T ∈ cs, Consistent T) (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup)
    (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hsmall :
        (∑ σ' ∈ (extBox σ).filter (fun σ' => SwitchingCounting.stars σ' ≤ s - 1), pweight p σ')
          + ((((2 * p / (1 - p)) * (4 * w + 1)) ^ s
                / (1 - (2 * p / (1 - p)) * (4 * w + 1)))
              * ((1 - p) / 2) ^ (n - SwitchingCounting.stars σ))
        < ((1 - p) / 2) ^ (n - SwitchingCounting.stars σ)) :
    ∃ σ' : Fin n → Option Bool, Extends σ σ' ∧ SwitchingCounting.stars σ' < F ∧
      (canonicalDTree cs w F σ').depth < SwitchingCounting.stars σ' := by
  obtain ⟨ρ, hext, hshallow, hk⟩ :=
    exists_shallow_survivor_extends_findep hp0 hp3 F s (s - 1) σ {cs}
      (by intro g hg; rw [Finset.mem_singleton] at hg; subst hg; exact hcons)
      (by intro g hg; rw [Finset.mem_singleton] at hg; subst hg; exact hnd)
      (by intro g hg; rw [Finset.mem_singleton] at hg; subst hg; exact hw)
      hr'
      (by
        -- the singleton budget: `G.card = 1`, so the `card` factor drops out
        rw [Finset.card_singleton]
        simpa using hsmall)
  have hsρ : s ≤ SwitchingCounting.stars ρ := by omega
  have hdepth : (canonicalDTree cs w F ρ).depth < s :=
    hshallow cs (Finset.mem_singleton_self cs)
  have hstarsF : SwitchingCounting.stars ρ < F :=
    lt_of_le_of_lt (by rw [stars]; exact le_trans (Finset.card_le_univ _) (by simp)) hF
  exact ⟨ρ, hext, hstarsF, lt_of_lt_of_le hdepth hsρ⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.terminal_shallow_of_survivor_findep
