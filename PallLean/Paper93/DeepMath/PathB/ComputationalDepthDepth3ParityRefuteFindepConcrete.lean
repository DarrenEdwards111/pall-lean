import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorShallowFindep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTail

/-!
# Block-DT model, route-2 step [159]: tail-abstracted m-free single-DNF parity refutation

Brick [158] (`dnf_not_parity_findep`) refutes parity for a width-`≤ w` DNF under the m-free,
F-independent budget hypothesis `hsmall` — the sum of the low-star tail, the high-star tail, and the
single geometric deep-cap term being `< 1`.  Here we abstract the two opaque star-tails behind
explicit bounds `Blo`/`Bhi`, reducing `hsmall` to a single clean numeric gap

  `(r')^s / (1 - r') + Blo + Bhi < 1`,   `r' = (2p/(1-p))(4w+1)`,

exactly mirroring the (non-m-free, F-dependent) `parity_refuted_of_tails` (brick 64) but with the
m-free geometric cap in place of the `card`-factor cap.  Instantiating `Blo`/`Bhi` with the Markov
star-tail bounds `stars_tail_le` / `stars_tail_ge` then discharges the refutation at a concrete gap.

* `dnf_not_parity_findep_of_tails` — `low ≤ Blo`, `high ≤ Bhi`, and `cap + Blo + Bhi < 1` ⟹ the
  width-`≤ w` DNF disagrees with parity on some subcube.  m-free; F enters only through `Bhi`.

This closes the *concentration* step for the m-free single-gate story: the refutation now follows
from a clean numeric gap on the tails, no opaque `hsmall`.  It does NOT close `parity ∉ AC⁰`, which
additionally needs the multi-round depth-`d` reduction (route-2 option (b)).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **m-free single-DNF parity refutation, via the star-count tail bounds.**  If the low/high star
tails are bounded by `Blo`/`Bhi` and the m-free geometric deep-cap plus the two tails total `< 1`,
then the width-`≤ w` DNF `D` disagrees with parity at some subcube point.  This is the m-free,
F-independent analog of `parity_refuted_of_tails`: the cap is the geometric
`(r')^s/(1-r')` with `r' = (2p/(1-p))(4w+1)`, carrying no clause-count `m` and no `F`-dependent
`card` factor. -/
theorem dnf_not_parity_findep_of_tails {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (D : List (Clause n))
    (hcons : ∀ T ∈ D, Consistent T) (hnd : ∀ T ∈ D, (T.lits.map litVarOf).Nodup)
    (hw : ∀ T ∈ D, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    {Blo Bhi : ℚ}
    (hlo : (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
        pweight p ρ) ≤ Blo)
    (hhi : (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
        pweight p ρ) ≤ Bhi)
    (hgap : ((2 * p / (1 - p)) * (4 * w + 1)) ^ s
              / (1 - (2 * p / (1 - p)) * (4 * w + 1)) + Blo + Bhi < 1) :
    ∃ (ρ : Restriction n) (x : Fin n → Bool),
      DTree.agreeRestriction ρ x ∧ DTree.dnfValue D x ≠ DTree.parity x := by
  apply dnf_not_parity_findep hp0 hp3 D hcons hnd hw hr'
  -- treat the geometric deep-cap as a single atom so `linarith` never normalizes the denominator
  set cap := ((2 * p / (1 - p)) * (4 * w + 1)) ^ s
      / (1 - (2 * p / (1 - p)) * (4 * w + 1)) with hcap
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dnf_not_parity_findep_of_tails
