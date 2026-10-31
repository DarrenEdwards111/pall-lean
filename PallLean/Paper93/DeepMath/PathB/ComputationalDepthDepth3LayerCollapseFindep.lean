import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SurvivorShallowFindep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LayerCollapseAt

/-!
# Block-DT model, route-2 step [162]: the m-FREE producing OR-layer collapse

The existing producing round `collapse_or_layer` (brick on `ComputationalDepthDepth3LayerCollapse`)
obtains its survivor `ρ` from the **m-ful** `exists_shallow_all`, whose budget carries the
`F`-dependent `card (Fin F → Option (Fin w → Option (Option Bool)))` factor — exactly the factor that
makes the depth-`d` tower vacuous for `d ≥ 1`.  Here we give the **m-free** producing round: the
survivor comes from the value-augmented, `F`-independent `exists_survivor_shallow_findep` (brick
[157]), whose budget is the three-tail form with base `4w+1` and **no clause-count `m`**.

The structural collapse itself is unchanged — we hand the m-free survivor straight to the
parameter-agnostic `collapse_or_layer_at`.  This is the first rung of route-2 option (b): the m-free
budget now drives a *producing* layer collapse, so it can seed the iterated tower.

* `collapse_or_layer_findep` — under the m-free three-tail budget, some `ρ` makes the `OR`-of-`AND`-
  of-`DNF` layer `EquivOn`-collapse to an `OR`-of-`CNF` with every clause of width `< s`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

namespace Layered

variable {n : ℕ}

/-- **The m-free producing `OR`-layer collapse.**  Identical conclusion to `collapse_or_layer`, but
the survivor is produced by the `m`-free, `F`-independent switching budget [157] (base `4w+1`, the
three star-tails plus the geometric deep-cap), not by the `m`-ful `exists_shallow_all`.  No
`hF : n < F` is needed: `exists_survivor_shallow_findep` already returns `stars ρ < F` directly. -/
theorem collapse_or_layer_findep {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] (gates : List (Finset (List (Clause n))))
    (Gtot : Finset (List (Clause n)))
    (hsub : ∀ G ∈ gates, G ⊆ Gtot)
    (hcons : ∀ g ∈ Gtot, ∀ T ∈ g, Consistent T)
    (hnd : ∀ g ∈ Gtot, ∀ T ∈ g, (T.lits.map litVarOf).Nodup)
    (hw : ∀ g ∈ Gtot, ∀ T ∈ g, T.lits.length ≤ w)
    (hr' : (2 * p / (1 - p)) * (4 * w + 1) < 1)
    (hsmall :
        (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => SwitchingCounting.stars ρ < s),
            pweight p ρ)
          + (∑ ρ ∈ Finset.univ.filter (fun ρ : Restriction n => F ≤ SwitchingCounting.stars ρ),
              pweight p ρ)
          + (Gtot.card : ℚ)
              * (((2 * p / (1 - p)) * (4 * w + 1)) ^ s
                  / (1 - (2 * p / (1 - p)) * (4 * w + 1))) < 1) :
    ∃ ρ : Fin n → Option Bool,
      EquivOn ρ (gOr (gates.map (fun G => gAnd (G.toList.map dnf))))
          (gOr (gates.map (fun G => cnf (G.toList.flatMap
            (fun g => dtreeToCNF (canonicalDTree g w F ρ))))))
        ∧ (∀ G ∈ gates, ∀ C ∈ G.toList.flatMap (fun g => dtreeToCNF (canonicalDTree g w F ρ)),
            C.lits.length < s) := by
  obtain ⟨ρ, _hge, hltF, hshallow⟩ :=
    exists_survivor_shallow_findep hp0 hp3 Gtot hcons hnd hw hr' hsmall
  have hsh : ∀ G ∈ gates, ∀ g ∈ G, (canonicalDTree g w F ρ).depth < s :=
    fun G hG g hg => hshallow g (hsub G hG hg)
  have hnd' : ∀ G ∈ gates, ∀ g ∈ G, ∀ T ∈ g, (T.lits.map litVarOf).Nodup :=
    fun G hG g hg T hT => hnd g (hsub G hG hg) T hT
  have hca := collapse_or_layer_at w F s gates ρ hltF hnd' hsh
  exact ⟨ρ, hca.1, hca.2.1⟩

end Layered

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.Layered.collapse_or_layer_findep
