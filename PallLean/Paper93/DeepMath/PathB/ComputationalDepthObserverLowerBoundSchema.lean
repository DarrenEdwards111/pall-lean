import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverNeciporukCalibration

/-!
# The observer lower-bound schema: what all the proved rungs share, and the one open ingredient

Three rungs are now proved through the observer-boundary invariant — resolution proof-space (Tseitin),
AC⁰[p] degree (Razborov–Smolensky), and Nečiporuk formula size.  This file extracts the **single structure**
they share, as a one-line meta-theorem, and pins down precisely the ingredient that is missing for the
general (P vs NP) rung.

## The schema

Every observer lower bound has exactly two ingredients:

1. **A boundary lower bound from non-mergeability** (the *universal* half): the target function forces the
   observer to keep many behaviors apart, so its boundary is `≥ lb`.  This is always the same principle —
   `many_nonmergeable_sectors_force_boundary` / `faithful_separated_forces_boundary` /
   `separated_forces_blockBoundary` / the RS dimension count.
2. **A resource↔boundary bridge** (the *model-specific* half): in the model, an object of resource (size)
   `R` has boundary `≤ bridge(R)` — a *small* object is a *low-boundary* observer.

Combine them and the size is forced up: `lb ≤ boundary(o) ≤ bridge(size(o))`, so `bridge(size(o)) ≥ lb`.

That is the entire method, in one theorem (`observer_resource_lower_bound`).

## The instances

| rung | `size` | `boundary` | `bridge(R)` | `lb` |
|---|---|---|---|---|
| resolution proof-space | `totalSpace` | `totalSpace` | `R` (identity) | `c·t` (Tseitin) |
| AC⁰[p] degree | `#monomials` | `finrank feature` | `R` (identity) | `|G|` (RS) |
| Nečiporuk formula | `litCount` | `formulaTotalBoundary` | `4·R + #blocks` | `m·(2^b−1)` (`hardF`) |

`hardF_litCount_via_schema` below **rederives the Nečiporuk formula bound by applying the schema** to the
Nečiporuk bridge (`formulaTotalBoundary_le_size`) and the forced total boundary
(`hardF_totalBoundary_ge`) — demonstrating the schema genuinely produces a real lower bound, not just names
one.

## The one open ingredient (P vs NP)

For the general machine-decomposition rung, the **bridge half is structurally available** (a small machine is
a low-boundary observer — the Route-F crossing-sequence bound).  What is missing is ingredient (1) *under
every admissible decomposition*: that SAT forces boundary `≥ ω(log n)` for **every** faithful observer.  That
is `CookLevinFrontierHyp` — and `equality_decomposition_gap` shows it cannot come from a single
decomposition.  The schema makes precise that this — and only this — is the gap.
-/

namespace PallLean.Paper93.DeepMath.PathB.ObserverSchema

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.NecHard
open PallLean.Paper93.DeepMath.PathB.ObserverNeciporuk
open BFormula
open scoped BigOperators

/-- **The observer lower-bound schema (meta-theorem).**  Given a `bridge` with `boundary o ≤ bridge (size o)`
for every object (a small object is a low-boundary observer), and a target forcing `lb ≤ boundary o`, the
resource is forced: `lb ≤ bridge (size o)`.  Every observer lower bound in this development is an instance. -/
theorem observer_resource_lower_bound {Obj : Type*} (size boundary : Obj → ℕ) (bridge : ℕ → ℕ)
    (hbridge : ∀ o, boundary o ≤ bridge (size o)) {lb : ℕ} (o : Obj) (hforced : lb ≤ boundary o) :
    lb ≤ bridge (size o) :=
  le_trans hforced (hbridge o)

/-! ## Instance: rederiving the Nečiporuk formula bound through the schema -/

variable {b m : ℕ}

/-- **Forced total boundary (ingredient 1 for `hardF`).**  Every formula computing `hardF` has total observer
boundary `≥ m·(2^b−1)` over the Nečiporuk partition: each of the `m` address blocks is forced to boundary
`≥ 2^b−1` (`hardF_blockBoundary_ge`), and the data block contributes `≥ 0`. -/
theorem hardF_totalBoundary_ge (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    m * (Dsize b - 1) ≤ formulaTotalBoundary Finset.univ (blkS (b := b) (m := m)) F := by
  classical
  unfold formulaTotalBoundary
  rw [Fintype.sum_option]
  have hper : ∀ k : Fin m, Dsize b - 1 ≤ formulaBlockBoundary (blkS (some k)) F := by
    intro k; rw [blkS_some]; exact hardF_blockBoundary_ge k F hF
  have hsum : m * (Dsize b - 1) ≤ ∑ k : Fin m, formulaBlockBoundary (blkS (some k)) F := by
    have hconst : ∑ _k : Fin m, (Dsize b - 1) = m * (Dsize b - 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [← hconst]
    exact Finset.sum_le_sum (fun k _ => hper k)
  exact le_trans hsum (Nat.le_add_left _ _)

/-- **The Nečiporuk formula bound, rederived through the schema.**  Apply `observer_resource_lower_bound` with
`size = litCount`, `boundary = formulaTotalBoundary`, `bridge R = 4·R + (m+1)` (the Nečiporuk bridge
`formulaTotalBoundary_le_size`), and `lb = m·(2^b−1)` (the forced boundary `hardF_totalBoundary_ge`):
`m·(2^b−1) ≤ 4·litCount F + (m+1)`.  Reproduces `hardF_litCount_lower_opt`, but *assembled by the schema*. -/
theorem hardF_litCount_via_schema (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    m * (Dsize b - 1) ≤ 4 * BFormula.litCount F + (m + 1) := by
  have hbridge : ∀ G : BFormula (nn b m),
      formulaTotalBoundary Finset.univ (blkS (b := b) (m := m)) G
        ≤ 4 * BFormula.litCount G + (m + 1) := by
    intro G
    have h := formulaTotalBoundary_le_size Finset.univ (blkS (b := b) (m := m)) G blkS_disj blkS_cover
    rwa [Finset.card_univ, Fintype.card_option, Fintype.card_fin] at h
  exact observer_resource_lower_bound BFormula.litCount
    (formulaTotalBoundary Finset.univ (blkS (b := b) (m := m))) (fun R => 4 * R + (m + 1))
    hbridge F (hardF_totalBoundary_ge F hF)

/-- Headline (division form), rederived through the schema: `litCount F ≥ (m·(2^b−1) − (m+1)) / 4`. -/
theorem hardF_litCount_via_schema_div (F : BFormula (nn b m)) (hF : ∀ x, BFormula.eval F x = hardF x) :
    (m * (Dsize b - 1) - (m + 1)) / 4 ≤ BFormula.litCount F := by
  have h := hardF_litCount_via_schema F hF
  have key : m * (Dsize b - 1) - (m + 1) ≤ 4 * BFormula.litCount F := by omega
  calc (m * (Dsize b - 1) - (m + 1)) / 4
      ≤ (4 * BFormula.litCount F) / 4 := Nat.div_le_div_right key
    _ = BFormula.litCount F := by rw [Nat.mul_div_cancel_left _ (by norm_num)]

end PallLean.Paper93.DeepMath.PathB.ObserverSchema

#print axioms PallLean.Paper93.DeepMath.PathB.ObserverSchema.observer_resource_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ObserverSchema.hardF_litCount_via_schema
