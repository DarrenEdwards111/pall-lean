import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCRestrictionSwitchingVariance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACCOverlapStar

/-!
# Spread overlap: the genuine Håstad regime

The star probe (`…ACCOverlapStar`) showed concentrated overlap is *removable*: all overlap sits in a shared core,
and killing the core restores disjointness.  This file tests the real enemy — **spread overlap** with no small core
to kill — via a *design family* (bounded pairwise intersections `|S_i ∩ S_j| ≤ λ`, but spread across distinct
coordinates).

The decisive comparison: the **variance bound does not distinguish** star from spread (both give
`Var ≤ k·s·p + k²·λ·p`), so the second moment alone cannot tell the easy case from the hard one.  What distinguishes
them is the **surgery cost** — the number of coordinates one must kill to disjointify, which equals the size of the
*overlap‑coordinate set* `overlapCoords = {v : v lies in ≥ 2 supports}`:

* **star**: `overlapCoords ⊆ core` — small, so killing `|core|` coordinates disjointifies (`core_surgery`);
* **spread**: `overlapCoords` is large, and `disjointify_requires_kill` proves *any* live set on which the supports
  are disjoint must have `overlapCoords` entirely dead — so disjointifying costs killing `≥ |overlapCoords|`
  coordinates.  When `overlapCoords` is large, no small killed set works, and a heavily‑killed restriction leaves
  too few live coordinates for the cell bridge.

So the genuine `NP ⊄ ACC⁰` wall is **spread overlap with large `overlapCoords`** — overlap no small killed set can
remove — exactly the regime where core surgery fails.

## What is proved (clean axioms, no `sorry`)

* `design_variance_le` — `Var[X] ≤ k·s·p + k²·λ·p` under bounded pairwise intersection `λ` (variance controllable
  when `λ` is small — the *same* bound as the star).
* `incidence`, `overlapCoords`, `disjointOnLive` — the spread‑overlap structure.
* `disjointify_requires_kill` — **the surgery cost**: making the supports disjoint on a live set forces every
  overlap coordinate dead (`Disjoint overlapCoords L`).
* `card_overlapCoords_le_compl` — hence `|overlapCoords| ≤ #dead`: disjointifying costs `≥ |overlapCoords|` kills.
* `star_overlapCoords_subset_core` — the star is the small‑`overlapCoords` (removable) case.

## Honest reading

`design_variance_le` confirms the second moment cannot separate easy from hard overlap (both bound by `k²λp`).
The separation is `overlapCoords`: small ⇒ surgically removable (star), large ⇒ not (`disjointify_requires_kill`
plus a large `overlapCoords`).  The remaining `NP ⊄ ACC⁰` difficulty is precisely a support family with **small
pairwise intersections yet large `overlapCoords`** — spread overlap — where killing few coordinates cannot
disjointify and killing many destroys the live set.  That is the Håstad regime, now isolated by an explicit
quantity.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACCOverlapDesign

open PallLean.Paper93.DeepMath.PathB.ACCRestrictionSwitchingVariance

variable {n k : ℕ}

/-! ## Variance under spread (bounded pairwise) overlap -/

/-- **Variance under bounded pairwise overlap (proved): `Var[X] ≤ k·s·p + k²·λ·p`** when `|S_i ∩ S_j| ≤ λ` for all
`i ≠ j`.  Identical in shape to the star bound — the second moment cannot distinguish concentrated from spread
overlap. -/
theorem design_variance_le (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (supports : Fin k → Finset (Fin n))
    (s lam : ℕ) (hfan : ∀ i, (supports i).card ≤ s)
    (hpair : ∀ i j, i ≠ j → (supports i ∩ supports j).card ≤ lam) :
    variance p supports ≤ ((k * s + k ^ 2 * lam : ℕ) : ℝ) * p := by
  have hrow : ∀ i, ∑ j, (supports i ∩ supports j).card ≤ s + k * lam := by
    intro i
    rw [← Finset.add_sum_erase Finset.univ
        (fun j => (supports i ∩ supports j).card) (Finset.mem_univ i), Finset.inter_self]
    have he : ∑ j ∈ Finset.univ.erase i, (supports i ∩ supports j).card
        ≤ ∑ _j ∈ Finset.univ.erase i, lam :=
      Finset.sum_le_sum (fun j hj => hpair i j (Finset.ne_of_mem_erase hj).symm)
    have h2 : (Finset.univ.erase i).card ≤ k := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]; omega
    calc (supports i).card + ∑ j ∈ Finset.univ.erase i, (supports i ∩ supports j).card
        ≤ s + ∑ _j ∈ Finset.univ.erase i, lam := Nat.add_le_add (hfan i) he
      _ = s + (Finset.univ.erase i).card * lam := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ s + k * lam := Nat.add_le_add_left (Nat.mul_le_mul h2 (le_refl _)) s
  have htot : ∑ i, ∑ j, (supports i ∩ supports j).card ≤ k * s + k ^ 2 * lam := by
    calc ∑ i, ∑ j, (supports i ∩ supports j).card
        ≤ ∑ _i : Fin k, (s + k * lam) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = k * (s + k * lam) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ = k * s + k ^ 2 * lam := by ring
  unfold variance
  calc ∑ i, ∑ j, cov p (supports i) (supports j)
      ≤ ∑ i, ∑ j, ((supports i ∩ supports j).card : ℝ) * p :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => cov_le p hp0 hp1 _ _))
    _ = (∑ i, ∑ j, ((supports i ∩ supports j).card : ℝ)) * p := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
    _ = ((∑ i, ∑ j, (supports i ∩ supports j).card : ℕ) : ℝ) * p := by push_cast; ring
    _ ≤ ((k * s + k ^ 2 * lam : ℕ) : ℝ) * p := by
        apply mul_le_mul_of_nonneg_right _ hp0; exact_mod_cast htot

/-! ## The overlap‑coordinate set and the surgery cost -/

/-- How many supports a coordinate lies in. -/
def incidence (supports : Fin k → Finset (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => v ∈ supports j)).card

/-- The set of overlap coordinates — those lying in at least two supports. -/
def overlapCoords (supports : Fin k → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => 2 ≤ incidence supports v)

/-- The supports are disjoint on the live set `L`: every live coordinate lies in at most one support. -/
def disjointOnLive (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n)) : Prop :=
  ∀ v ∈ L, incidence supports v ≤ 1

/-- **The surgery cost (proved): disjointifying on `L` forces every overlap coordinate dead.**  If the supports are
disjoint on `L`, then `overlapCoords` is disjoint from `L` — to remove all overlap one must kill every
overlap coordinate. -/
theorem disjointify_requires_kill (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : disjointOnLive supports L) : Disjoint (overlapCoords supports) L := by
  rw [Finset.disjoint_left]
  intro v hv hvL
  rw [overlapCoords, Finset.mem_filter] at hv
  have := h v hvL
  omega

/-- **The kill cost is at least `|overlapCoords|` (proved).**  Any live set on which the supports are disjoint
leaves at most `n − |overlapCoords|` live coordinates. -/
theorem card_overlapCoords_le_compl (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : disjointOnLive supports L) :
    (overlapCoords supports).card ≤ Fintype.card (Fin n) - L.card := by
  have hsub : overlapCoords supports ⊆ Lᶜ := fun v hv =>
    Finset.mem_compl.mpr (Finset.disjoint_left.mp (disjointify_requires_kill supports L h) hv)
  calc (overlapCoords supports).card ≤ Lᶜ.card := Finset.card_le_card hsub
    _ = Fintype.card (Fin n) - L.card := Finset.card_compl L

/-! ## The star is the small‑`overlapCoords` (removable) case -/

/-- **The star has small overlap coordinates (proved): `overlapCoords ⊆ core`.**  Every coordinate in two star
supports lies in the core (else it would be in two disjoint petals).  So the star is the surgically‑removable case;
spread designs with large `overlapCoords` are not. -/
theorem star_overlapCoords_subset_core (core : Finset (Fin n)) (petals : Fin k → Finset (Fin n))
    (hpet : ∀ i j, i ≠ j → Disjoint (petals i) (petals j)) :
    overlapCoords (PallLean.Paper93.DeepMath.PathB.ACCOverlapStar.starSupport core petals) ⊆ core := by
  intro v hv
  rw [overlapCoords, Finset.mem_filter] at hv
  by_contra hvc
  have hcard : 1 < (Finset.univ.filter
      (fun l => v ∈ PallLean.Paper93.DeepMath.PathB.ACCOverlapStar.starSupport core petals l)).card := by
    have := hv.2; unfold incidence at this; omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  have hvi := (Finset.mem_filter.mp hi).2
  have hvj := (Finset.mem_filter.mp hj).2
  unfold PallLean.Paper93.DeepMath.PathB.ACCOverlapStar.starSupport at hvi hvj
  rw [Finset.mem_union] at hvi hvj
  exact Finset.disjoint_left.mp (hpet i j hij) (hvi.resolve_left hvc) (hvj.resolve_left hvc)

end PallLean.Paper93.DeepMath.PathB.ACCOverlapDesign

#print axioms PallLean.Paper93.DeepMath.PathB.ACCOverlapDesign.design_variance_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACCOverlapDesign.disjointify_requires_kill
#print axioms PallLean.Paper93.DeepMath.PathB.ACCOverlapDesign.card_overlapCoords_le_compl
#print axioms PallLean.Paper93.DeepMath.PathB.ACCOverlapDesign.star_overlapCoords_subset_core
