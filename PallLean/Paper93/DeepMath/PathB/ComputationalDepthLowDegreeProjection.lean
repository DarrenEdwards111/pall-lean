import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProjectedContextualRank

/-!
# First real projection: the low-degree / low-Hamming-weight signature — calibrated honestly

The projected-rank framework (`…ProjectedContextualRank`) reduced the Book-1 A1 bridge to one object: a projection
that collapses easy high-rank rows but keeps hard-family rows distinct, *and* escapes the cheap bounded-range
deathtrap.  This file instantiates the **first concrete candidate** — the low-degree signature — and runs the
calibration the levers were built for.

A row of an `a`-bit cut matrix is a Boolean function `r : (Fin a → Bool) → Bool`.  Its **low-degree signature up
to degree `d`** is recorded here by its restriction to the **low‑Hamming‑weight inputs** `{y : hw y ≤ d}` — this is
the evaluation form of the degree‑`≤ d` ANF (the two are Möbius‑equivalent over `F₂`).  The projection is

`lowDegProj a d r = (r restricted to {y : hw y ≤ d})`.

## What is proved (clean axioms, no `sorry`)

* `lowDegProj_feature_bound` — `pcrank (lowDegProj a d) M ≤ 2^{N(a,d)}`, where `N(a,d) = #{y : hw y ≤ d}`.  For
  fixed `d`, `N(a,d) = ∑_{i≤d} C(a,i) = poly(a)`, so the feature space is `2^{poly}` — **exponential, not
  polynomial**.  (This is exactly why the projection is *not* killed by `boundedRange_cannot_be_separating`, which
  needs a *polynomial* codomain: low-degree escapes the cheap deathtrap.)
* `lowDegProj_eqMatrix_collapse_high` — every equality row of Hamming weight `> d` is sent to the **same** (zero)
  signature: low-degree cannot see a high-weight point indicator.
* `lowDegProj_eqMatrix_le` — consequently `pcrank (lowDegProj a d) (equality) ≤ N(a,d) + 1`: the projection
  **collapses the easy full‑rank equality matrix to `poly`**.  Easy-collapse: PASSES.
* `lowDegProj_merges_equality` — via the lever `easy_highRank_forces_merging`: when `N(a,d)+1 < 2^a` the projection
  is provably **not injective** on the equality rows — it genuinely merges easy high-rank rows.
* `lowDegProj_hard_survives` — via the lever `pcrank_ge_of_injOn`: the A3-survival half reduces to a concrete,
  checkable statement — *if* the hard family has `s` rows with distinct low-degree signatures, its projected rank
  is `≥ s`.

## Honest calibration verdict

The low-degree projection is the **first candidate past the cheap deathtrap**: it collapses easy high-rank
(equality → `poly`) yet has a `2^{poly}` (non-polynomial) feature space, so `boundedRange_cannot_be_separating`
does not apply.  But it does **not** automatically satisfy A1: a generic row can take up to `2^{N(a,d)}` distinct
low-degree signatures, so "poly-time ⇒ poly low-degree rank" is *not* free — it is a genuine sub-lemma.  And A3
(hard survival) reduces to `lowDegProj_hard_survives`'s hypothesis: that the hard family has super-polynomially
many distinct low-degree signatures — itself a low-degree lower bound (open for Tseitin/Majority/Goldreich rows).

So the experiment's outcome is the useful kind: low-degree is **not ruled out** (it passes easy-collapse and
escapes the deathtrap), and the two remaining obligations are now *explicit, separated sub-problems* —
(i) poly low-degree signature count for all `P`; (ii) super-poly distinct low-degree signatures for the hard
family — rather than the single opaque A1.  If (ii) fails (the hard family also collapses), this projection class
is ruled out and the next move is the SPDP / partial-derivative feature map.
-/

namespace PallLean.Paper93.DeepMath.PathB.LowDegreeProjection

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank

variable {a : ℕ}

/-- Hamming weight of a Boolean point. -/
def hw (y : Fin a → Bool) : ℕ := (Finset.univ.filter (fun i => y i = true)).card

/-- The low‑Hamming‑weight inputs (degree‑`≤ d` evaluation support). -/
abbrev LowWt (a d : ℕ) : Type := {y : Fin a → Bool // hw y ≤ d}

/-- The **low-degree projection**: restrict a row (a Boolean function on `a` bits) to the low-weight inputs. -/
def lowDegProj (a d : ℕ) : ((Fin a → Bool) → Bool) → (LowWt a d → Bool) :=
  fun r y => r y.val

/-- `pcrank` as the count of distinct projected rows (composition unfolded). -/
theorem pcrank_eq_image {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [DecidableEq R]
    (proj : (B → Bool) → R) (M : A → B → Bool) :
    pcrank proj M = (Finset.univ.image (fun x => proj (fun b => M x b))).card := by
  unfold pcrank rowsOf
  rw [Finset.image_image]
  rfl

/-- **Feature bound (proved): `pcrank ≤ 2^{N(a,d)}`.**  The number of distinct low-degree signatures is at most the
size of the signature space `2^{#low-weight inputs}` — `2^{poly}`, hence *exponential*, not polynomial.  This is
why the projection escapes the polynomial-codomain deathtrap of `boundedRange_cannot_be_separating`. -/
theorem lowDegProj_feature_bound (d : ℕ) (M : (Fin a → Bool) → (Fin a → Bool) → Bool) :
    pcrank (lowDegProj a d) M ≤ 2 ^ Fintype.card (LowWt a d) := by
  have h := pcrank_le_card_range (lowDegProj a d) M
  rwa [show Fintype.card (LowWt a d → Bool) = 2 ^ Fintype.card (LowWt a d) by
    simp [Fintype.card_bool]] at h

/-- **High-weight equality rows collapse (proved).**  A point indicator of Hamming weight `> d` has the all-zero
low-degree signature — the projection cannot distinguish it.  So all `> d`-weight equality rows merge to one. -/
theorem lowDegProj_eqMatrix_collapse_high (d : ℕ) (a0 : Fin a → Bool) (hwt : d < hw a0) :
    lowDegProj a d (fun b => eqMatrix (Fin a → Bool) a0 b) = (fun _ => false) := by
  funext y
  have hy := y.property
  have hne : a0 ≠ y.val := by intro h; rw [h] at hwt; omega
  simp [lowDegProj, eqMatrix, hne]

/-- **Easy-collapse (proved): the low-degree projection sends the full-rank equality matrix to `poly` rank.**
`pcrank (lowDegProj a d) (equality) ≤ N(a,d) + 1`: the only surviving signatures come from the `≤ d`-weight points
(one each) plus the single collapsed zero signature for every higher-weight point. -/
theorem lowDegProj_eqMatrix_le (d : ℕ) :
    pcrank (lowDegProj a d) (eqMatrix (Fin a → Bool)) ≤ Fintype.card (LowWt a d) + 1 := by
  classical
  rw [pcrank_eq_image]
  have hsub : Finset.univ.image (fun x => lowDegProj a d (fun b => eqMatrix (Fin a → Bool) x b))
      ⊆ insert (fun _ => false)
          ((Finset.univ.filter (fun x => hw x ≤ d)).image
            (fun x => lowDegProj a d (fun b => eqMatrix (Fin a → Bool) x b))) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, _, rfl⟩ := hz
    by_cases hx : hw x ≤ d
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩)
    · rw [Finset.mem_insert]
      exact Or.inl (lowDegProj_eqMatrix_collapse_high d x (by omega))
  calc (Finset.univ.image (fun x => lowDegProj a d (fun b => eqMatrix (Fin a → Bool) x b))).card
      ≤ (insert (fun _ => false)
          ((Finset.univ.filter (fun x => hw x ≤ d)).image
            (fun x => lowDegProj a d (fun b => eqMatrix (Fin a → Bool) x b)))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ.filter (fun x => hw x ≤ d)).image
            (fun x => lowDegProj a d (fun b => eqMatrix (Fin a → Bool) x b))).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ (Finset.univ.filter (fun x => hw x ≤ d)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
    _ = Fintype.card (LowWt a d) + 1 := by rw [Fintype.card_subtype]

/-- **The low-degree projection provably merges easy high-rank rows (proved, via the lever).**  When the low-degree
signature count `N(a,d)+1` is below the full rank `2^a`, `easy_highRank_forces_merging` certifies that
`lowDegProj a d` is *not injective* on the equality matrix's rows — it genuinely collapses easy high-rank. -/
theorem lowDegProj_merges_equality (d : ℕ) (h : Fintype.card (LowWt a d) + 1 < 2 ^ a) :
    ¬ Set.InjOn (lowDegProj a d) ↑(rowsOf (eqMatrix (Fin a → Bool))) :=
  easy_highRank_forces_merging (lowDegProj a d) (Fintype.card (LowWt a d) + 1)
    (lowDegProj_eqMatrix_le d) h

/-- **A3-survival reduces to a concrete low-degree lower bound (proved, via the lever).**  If the hard family
`Mhard` has a subset `T` of its rows on which the low-degree projection is injective — i.e. `|T|` rows with
*distinct* low-degree signatures — then the hard family's projected rank survives: `pcrank ≥ |T|`.  Establishing
such a `T` of super-polynomial size for an actual NP family (Tseitin/Majority/Goldreich) is the open obligation. -/
theorem lowDegProj_hard_survives (d : ℕ) (Mhard : (Fin a → Bool) → (Fin a → Bool) → Bool)
    (T : Finset ((Fin a → Bool) → Bool)) (hT : T ⊆ rowsOf Mhard)
    (hinj : Set.InjOn (lowDegProj a d) ↑T) :
    T.card ≤ pcrank (lowDegProj a d) Mhard :=
  pcrank_ge_of_injOn (lowDegProj a d) Mhard T hT hinj

end PallLean.Paper93.DeepMath.PathB.LowDegreeProjection

#print axioms PallLean.Paper93.DeepMath.PathB.LowDegreeProjection.lowDegProj_feature_bound
#print axioms PallLean.Paper93.DeepMath.PathB.LowDegreeProjection.lowDegProj_eqMatrix_le
#print axioms PallLean.Paper93.DeepMath.PathB.LowDegreeProjection.lowDegProj_merges_equality
#print axioms PallLean.Paper93.DeepMath.PathB.LowDegreeProjection.lowDegProj_hard_survives
