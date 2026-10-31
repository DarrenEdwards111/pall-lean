import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRankContextualWidth

/-!
# Projected contextual rank — turning the Book-1 A1 bridge into a concrete target certificate

Raw `crank` (`…RankContextualWidth`) did its job: it proved the multiplicative horn (A3 reachable) and exposed why
A1 fails — easy functions (equality, inner-product) already have *full* raw rank.  The Book-1 route's actual claim
is not about raw rank but about a **projected** rank: a contextual/SPDP projection `Π` that is supposed to collapse
the rank of *time-structured* (poly-time) computations while leaving the hard family's rank high.  This file makes
that object concrete and proves the laws that pin down exactly what a successful projection must do.

A **projection** is any map `proj : (B → Bool) → R` applied to each row of the cut matrix; the **projected
contextual rank** is the number of distinct projected rows:

`pcrank proj M = |{ proj (row a) : a }|`.

Because post-composing a function can only merge rows, `pcrank ≤ crank` always, with equality iff `proj` is
injective on the rows.  So a projection separates *only* by **merging some rows and not others**.

## Sanity laws (all proved, clean axioms)

* `pcrank_le_crank` — projecting never increases rank.
* `pcrank_id_eq_crank` — the identity projection recovers raw rank.
* `pcrank_le_card_range` — `pcrank ≤ |R|` (a projection into a small codomain bounds rank).
* `pcrank_eq_crank_of_injOn` / `pcrank_eq_crank_of_injective` — **rank survives an injective projection**
  (`projection_preserves_rank_if_injective`).
* `pcrank_ge_of_injOn` — **A3-survival certificate**: if `proj` is injective on an `s`-element subset of the hard
  family's rows, then `pcrank ≥ s` (the hard rank survives).

## A1 as a certificate, not a mystery

* `BoundedRangeProjection proj k := |R| ≤ k`, and `boundedRange_pcrank_le` proves it forces `pcrank ≤ k` for
  **every** `M`.  This is the cheap way to get A1 — and `boundedRange_cannot_be_separating` proves it is **fatal**:
  a bounded-range projection bounds the *hard* family too, so it can never satisfy A3.  (Calibration: the constant
  projection `constProj` collapses the full-rank equality matrix to `pcrank ≤ 1` — but it is bounded-range, hence
  indiscriminate: it collapses everything, easy and hard alike.)

## The isolated A1 certificate (the live target)

* `SeparatingProjection proj Mhard p s := pcrank proj (equality) ≤ p ∧ s ≤ pcrank proj Mhard` — A1 on an explicit
  easy high-rank calibrator *and* A3-survival on the hard family.
* `separatingProjection_forces_selective` — **a separating projection must be `selective`**: with `p < s` it
  provably *merges* rows of the easy equality matrix (`¬ InjOn` there) while keeping `≥ s` hard rows distinct.  So
  the projection must distinguish hardness from easiness **at the level of the row vectors themselves**.
* `boundedRange_cannot_be_separating` — the cheap A1 (bounded range) is provably not separating.

**Honest status.**  The framework is fully proved; what is *not* proved (and is exactly `P ≠ NP`-strength) is the
**existence** of a separating projection for an actual NP family — equivalently a projection that is injective on
the hard family's rows yet collapses every poly-time computation's rows to a polynomial count.  This file does not
assert that exists; it reduces the Book-1 A1 bridge to that single concrete object and proves the structural
constraints any solution must meet (selective merging) and that the obvious cheap attempt (bounded range) cannot
work.  That is the live-invariant path made precise, not closed.
-/

namespace PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth

/-- The finite set of **rows** of the cut matrix `M : A → B → Bool` (one per past-context). -/
def rowsOf {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (M : A → B → Bool) : Finset (B → Bool) :=
  Finset.univ.image (fun a => (fun b => M a b))

/-- `crank` is exactly the number of rows. -/
theorem crank_eq_card_rowsOf {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (M : A → B → Bool) :
    crank M = (rowsOf M).card := rfl

/-- The **projected contextual rank**: the number of distinct *projected* rows under `proj : (B → Bool) → R`. -/
def pcrank {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [DecidableEq R]
    (proj : (B → Bool) → R) (M : A → B → Bool) : ℕ :=
  ((rowsOf M).image proj).card

/-- **`pcrank ≤ crank` (proved).**  Post-composing a projection can only merge rows, never split them. -/
theorem pcrank_le_crank {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [DecidableEq R]
    (proj : (B → Bool) → R) (M : A → B → Bool) :
    pcrank proj M ≤ crank M := by
  rw [crank_eq_card_rowsOf]
  exact Finset.card_image_le

/-- **`pcrank id = crank` (proved).**  The identity projection recovers the raw rank. -/
theorem pcrank_id_eq_crank {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (M : A → B → Bool) :
    pcrank (id : (B → Bool) → (B → Bool)) M = crank M := by
  rw [crank_eq_card_rowsOf]
  unfold pcrank
  rw [Finset.image_id]

/-- **`pcrank ≤ |R|` (proved).**  A projection into a small codomain bounds the rank. -/
theorem pcrank_le_card_range {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [DecidableEq R]
    [Fintype R] (proj : (B → Bool) → R) (M : A → B → Bool) :
    pcrank proj M ≤ Fintype.card R := by
  unfold pcrank
  exact le_trans (Finset.card_le_card (Finset.subset_univ _)) (le_of_eq Finset.card_univ)

/-- **Refinement monotonicity (proved).**  If `proj1` factors through `proj2` (`proj1 = g ∘ proj2`), then `proj2`
is at least as distinguishing: `pcrank proj1 M ≤ pcrank proj2 M`.  A strictly richer projection can only *raise*
rank — the lever for comparing projection families (e.g. SPDP refines low-degree). -/
theorem pcrank_le_of_factor {A B R₁ R₂ : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    [DecidableEq R₁] [DecidableEq R₂] (proj1 : (B → Bool) → R₁) (proj2 : (B → Bool) → R₂)
    (g : R₂ → R₁) (M : A → B → Bool) (hfac : ∀ r, proj1 r = g (proj2 r)) :
    pcrank proj1 M ≤ pcrank proj2 M := by
  unfold pcrank
  have heq : (rowsOf M).image proj1 = ((rowsOf M).image proj2).image g := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro r _
    exact hfac r
  rw [heq]
  exact Finset.card_image_le

/-- **Rank survives an injective projection (proved).**  If `proj` is injective on the rows of `M`, the projected
rank equals the raw rank.  This is `projection_preserves_rank_if_injective` at the row level. -/
theorem pcrank_eq_crank_of_injOn {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [DecidableEq R]
    (proj : (B → Bool) → R) (M : A → B → Bool) (hinj : Set.InjOn proj ↑(rowsOf M)) :
    pcrank proj M = crank M := by
  rw [crank_eq_card_rowsOf]
  unfold pcrank
  exact Finset.card_image_of_injOn hinj

/-- Globally injective projections preserve rank. -/
theorem pcrank_eq_crank_of_injective {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [DecidableEq R]
    (proj : (B → Bool) → R) (M : A → B → Bool) (hinj : Function.Injective proj) :
    pcrank proj M = crank M :=
  pcrank_eq_crank_of_injOn proj M (hinj.injOn)

/-- **A3-survival certificate (proved).**  If `proj` is injective on a subset `T` of the rows of `M`, then
`pcrank proj M ≥ |T|`.  Used to certify that a hard family's high rank *survives* a projection: exhibit a large
subset of its rows on which the projection stays injective. -/
theorem pcrank_ge_of_injOn {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [DecidableEq R]
    (proj : (B → Bool) → R) (M : A → B → Bool) (T : Finset (B → Bool)) (hT : T ⊆ rowsOf M)
    (hinj : Set.InjOn proj ↑T) :
    T.card ≤ pcrank proj M := by
  unfold pcrank
  calc T.card = (T.image proj).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((rowsOf M).image proj).card := Finset.card_le_card (Finset.image_subset_image hT)

/-! ### A1 as a certificate -/

/-- **The A1 certificate, cheap form:** the projection has a small codomain. -/
def BoundedRangeProjection {B R : Type*} [Fintype R] (_proj : (B → Bool) → R) (k : ℕ) : Prop :=
  Fintype.card R ≤ k

/-- **A bounded-range projection bounds `pcrank` for every `M` (proved).**  This is the cheap A1: any function's
projected rank is `≤ k`. -/
theorem boundedRange_pcrank_le {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq B] [DecidableEq R]
    [Fintype R] (proj : (B → Bool) → R) (M : A → B → Bool) (k : ℕ)
    (h : BoundedRangeProjection proj k) :
    pcrank proj M ≤ k :=
  le_trans (pcrank_le_card_range proj M) h

/-- The constant projection (codomain `Unit`). -/
def constProj (B : Type*) : (B → Bool) → Unit := fun _ => ()

/-- **Calibration: the constant projection collapses even full raw rank (proved).**  `pcrank (constProj) M ≤ 1`
for every `M` — including the full-rank equality matrix.  But `constProj` is bounded-range (`|Unit| = 1`), hence
*indiscriminate*: it collapses easy and hard alike, so by `boundedRange_cannot_be_separating` it is useless as a
separator. -/
theorem pcrank_constProj_le_one {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (M : A → B → Bool) :
    pcrank (constProj B) M ≤ 1 := by
  have h := pcrank_le_card_range (constProj B) M
  simpa using h

/-! ### Calibration on easy high-rank functions and the isolated target -/

/-- Helper: on `a`-bit cut blocks the rank is at most `2^a`. -/
theorem crank_cube_le {a : ℕ} (M : (Fin a → Bool) → (Fin a → Bool) → Bool) :
    crank M ≤ 2 ^ a := by
  have h := crank_le_card_past M
  rwa [show Fintype.card (Fin a → Bool) = 2 ^ a by
    simp [Fintype.card_bool, Fintype.card_fin]] at h

/-- **A1 on an easy high-rank function forces merging (proved).**  If a projection bounds the equality matrix's
projected rank below its full raw rank `2^a`, then it is **not injective** on the equality matrix's rows — it must
merge some of them.  Since the equality matrix is easy (linear-time), any A1-satisfying projection must do this. -/
theorem easy_highRank_forces_merging {a : ℕ} {R : Type*} [DecidableEq R]
    (proj : ((Fin a → Bool) → Bool) → R) (p : ℕ)
    (hp : pcrank proj (eqMatrix (Fin a → Bool)) ≤ p) (hlt : p < 2 ^ a) :
    ¬ Set.InjOn proj ↑(rowsOf (eqMatrix (Fin a → Bool))) := by
  intro hinj
  have heq : pcrank proj (eqMatrix (Fin a → Bool)) = crank (eqMatrix (Fin a → Bool)) :=
    pcrank_eq_crank_of_injOn proj _ hinj
  rw [heq, crank_cube_full] at hp
  omega

/-- **The isolated A1 certificate.**  A projection is *separating* for a hard family `Mhard` (with witness sizes
`p < s`) if it bounds the easy calibrator's projected rank by `p` (A1) while keeping the hard family's projected
rank `≥ s` (A3-survival). -/
def SeparatingProjection {a : ℕ} {R : Type*} [DecidableEq R]
    (proj : ((Fin a → Bool) → Bool) → R) (Mhard : (Fin a → Bool) → (Fin a → Bool) → Bool) (p s : ℕ) : Prop :=
  pcrank proj (eqMatrix (Fin a → Bool)) ≤ p ∧ s ≤ pcrank proj Mhard

/-- **A separating projection must be selective (proved).**  With `p < s ≤ 2^a`, a separating projection provably
*merges* rows of the easy equality matrix (it is not injective there) while keeping `≥ s` distinct projected rows
of the hard family.  So a successful Book-1 projection must distinguish hardness from easiness purely from the row
vectors — collapsing easy high-rank rows but not hard ones.  Constructing such a projection for an actual NP family
is exactly the open `P ≠ NP`-strength step. -/
theorem separatingProjection_forces_selective {a : ℕ} {R : Type*} [DecidableEq R]
    (proj : ((Fin a → Bool) → Bool) → R) (Mhard : (Fin a → Bool) → (Fin a → Bool) → Bool) (p s : ℕ)
    (hps : p < s) (hs : s ≤ 2 ^ a) (H : SeparatingProjection proj Mhard p s) :
    (¬ Set.InjOn proj ↑(rowsOf (eqMatrix (Fin a → Bool)))) ∧ s ≤ pcrank proj Mhard := by
  refine ⟨?_, H.2⟩
  exact easy_highRank_forces_merging proj p H.1 (lt_of_lt_of_le hps hs)

/-- **The cheap A1 cannot separate (proved).**  A bounded-range projection (codomain `≤ p`) bounds the hard
family's projected rank by `p` too, so it cannot meet the A3-survival threshold `s > p`.  Any separating projection
must therefore have *unbounded range* yet still collapse all poly-time computations — which is the genuine,
unsolved A1. -/
theorem boundedRange_cannot_be_separating {a : ℕ} {R : Type*} [DecidableEq R] [Fintype R]
    (proj : ((Fin a → Bool) → Bool) → R) (Mhard : (Fin a → Bool) → (Fin a → Bool) → Bool) (p s : ℕ)
    (hps : p < s) (hbr : BoundedRangeProjection proj p) :
    ¬ SeparatingProjection proj Mhard p s := by
  rintro ⟨_, hs⟩
  have hle : pcrank proj Mhard ≤ p := boundedRange_pcrank_le proj Mhard p hbr
  omega

end PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank

#print axioms PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank.pcrank_le_crank
#print axioms PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank.pcrank_id_eq_crank
#print axioms PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank.pcrank_eq_crank_of_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank.pcrank_ge_of_injOn
#print axioms PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank.easy_highRank_forces_merging
#print axioms PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank.separatingProjection_forces_selective
#print axioms PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank.boundedRange_cannot_be_separating
