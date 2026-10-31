import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSPDPFeatureProjection

/-!
# The decisive test: high-degree affine-indicator residual — SPDP collapses too

The inner-product probe (`…SPDPHardSurvivalProbe`) showed SPDP preserves the *linear* parity core, but that core
is degree 1 (survives even low-degree).  The decisive case is the **high-degree** residual: rows that are
indicators of affine subspaces / parity-constraint cosets, which *low-degree collapses* (they vanish on all
low-weight inputs).  Does SPDP survive there?

This file answers it.  The key structural fact:

> **SPDP at constant order `(k, d)` is a *local* probe — it only ever evaluates a row on the weight-`≤ (k+d)` ball.**

So any row that vanishes on that ball has the all-zero SPDP feature.  High-degree affine indicators whose support
avoids low weight therefore collapse — exactly like under low-degree.

## What is proved (clean axioms, no `sorry`)

* `spdpProj_zero_of_vanishing` — a row vanishing on the weight-`(k+d)` ball has the zero SPDP feature (the locality
  of SPDP, made precise).  `lowDegProj_zero_of_vanishing` is the order-`0` analogue.
* `spdp_pcrank_le_ballMeeting` — **general collapse bound**: `pcrank (spdpProj a k d) M ≤ (# rows that are nonzero
  somewhere on the (k+d)-ball) + 1`.  Rows avoiding the ball all merge into the single zero feature.
* The concrete high-degree family `constraintMatrix P` (rows = indicators of the affine subcube
  `{v : v|_P = s}`, a product of `|P|` coordinate constraints — degree `|P|`):
  * `crank_constraintMatrix` — full raw rank `2^{|P|}` (superpolynomial when `|P|` is large).
  * `constraint_weight_le` — a row's syndrome weight lower-bounds the Hamming weight of any input it accepts.
  * `spdp_constraintMatrix_collapse` — **`pcrank (spdpProj a k d) (constraintMatrix P) ≤ N(|P|, k+d) + 1`** (only
    syndromes reachable by `≤ (k+d)`-weight inputs survive) — *polynomial* for constant `k, d`.
  * `lowDeg_constraintMatrix_collapse` — the same `≤ N(|P|, d) + 1` for low-degree.

## Verdict: the projection path takes the hit

`crank = 2^{|P|}` (superpolynomial) while `pcrank (spdpProj a k d) ≤ N(|P|, k+d) + 1` (polynomial for constant
`k, d`): **SPDP collapses the high-degree affine-indicator residual to polynomial rank — exactly as low-degree
does.**  The earlier domination `spdp_refines_lowDeg` is real but does not help here: both projections are local
low-weight probes, and a high-codimension affine indicator is invisible to *any* bounded-order local probe.

This is the negative outcome flagged as decisive.  A *constant-order* SPDP feature map cannot be the A1 projection:
it collapses the very (high-degree, Tseitin-style) residuals whose rank A3 needs to preserve.  Survival would
require the order `(k, d)` to **grow with the codimension** — i.e. `k + d = Ω(distance)` — which pushes the feature
space to `2^{super-poly}` and breaks the A1 (poly feature count) side.  The locality/feature-count tension is the
quantitative shadow of the SPDP-rank barrier: bounded-order SPDP is too local to separate, and unbounded-order
SPDP is too large to bound `P`.  The projected-rank path, with a *fixed* feature order, is ruled out here.
-/

namespace PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.LowDegreeProjection
open PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection

variable {a : ℕ}

/-- **SPDP is local (proved): a row vanishing on the weight-`(k+d)` ball has the zero SPDP feature.**  Every
order-`≤k` derivative on a `≤ d`-weight input only ever evaluates the row on inputs of weight `≤ k+d`. -/
theorem spdpProj_zero_of_vanishing (k d : ℕ) (r : (Fin a → Bool) → Bool)
    (hr : ∀ z, hw z ≤ k + d → r z = false) :
    spdpProj a k d r = (fun _ => false) := by
  funext p
  obtain ⟨⟨S, hS⟩, ⟨y, hy⟩⟩ := p
  simp only [spdpProj]
  apply derivSet_eq_false_of_all_false
  intro T hT
  apply hr
  calc hw (flipSet y T) ≤ hw y + T.card := hw_flipSet_le y T
    _ ≤ d + S.card := Nat.add_le_add hy (Finset.card_le_card (Finset.mem_powerset.mp hT))
    _ ≤ d + k := Nat.add_le_add_left hS d
    _ = k + d := Nat.add_comm d k

/-- **Low-degree is local (proved): a row vanishing on the weight-`d` ball has the zero low-degree feature.** -/
theorem lowDegProj_zero_of_vanishing (d : ℕ) (r : (Fin a → Bool) → Bool)
    (hr : ∀ z, hw z ≤ d → r z = false) :
    lowDegProj a d r = (fun _ => false) := by
  funext y
  obtain ⟨z, hz⟩ := y
  simp only [lowDegProj]
  exact hr z hz

/-- **General SPDP collapse bound (proved): `pcrank ≤ (#rows meeting the (k+d)-ball) + 1`.**  Every row that is
zero on the whole ball collapses to the single zero feature. -/
theorem spdp_pcrank_le_ballMeeting {A : Type*} [Fintype A] (k d : ℕ) (M : A → (Fin a → Bool) → Bool) :
    pcrank (spdpProj a k d) M
      ≤ (Finset.univ.filter (fun x => ∃ z, hw z ≤ k + d ∧ M x z = true)).card + 1 := by
  classical
  rw [pcrank_eq_image]
  have hsub : Finset.univ.image (fun x => spdpProj a k d (fun b => M x b))
      ⊆ insert (fun _ => false)
          ((Finset.univ.filter (fun x => ∃ z, hw z ≤ k + d ∧ M x z = true)).image
            (fun x => spdpProj a k d (fun b => M x b))) := by
    intro w hw'
    rw [Finset.mem_image] at hw'
    obtain ⟨x, _, rfl⟩ := hw'
    by_cases hx : ∃ z, hw z ≤ k + d ∧ M x z = true
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩)
    · rw [Finset.mem_insert]
      left
      apply spdpProj_zero_of_vanishing
      intro z hz
      cases hb : M x z
      · rfl
      · exact absurd ⟨z, hz, hb⟩ hx
  calc (Finset.univ.image (fun x => spdpProj a k d (fun b => M x b))).card
      ≤ (insert (fun _ => false)
          ((Finset.univ.filter (fun x => ∃ z, hw z ≤ k + d ∧ M x z = true)).image
            (fun x => spdpProj a k d (fun b => M x b)))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.univ.filter (fun x => ∃ z, hw z ≤ k + d ∧ M x z = true)).image
            (fun x => spdpProj a k d (fun b => M x b))).card + 1 := Finset.card_insert_le _ _
    _ ≤ (Finset.univ.filter (fun x => ∃ z, hw z ≤ k + d ∧ M x z = true)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1

/-! ### A concrete high-degree affine-indicator family -/

variable (P : Fin a → Prop) [DecidablePred P]

/-- The **affine subcube indicator** matrix: row `s` accepts `v` iff `v` matches the syndrome `s` on every
constrained coordinate (`P i`).  Each row is a product of `|P|` coordinate constraints — degree `|P|`. -/
def constraintMatrix (s : {i : Fin a // P i} → Bool) (v : Fin a → Bool) : Bool :=
  decide (∀ i : {i : Fin a // P i}, v i.val = s i)

/-- The canonical accepted input for syndrome `s`: the constrained coordinates carry `s`, the rest are `0`. -/
def embed (s : {i : Fin a // P i} → Bool) : Fin a → Bool :=
  fun i => if h : P i then s ⟨i, h⟩ else false

/-- The syndrome weight: number of constrained coordinates set to `true`. -/
def swt (s : {i : Fin a // P i} → Bool) : ℕ :=
  (Finset.univ.filter (fun i => s i = true)).card

theorem embed_eval (s : {i : Fin a // P i} → Bool) (j : {i : Fin a // P i}) :
    embed P s j.val = s j := by
  simp only [embed, j.property, dif_pos]

/-- **Syndrome weight lower-bounds accepted-input weight (proved): `swt s ≤ hw v` whenever `v` is accepted.**  Each
constrained coordinate set in `s` forces a distinct `1` in `v`. -/
theorem constraint_weight_le (s : {i : Fin a // P i} → Bool) (v : Fin a → Bool)
    (h : constraintMatrix P s v = true) :
    swt P s ≤ hw v := by
  have hall : ∀ i : {i : Fin a // P i}, v i.val = s i := of_decide_eq_true h
  unfold swt hw
  have hmap : (Finset.univ.filter (fun j : {i : Fin a // P i} => s j = true)).image (fun j => j.val)
      ⊆ Finset.univ.filter (fun i => v i = true) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hall j]
    exact hj.2
  calc (Finset.univ.filter (fun j : {i : Fin a // P i} => s j = true)).card
      = ((Finset.univ.filter (fun j : {i : Fin a // P i} => s j = true)).image (fun j => j.val)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (Finset.univ.filter (fun i => v i = true)).card := Finset.card_le_card hmap

/-- The rows of `constraintMatrix` are distinct: distinct syndromes give distinct affine subcubes. -/
theorem constraintMatrix_row_injective :
    Function.Injective (fun s : {i : Fin a // P i} → Bool => (fun v => constraintMatrix P s v)) := by
  intro s s' h
  have hself : constraintMatrix P s (embed P s) = true := by
    simp only [constraintMatrix]
    rw [decide_eq_true_eq]
    intro j
    exact embed_eval P s j
  have hcross := congrFun h (embed P s)
  dsimp only at hcross
  rw [hself] at hcross
  have hall : ∀ j : {i : Fin a // P i}, embed P s j.val = s' j := of_decide_eq_true hcross.symm
  funext j
  rw [← embed_eval P s j]
  exact hall j

/-- **Full raw rank (proved): `crank (constraintMatrix P) = 2^{|P|}`** (superpolynomial when `|P|` is large). -/
theorem crank_constraintMatrix :
    crank (constraintMatrix P) = 2 ^ Fintype.card {i : Fin a // P i} := by
  have hrfl : crank (constraintMatrix P)
      = (Finset.univ.image (fun s : {i : Fin a // P i} → Bool => (fun v => constraintMatrix P s v))).card := rfl
  rw [hrfl, Finset.card_image_of_injective _ (constraintMatrix_row_injective P), Finset.card_univ]
  simp [Fintype.card_bool]

/-- **SPDP collapses the high-degree affine family (proved): `pcrank ≤ N(|P|, k+d) + 1`** — only syndromes
reachable by a `≤ (k+d)`-weight input survive, which is polynomial for constant `k, d`. -/
theorem spdp_constraintMatrix_collapse (k d : ℕ) :
    pcrank (spdpProj a k d) (constraintMatrix P)
      ≤ (Finset.univ.filter (fun s : {i : Fin a // P i} → Bool => swt P s ≤ k + d)).card + 1 := by
  refine le_trans (spdp_pcrank_le_ballMeeting k d (constraintMatrix P)) ?_
  apply Nat.add_le_add_right
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter] at hs ⊢
  obtain ⟨z, hz, hMz⟩ := hs.2
  exact ⟨Finset.mem_univ s, le_trans (constraint_weight_le P s z hMz) hz⟩

/-- **Low-degree collapses it too (proved): `pcrank ≤ N(|P|, d) + 1`.** -/
theorem lowDeg_constraintMatrix_collapse (d : ℕ) :
    pcrank (lowDegProj a d) (constraintMatrix P)
      ≤ (Finset.univ.filter (fun s : {i : Fin a // P i} → Bool => swt P s ≤ d)).card + 1 := by
  classical
  rw [pcrank_eq_image]
  have hsub : Finset.univ.image (fun s => lowDegProj a d (fun v => constraintMatrix P s v))
      ⊆ insert (fun _ => false)
          ((Finset.univ.filter (fun s : {i : Fin a // P i} → Bool => swt P s ≤ d)).image
            (fun s => lowDegProj a d (fun v => constraintMatrix P s v))) := by
    intro w hw'
    rw [Finset.mem_image] at hw'
    obtain ⟨s, _, rfl⟩ := hw'
    by_cases hx : swt P s ≤ d
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hx⟩, rfl⟩)
    · rw [Finset.mem_insert]
      left
      apply lowDegProj_zero_of_vanishing
      intro z hz
      cases hb : constraintMatrix P s z
      · rfl
      · exact absurd (le_trans (constraint_weight_le P s z hb) hz) hx
  calc (Finset.univ.image (fun s => lowDegProj a d (fun v => constraintMatrix P s v))).card
      ≤ (insert (fun _ => false)
          ((Finset.univ.filter (fun s : {i : Fin a // P i} → Bool => swt P s ≤ d)).image
            (fun s => lowDegProj a d (fun v => constraintMatrix P s v)))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.univ.filter (fun s : {i : Fin a // P i} → Bool => swt P s ≤ d)).image
            (fun s => lowDegProj a d (fun v => constraintMatrix P s v))).card + 1 := Finset.card_insert_le _ _
    _ ≤ (Finset.univ.filter (fun s : {i : Fin a // P i} → Bool => swt P s ≤ d)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1

end PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse.spdpProj_zero_of_vanishing
#print axioms PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse.spdp_pcrank_le_ballMeeting
#print axioms PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse.crank_constraintMatrix
#print axioms PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse.spdp_constraintMatrix_collapse
#print axioms PallLean.Paper93.DeepMath.PathB.AffineIndicatorCollapse.lowDeg_constraintMatrix_collapse
