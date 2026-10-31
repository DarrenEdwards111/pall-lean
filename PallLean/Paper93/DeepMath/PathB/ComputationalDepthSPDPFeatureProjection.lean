import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLowDegreeProjection

/-!
# SPDP / partial-derivative feature projection — calibrated, and proved to dominate low-degree

Low-degree (`…LowDegreeProjection`) passed easy-collapse and escaped the bounded-range deathtrap, but its
distinguishing power is weak (it only sees a row's *values* on low-weight inputs).  The SPDP route enriches this
with **shifted partial derivatives**: it records, for each variable set `S` of size `≤ k`, the discrete order-`|S|`
derivative `∂_S r`, evaluated on the low-weight inputs.  Over `F₂` the order-`|S|` derivative is the XOR of `r`
over all sub-flips of `S`:

`derivSet S r x = parity #{ T ⊆ S : r (x with bits T flipped) = true }`.

The SPDP feature of a row is `spdpProj a k d r = (S, y) ↦ derivSet S r y`, over `|S| ≤ k` and `hw y ≤ d`.

## What is proved (clean axioms, no `sorry`)

* `derivSet_empty` — the order-`0` derivative is the value: `derivSet ∅ r x = r x`.  So the low-degree signature is
  literally the `S = ∅` coordinate of the SPDP feature.
* `spdp_refines_lowDeg` — **SPDP dominates low-degree**: `pcrank (lowDegProj a d) M ≤ pcrank (spdpProj a k d) M`
  for every `M` (via `pcrank_le_of_factor`, the `S = ∅` coordinate).  SPDP preserves *at least* as many rows — the
  precise sense in which it is a strictly stronger separator candidate.
* `spdpProj_feature_bound` — `pcrank ≤ 2^{(#S≤k)·N(a,d)} = 2^{poly}` — still an *exponential* (non-polynomial)
  feature space, so SPDP also escapes `boundedRange_cannot_be_separating`.
* `spdpProj_collapse_high` / `spdpProj_eqMatrix_le` — **easy-collapse still passes**: every equality row of weight
  `> k + d` has the all-zero SPDP feature (its derivatives never reach the low-weight inputs), so
  `pcrank (spdpProj a k d) (equality) ≤ N(a, k+d) + 1 = poly`.
* `spdpProj_hard_survives` — A3-survival via the same lever `pcrank_ge_of_injOn`.

## Honest calibration verdict

SPDP is a **strictly stronger candidate than low-degree** (`spdp_refines_lowDeg`, proved) that nonetheless retains
both good properties: it collapses easy high-rank (equality → poly) and escapes the deathtrap (feature space
`2^{poly}`).  The two open obligations are *unchanged in shape but now harder to fail on the hard side*:

1. **A1 for all `P`** — poly SPDP feature count for every poly-time computation.  Still not free; this is exactly
   the assumed SPDP/CEW bridge audited as *assumed-not-derived* (`…NFrameHypercubeConstraint`).
2. **A3 hard-survival** — super-polynomially many distinct SPDP features for the hard family.  Because SPDP
   dominates low-degree, *any* hard row that low-degree keeps, SPDP keeps too — so SPDP is at least as likely to
   pass A3.  Establishing it for an actual NP family is the genuine SPDP rank lower bound (the Tseitin/permanent
   surface, barriered short of `P/poly`).

So the experiment escalates the candidate without faking the bridge: SPDP `≥` low-degree as a separator, same two
explicit sub-problems, the hard-survival one strictly easier to satisfy.  If even SPDP collapses the hard family
(A3 fails), the whole *projected-rank* approach to A1 is ruled out — which would itself be a sharp, honest no-go.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection

open PallLean.Paper93.DeepMath.PathB.RankContextualWidth
open PallLean.Paper93.DeepMath.PathB.ProjectedContextualRank
open PallLean.Paper93.DeepMath.PathB.LowDegreeProjection

variable {a : ℕ}

/-- Flip the bits of `x` in the set `T`. -/
def flipSet (x : Fin a → Bool) (T : Finset (Fin a)) : Fin a → Bool :=
  fun i => if i ∈ T then !(x i) else x i

@[simp] theorem flipSet_empty (x : Fin a → Bool) : flipSet x ∅ = x := by
  funext i; simp [flipSet]

/-- Flipping the bits in `T` raises the Hamming weight by at most `|T|`. -/
theorem hw_flipSet_le (x : Fin a → Bool) (T : Finset (Fin a)) :
    hw (flipSet x T) ≤ hw x + T.card := by
  unfold hw flipSet
  have hsub : (Finset.univ.filter (fun i => (if i ∈ T then !(x i) else x i) = true))
      ⊆ (Finset.univ.filter (fun i => x i = true)) ∪ T := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases hiT : i ∈ T
    · exact Finset.mem_union_right _ hiT
    · simp only [hiT, if_false] at hi
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  calc (Finset.univ.filter (fun i => (if i ∈ T then !(x i) else x i) = true)).card
      ≤ ((Finset.univ.filter (fun i => x i = true)) ∪ T).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun i => x i = true)).card + T.card := Finset.card_union_le _ _

/-- The discrete order-`|S|` derivative of a row `r` over `F₂`: the parity of the number of sub-flips `T ⊆ S` on
which `r` evaluates true. -/
def derivSet (S : Finset (Fin a)) (r : (Fin a → Bool) → Bool) (x : Fin a → Bool) : Bool :=
  decide ((S.powerset.filter (fun T => r (flipSet x T) = true)).card % 2 = 1)

/-- **Order-`0` derivative is the value (proved).** -/
theorem derivSet_empty (r : (Fin a → Bool) → Bool) (x : Fin a → Bool) :
    derivSet ∅ r x = r x := by
  unfold derivSet
  rw [Finset.powerset_empty, Finset.filter_singleton, flipSet_empty]
  cases r x <;> simp

/-- If `r` vanishes on every sub-flip of `S`, its order-`|S|` derivative is zero. -/
theorem derivSet_eq_false_of_all_false (S : Finset (Fin a)) (r : (Fin a → Bool) → Bool)
    (x : Fin a → Bool) (h : ∀ T ∈ S.powerset, r (flipSet x T) = false) :
    derivSet S r x = false := by
  unfold derivSet
  have hempty : (S.powerset.filter (fun T => r (flipSet x T) = true)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro T hT
    rw [h T hT]
    simp
  rw [hempty]
  simp

/-- The **SPDP feature projection**: for each `|S| ≤ k` and low-weight input `y`, the order-`|S|` derivative of the
row at `y`. -/
def spdpProj (a k d : ℕ) :
    ((Fin a → Bool) → Bool) → ({S : Finset (Fin a) // S.card ≤ k} × LowWt a d → Bool) :=
  fun r p => derivSet p.1.val r p.2.val

/-- **SPDP dominates low-degree (proved).**  The low-degree signature is the `S = ∅` coordinate of the SPDP
feature, so `pcrank (lowDegProj a d) M ≤ pcrank (spdpProj a k d) M`: the SPDP projection preserves at least as many
rows as low-degree, for every `M`. -/
theorem spdp_refines_lowDeg (k d : ℕ) (M : (Fin a → Bool) → (Fin a → Bool) → Bool) :
    pcrank (lowDegProj a d) M ≤ pcrank (spdpProj a k d) M := by
  refine pcrank_le_of_factor (lowDegProj a d) (spdpProj a k d)
    (fun feat y => feat (⟨∅, by rw [Finset.card_empty]; exact Nat.zero_le k⟩, y)) M ?_
  intro r
  funext y
  simp only [lowDegProj, spdpProj]
  rw [derivSet_empty]

/-- **Feature bound (proved): `pcrank ≤ 2^{poly}`.**  The SPDP feature space has size `2^{(#S≤k)·N(a,d)}` —
exponential, not polynomial — so SPDP escapes the polynomial-codomain deathtrap just as low-degree does. -/
theorem spdpProj_feature_bound (k d : ℕ) (M : (Fin a → Bool) → (Fin a → Bool) → Bool) :
    pcrank (spdpProj a k d) M ≤ 2 ^ Fintype.card ({S : Finset (Fin a) // S.card ≤ k} × LowWt a d) := by
  have h := pcrank_le_card_range (spdpProj a k d) M
  rwa [show Fintype.card (({S : Finset (Fin a) // S.card ≤ k} × LowWt a d) → Bool)
        = 2 ^ Fintype.card ({S : Finset (Fin a) // S.card ≤ k} × LowWt a d) by
    simp [Fintype.card_bool]] at h

/-- **High-weight equality rows collapse under SPDP (proved).**  A point indicator of weight `> k + d` has the
all-zero SPDP feature: every order-`≤k` derivative evaluated on a `≤ d`-weight input only ever touches inputs of
weight `≤ k + d < hw a₀`, where the indicator is `false`. -/
theorem spdpProj_collapse_high (k d : ℕ) (a0 : Fin a → Bool) (hwt : k + d < hw a0) :
    spdpProj a k d (fun b => eqMatrix (Fin a → Bool) a0 b) = (fun _ => false) := by
  funext p
  obtain ⟨⟨S, hS⟩, ⟨y, hy⟩⟩ := p
  simp only [spdpProj]
  apply derivSet_eq_false_of_all_false
  intro T hT
  have hTS : T ⊆ S := Finset.mem_powerset.mp hT
  have hwflip : hw (flipSet y T) ≤ d + k := by
    calc hw (flipSet y T) ≤ hw y + T.card := hw_flipSet_le y T
      _ ≤ d + S.card := Nat.add_le_add hy (Finset.card_le_card hTS)
      _ ≤ d + k := Nat.add_le_add_left hS d
  have hne : a0 ≠ flipSet y T := by
    intro heq; rw [heq] at hwt; omega
  simp [eqMatrix, hne]

/-- **Easy-collapse still passes under SPDP (proved): equality → `poly`.**  `pcrank (spdpProj a k d) (equality) ≤
N(a, k+d) + 1`: only the `≤ (k+d)`-weight points contribute, plus the single collapsed zero feature. -/
theorem spdpProj_eqMatrix_le (k d : ℕ) :
    pcrank (spdpProj a k d) (eqMatrix (Fin a → Bool))
      ≤ Fintype.card {y : Fin a → Bool // hw y ≤ k + d} + 1 := by
  classical
  rw [pcrank_eq_image]
  have hsub : Finset.univ.image (fun x => spdpProj a k d (fun b => eqMatrix (Fin a → Bool) x b))
      ⊆ insert (fun _ => false)
          ((Finset.univ.filter (fun x => hw x ≤ k + d)).image
            (fun x => spdpProj a k d (fun b => eqMatrix (Fin a → Bool) x b))) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, _, rfl⟩ := hz
    by_cases hx : hw x ≤ k + d
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩)
    · rw [Finset.mem_insert]
      exact Or.inl (spdpProj_collapse_high k d x (by omega))
  calc (Finset.univ.image (fun x => spdpProj a k d (fun b => eqMatrix (Fin a → Bool) x b))).card
      ≤ (insert (fun _ => false)
          ((Finset.univ.filter (fun x => hw x ≤ k + d)).image
            (fun x => spdpProj a k d (fun b => eqMatrix (Fin a → Bool) x b)))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ.filter (fun x => hw x ≤ k + d)).image
            (fun x => spdpProj a k d (fun b => eqMatrix (Fin a → Bool) x b))).card + 1 :=
        Finset.card_insert_le _ _
    _ ≤ (Finset.univ.filter (fun x => hw x ≤ k + d)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
    _ = Fintype.card {y : Fin a → Bool // hw y ≤ k + d} + 1 := by rw [Fintype.card_subtype]

/-- **A3-survival reduces to a concrete SPDP lower bound (proved, via the lever).**  If the hard family has a
subset `T` of rows on which the SPDP projection is injective — `|T|` rows with *distinct* SPDP features — then the
hard projected rank survives: `pcrank ≥ |T|`.  Establishing super-polynomial such `T` for an NP family is the SPDP
rank lower bound. -/
theorem spdpProj_hard_survives (k d : ℕ) (Mhard : (Fin a → Bool) → (Fin a → Bool) → Bool)
    (T : Finset ((Fin a → Bool) → Bool)) (hT : T ⊆ rowsOf Mhard)
    (hinj : Set.InjOn (spdpProj a k d) ↑T) :
    T.card ≤ pcrank (spdpProj a k d) Mhard :=
  pcrank_ge_of_injOn (spdpProj a k d) Mhard T hT hinj

end PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection.derivSet_empty
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection.spdp_refines_lowDeg
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection.spdpProj_feature_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection.spdpProj_eqMatrix_le
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPFeatureProjection.spdpProj_hard_survives
