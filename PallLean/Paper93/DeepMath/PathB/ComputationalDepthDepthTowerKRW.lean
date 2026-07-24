import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW4

/-!
# Wiring the depth tower to KRW: `KRWConjectureDepth` + scaling base ⟹ `depth_grow`

`DepthTowerReduction` isolated the open lemma `depth_grow`
(`dmdepth(fam k) + k ≤ dmdepth(fam (k+1))`).  Here it is *derived* from the two standard KRW
sockets, so the holographic depth-projection is assembled down to exactly them — nothing hidden.

The block composition `comp` has **multiplicative** arity (`m·b`), and `KRWConjectureDepth` is
depth-additive on nonconstant functions: `dmdepth f + dmdepth g ≤ dmdepth (comp f g)`.  A *fixed*
base iterated (`iterComp`, already in the repo) gives depth `(d+1)·D` at arity `b^{d+1}` — a
*constant* depth/log-arity ratio, i.e. the NC¹ boundary, not past it (`krw_iter_lb`).  To grow the
ratio the base must **scale**: at step `k` fold in a gadget `g k` of depth `≥ k`.

* **`ScalingBase`** — bundles the scaling base: arity `ar k`, function `g k`, nonconstancy, and the
  **scaling-depth socket `g_deep : ∀ k, k ≤ dmdepth (g k)`** (an *explicit* such family is the
  uniformity gap — not supplied here);
* **`scaleTower S`** — the composed family `fam 0 = g 0`, `fam (k+1) = comp (fam k) (g k)`;
* **`scaleTower_nc`** — every level is nonconstant (needed for `KRWConjectureDepth`);
* **`scaleTower_depth_grow` (proved from `KRWConjectureDepth`)** — `dmdepth(fam k) + k ≤
  dmdepth(fam (k+1))`: exactly `DepthTower.depth_grow`.  KRW gives `+ dmdepth(g k)`, `g_deep`
  turns that into `+ k`;
* **`scaleTower_dmdepth_ge` (proved)** — the growing increments accumulate to the triangular
  number, so `dmdepth(fam k) ≥ k(k-1)/2` — super-linear in the composition index.

**Honest scope.**  Two named sockets remain, both explicit hypotheses (no `sorry`): the conjecture
`H : KRWConjectureDepth`, and the scaling base `ScalingBase` with `g_deep` (an explicit in-`P`
depth-`≥k` gadget = the uniformity gap).  The composed family lives on `∏ ar j` bits (multiplicative
arity), not `2^k`, so converting index-super-linearity to the log-arity NC¹ statement needs the
scaling base's arity to be polynomially controlled — the residual bookkeeping.  The ceiling is
`P ≠ NC¹`, not `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DepthTowerKRW

open PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- A **scaling-depth base**: at each level `k`, a nonconstant function on `ar k` bits whose depth is
at least `k`.  `g_deep` is the uniformity socket — an *explicit* (in-`P`) such family is exactly the
open KRW requirement; it is not constructed here. -/
structure ScalingBase where
  /-- Arity of the level-`k` base gadget. -/
  ar : ℕ → ℕ
  /-- Every base arity is positive. -/
  ar_pos : ∀ k, 0 < ar k
  /-- The level-`k` base gadget. -/
  g : ∀ k, (Fin (ar k) → Bool) → Bool
  /-- Each base is nonconstant (required by `KRWConjectureDepth`). -/
  g_nc : ∀ k, ∃ u u', g k u ≠ g k u'
  /-- **Scaling depth (the open socket):** the level-`k` base has DeMorgan depth `≥ k`. -/
  g_deep : ∀ k, k ≤ dmdepth (g k)

/-- The composed family: `fam 0 = g 0`, `fam (k+1) = comp (fam k) (g k)` (arity `∏_{j≤k} ar j`). -/
def scaleTower (S : ScalingBase) : ℕ → Σ N : ℕ, (Fin N → Bool) → Bool
  | 0 => ⟨S.ar 0, S.g 0⟩
  | (k + 1) => ⟨(scaleTower S k).1 * S.ar k, comp (S.ar_pos k) (scaleTower S k).2 (S.g k)⟩

/-- **Every level of the tower is nonconstant (proved).** -/
theorem scaleTower_nc (S : ScalingBase) (k : ℕ) :
    ∃ y y', (scaleTower S k).2 y ≠ (scaleTower S k).2 y' := by
  induction k with
  | zero => exact S.g_nc 0
  | succ k ih =>
    simp only [scaleTower]
    exact comp_nonconstant (S.ar_pos k) (scaleTower S k).2 (S.g k) ih (S.g_nc k)

/-- **`depth_grow`, derived from `KRWConjectureDepth` + the scaling base (proved).**  Composition is
depth-additive (KRW), and the level-`k` base contributes `≥ k` (`g_deep`), so
`dmdepth(fam k) + k ≤ dmdepth(fam (k+1))` — exactly `DepthTower.depth_grow`. -/
theorem scaleTower_depth_grow (H : KRWConjectureDepth) (S : ScalingBase) (k : ℕ) :
    dmdepth (scaleTower S k).2 + k ≤ dmdepth (scaleTower S (k + 1)).2 := by
  have hlb := H (scaleTower S k).1 (S.ar k) (S.ar_pos k) (scaleTower S k).2 (S.g k)
    (scaleTower_nc S k) (S.g_nc k)
  have hgd := S.g_deep k
  simp only [scaleTower]
  omega

/-- **The tower is depth-hard (proved).**  The growing increments accumulate to the triangular
number: `0 + 1 + ⋯ + (k-1) ≤ dmdepth(fam k)`, i.e. depth is super-linear in the composition index. -/
theorem scaleTower_dmdepth_ge (H : KRWConjectureDepth) (S : ScalingBase) (k : ℕ) :
    (∑ i ∈ Finset.range k, i) ≤ dmdepth (scaleTower S k).2 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact le_trans (Nat.add_le_add_right ih n) (scaleTower_depth_grow H S n)

end PallLean.Paper93.DeepMath.PathB.DepthTowerKRW

#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerKRW.scaleTower_depth_grow
#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerKRW.scaleTower_dmdepth_ge
