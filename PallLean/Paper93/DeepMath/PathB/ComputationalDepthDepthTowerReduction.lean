import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKRW9

/-!
# The depth-tower reduction: super-additive depth composition ⟹ `P ⊄ NC¹`

The depth analogue of `SuperAdditiveComposition`, wired to the KRW arc.  The two-unit test showed
the crucial quantitative fact: **additive**-per-level depth composition (`dmdepth` grows by a fixed
constant each step) gives `dmdepth(F k) = Θ(k) = Θ(log₂ arity)` — *exactly* the NC¹ boundary
(`DepthLogBounded`), not past it.  To beat NC¹ the per-step depth increment must itself **grow** with
the level, i.e. each composition folds in a gadget whose own depth scales.  That is the single open
lemma — KRW composition with a scaling base.

A `DepthTower` bundles it:

* `fam k` — a family on `2^k` bits (KRW indexing, arity `2^k`, `log₂ arity = k`);
* **`depth_grow : ∀ k, dmdepth (fam k) + k ≤ dmdepth (fam (k+1))`** — the super-additive step: level
  `k+1` exceeds level `k` by at least `k`.  *This is the entire open content* — depth-additive
  composition with a base whose depth grows (`≥ k`) per level.  Strictly stronger than
  `¬ DepthLogBounded` (a growing-increment shape, not just super-linearity), so it is not the
  conclusion in disguise; and it is **not constructed** here.

From `depth_grow` alone, `dmdepth (fam k) ≥ 0+1+⋯+(k-1) = k(k-1)/2` — quadratic in `k`, hence
super-linear, hence `¬ DepthLogBounded fam`.  Feeding that into the existing
`krw_separation_socket` (together with the uniformity conjuncts `InP L ∧ Realizes L fam`) yields
`∃ L ∈ InP, ¬ NC1Depth L`, i.e. `P ⊄ NC¹`.

**Honest scope.**  `depth_grow` is the KRW conjecture in its hard regime (a scaling-depth base); the
`InP`/`Realizes` conjuncts are the uniformity gap — the *same* open requirement as
`krw_separation_socket`.  Nothing is constructed; the tower and the uniformity are explicit
hypotheses (no `sorry`).  The ceiling is **`P ≠ NC¹`, not `P ≠ NP`** — the depth route's honest
limit.  This is the composition-based companion to the counting-based `hardFamily_not_DepthLogBounded`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DepthTowerReduction

open PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-- A hypothetical **super-additive depth-composition tower** on a `2^k`-bit family: each composition
step raises `dmdepth` by at least the current level `k` (a *growing* increment — composition with a
scaling-depth base).  `depth_grow` is the single open lemma; the tower is never constructed. -/
structure DepthTower where
  /-- The family: `fam k` is a Boolean function on `2^k` inputs. -/
  fam : (k : ℕ) → (Fin (2 ^ k) → Bool) → Bool
  /-- **Super-additivity (the open lemma):** level `k+1` has depth `≥ dmdepth(fam k) + k`. -/
  depth_grow : ∀ k, dmdepth (fam k) + k ≤ dmdepth (fam (k + 1))

/-- **Depth accumulates to the triangular number (proved).**  Iterating the growing increment gives
`dmdepth (fam k) ≥ 0 + 1 + ⋯ + (k-1)`. -/
theorem depthTower_dmdepth_ge (T : DepthTower) (k : ℕ) :
    (∑ i ∈ Finset.range k, i) ≤ dmdepth (T.fam k) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact le_trans (Nat.add_le_add_right ih n) (T.depth_grow n)

/-- **The tower is depth-hard (proved).**  Quadratic depth beats every `O(log arity) = O(k)` bound,
so the family violates the NC¹-depth condition. -/
theorem depthTower_not_DepthLogBounded (T : DepthTower) : ¬ DepthLogBounded T.fam := by
  rintro ⟨c, hc⟩
  have h1 := depthTower_dmdepth_ge T (2 * c + 3)
  have h2 := hc (2 * c + 3)
  have hk1 : 2 * c + 3 - 1 = 2 * c + 2 := by omega
  have h3 : (∑ i ∈ Finset.range (2 * c + 3), i) * 2 = (2 * c + 3) * (2 * c + 2) := by
    rw [Finset.sum_range_id_mul_two, hk1]
  nlinarith [h1, h2, h3]

/-- **THE DEPTH REDUCTION, wired to KRW (proved, conditional).**  A super-additive depth tower whose
family is realised by an `InP` language gives `P ⊄ NC¹` via `krw_separation_socket`.  The `InP` and
`Realizes` conjuncts are the uniformity gap (the standard open KRW requirement); `depth_grow` is the
scaling-base composition lemma.  Nothing here is `P ≠ NP` — the ceiling is `P ≠ NC¹`. -/
theorem depthTower_krw_separation (T : DepthTower)
    (L : List Bool → Bool) (hInP : ComposableMachine.InP L) (hR : Realizes L T.fam) :
    ∃ L, ComposableMachine.InP L ∧ ¬ NC1Depth L :=
  krw_separation_socket ⟨T.fam, L, hInP, hR, depthTower_not_DepthLogBounded T⟩

end PallLean.Paper93.DeepMath.PathB.DepthTowerReduction

#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerReduction.depthTower_dmdepth_ge
#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerReduction.depthTower_not_DepthLogBounded
#print axioms PallLean.Paper93.DeepMath.PathB.DepthTowerReduction.depthTower_krw_separation
