import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicCurvature

/-!
# What proving "SAT is AdS" would require

`curvature_is_cost_super` showed "SAT is AdS" **is** `cost_super`.  So this file does not cross the wall
— nothing can, in-model.  What it does is use the geometry to say *precisely what a proof would have to
supply*, splitting the demand into three requirements, two of which are already met, isolating the third
as the whole content.

## The three requirements

* **R1 — Globalization (already met, free).**  In Riemannian geometry a *pointwise* curvature bound
  globalizes to a volume bound by the comparison theorem (Rauch/Bishop–Gromov): curvature `≤ -κ`
  everywhere ⟹ balls grow at least like the constant-`-κ` model.  Here that is
  `globalization_is_free`: a local per-step doubling `∀ d, 2·vol d ≤ vol(d+1)` already gives the global
  exponential `2^d·vol 0 ≤ vol d`.  You never have to control the whole tower at once.

* **R2 — Locality / uniformity (met as a reduction).**  By `curvature_is_cost_super`, "AdS" is a
  `∀ d` conjunction of *identical* local certificates.  So a proof reduces to **one uniform local
  curvature bound** repeated at every scale — the per-step / one-round object.  This is real progress in
  *form* (the wall is local), but it only relocates the difficulty; it does not discharge it.

* **R3 — Adversary-proofness (THE WALL).**  The catch: `cbudget` is a **minimum over realizations** —
  the adversary picks the cheapest circuit.  The local certificate must therefore hold not for *some*
  hyperbolic realization but for the **min-cost** one.  And the adversary's only move — *sharing* — is
  exactly a shortcut that lowers cost, i.e. acts in the **flattening** direction (positive curvature that
  bends the tree toward Euclidean).  Worse, a shared sub-circuit is **non-local**: it couples distant
  steps, so a purely local certificate is not automatically preserved under the min.

## What is proved here

* **`globalization_is_free`** — R1: local doubling ⟹ global exponential (the comparison theorem).
* **`shortcut_is_anti_curvature`** — sharing is exactly anti-curvature: for `lo ≤ hi` with
  `lo < 2·base ≤ hi`, the *same* step passes the doubling test at the honest cost `hi` but **fails** it
  at the shared (lower) cost `lo`.  The adversary's only lever points straight at the sag.
* **`treeR_is_ads` / `sharing_only_lowers` / `adversary_flattens`** — the crux, concretely: the honest
  tree realization `treeR` **is** AdS (hyperbolic at 2), yet `cbudget = minCost` (the min over
  realizations) is **not** — a single cheaper shortcut realization `dagR` undercuts it and the min sags
  at a step (`2·minCost 2 = 8 > 7 = minCost 3`).  **Exhibiting a hyperbolic realization is not enough.**

## The bottom line — the exact shape of the missing proof

Proving "SAT is AdS" requires showing the **min over every realization** stays hyperbolic — i.e. that
**no shortcut the adversary can add flattens any step below doubling**.  R1 is free, R2 makes it local,
but R3 is a min over an exponential adversary class whose only move is anti-curvature and non-local.
That min-stays-hyperbolic statement is `cost_super` — proving `cbudget(SAT)` large, i.e. that no small
(flat) circuit computes SAT.  The geometry does not remove this; it says exactly what it is: **rule out
every flattening shortcut, uniformly.**  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AdSRequirement

open PallLean.Paper93.DeepMath.PathB.HolographicCurvature

/-- **R1: globalization is free (proved).**  The comparison theorem in discrete form: a *local* per-step
curvature bound (doubling at every scale) already forces the *global* exponential volume — you never
control the whole tower at once, only one step's curvature.  This is `hyperbolic_exponential`, restated
as the requirement it discharges. -/
theorem globalization_is_free (vol : ℕ → ℕ) (h : ∀ d, 2 * vol d ≤ vol (d + 1)) :
    ∀ d, 2 ^ d * vol 0 ≤ vol d :=
  hyperbolic_exponential vol 2 h

/-- **Sharing is exactly anti-curvature (proved).**  At a single step with base volume `base`, the honest
cost `hi` and a shared (cheaper) cost `lo ≤ hi`: if `lo < 2·base ≤ hi`, then the step **passes** the
doubling test at `hi` but **fails** it at `lo`.  The adversary's only lever — lowering cost by sharing —
points straight at the sag: it is positive curvature, flattening the tree. -/
theorem shortcut_is_anti_curvature (base lo hi : ℕ)
    (hle : lo ≤ hi) (hpass : 2 * base ≤ hi) (hsag : lo < 2 * base) :
    (2 * base ≤ hi) ∧ ¬ (2 * base ≤ lo) :=
  ⟨hpass, by omega⟩

/-- The honest tree realization: ball volume doubles every step (structural, no sharing). -/
def treeR : ℕ → ℕ
  | 0 => 1
  | (n + 1) => 2 * treeR n

/-- A flat (shared) realization: linear cost `d + 4`.  A shortcut DAG the adversary can build; its
curvature is zero, so it eventually **undercuts** the tree. -/
def dagR : ℕ → ℕ := fun d => d + 4

/-- What `cbudget` actually is: the **minimum** over realizations — the adversary picks the cheaper. -/
def minCost (d : ℕ) : ℕ := min (treeR d) (dagR d)

/-- **The honest tree realization IS AdS (proved).**  `treeR` is hyperbolic at rate `2` exactly:
`treeR (d+1) = 2 · treeR d`.  A single hyperbolic realization is easy to exhibit — that is *not* the
hard part. -/
theorem treeR_is_ads : Hyperbolic treeR 2 := by
  intro d
  show 2 * treeR d ≤ treeR (d + 1)
  exact Nat.le_refl _

/-- **Sharing only lowers cost (proved).**  The min-cost realization never exceeds the honest tree:
`minCost d ≤ treeR d`.  This is the discrete `dagCost ≤ treeCost` — sharing can only bend curvature down. -/
theorem sharing_only_lowers (d : ℕ) : minCost d ≤ treeR d := Nat.min_le_left _ _

/-- **The adversary min flattens (proved) — the crux.**  Even though `treeR` is AdS
(`treeR_is_ads`), the quantity that actually governs the lower bound, `minCost` (= `cbudget`, the min over
realizations), is **not** hyperbolic: the cheaper shortcut realization `dagR` undercuts the tree and the
min sags at a step — `2·minCost 2 = 8 > 7 = minCost 3`.  **Exhibiting one hyperbolic realization does not
make the min hyperbolic.** -/
theorem adversary_flattens : ¬ Hyperbolic minCost 2 := by
  intro h
  have h2 : 2 * minCost 2 ≤ minCost 3 := h 2
  have e2 : minCost 2 = 4 := by decide
  have e3 : minCost 3 = 7 := by decide
  rw [e2, e3] at h2
  omega

/-- **The exact shape of the missing proof (proved as a package).**  Two facts, side by side: the honest
realization `treeR` **is** AdS, yet the adversary min `minCost` is **not** — because sharing only lowers
cost (`sharing_only_lowers`) and one cheaper realization flattens the min (`adversary_flattens`).
Therefore proving "SAT is AdS" cannot be done by exhibiting a hyperbolic realization; it requires showing
the **min over every realization** stays hyperbolic — that *no* flattening shortcut exists.  That is
`cost_super`. -/
theorem ads_requires_ruling_out_all_shortcuts :
    Hyperbolic treeR 2 ∧ (∀ d, minCost d ≤ treeR d) ∧ ¬ Hyperbolic minCost 2 :=
  ⟨treeR_is_ads, sharing_only_lowers, adversary_flattens⟩

end PallLean.Paper93.DeepMath.PathB.AdSRequirement

#print axioms PallLean.Paper93.DeepMath.PathB.AdSRequirement.globalization_is_free
#print axioms PallLean.Paper93.DeepMath.PathB.AdSRequirement.shortcut_is_anti_curvature
#print axioms PallLean.Paper93.DeepMath.PathB.AdSRequirement.ads_requires_ruling_out_all_shortcuts
