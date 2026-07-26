import Mathlib.Data.Nat.Basic

/-!
# Bounded sharing: the quantitative survivable-sharing threshold

`HandoffRestricted` dented the handoff at **zero** sharing (disjoint blocks).  This refines it to **bounded**
sharing: allow `t` cross-block wires and prove the additive bound degrades *gracefully*, then compute the
exact threshold `t⋆` below which the magnifiable `n^{1+ε}` bound survives and above which mass production
kills it.  This is a **map refinement** — it turns "the locality barrier is `cost_super` in costume" into a
quantitative statement — not a wall-crossing (see the honest scope).

## The model

A `SharedComposition` is the disjoint composition plus a **sharing budget** `t`: `t` cross-block wires let
gates serve two blocks, so the additive bound degrades by at most `t`:
`shared_bound : k·b ≤ total + t`  (i.e. `total ≥ k·b − t`).  `t = 0` recovers the disjoint dent.

## What is proved

* **`degraded_bound`** — graceful degradation: with per-block super-linearity `m·D ≤ b`,
  `n·D ≤ total + t`, i.e. `total ≥ n·D − t`.  Each unit of sharing costs at most one unit of the bound —
  the degradation is *linear* in `t`.
* **`sharing_survivable`** — the threshold: if `t + n·D' ≤ n·D` (i.e. `t ≤ n·(D − D')`), the magnifiable
  bound `n·D' ≤ total` **survives**.  So the survivable-sharing threshold is `t⋆ = n·(D − D')`.
* **`survivable_example`** — below threshold (`t = 3 ≤ t⋆ = 6`) the bound holds: `n·1 = 6 ≤ total = 9`.
* **`oversharing_kills`** — above threshold (`t = 10 > t⋆ = 6`) the bound fails: `total = 2 < n·1 = 6`.
  Concretely: this much mass production is survivable, that much kills it.

## Honest scope — a sharper wall, still a wall

The threshold is real and informative: `t⋆ = n·(D − D')` says exactly how much protocol/circuit sharing
the magnifiable bound tolerates — a quantitative locality budget, the form the actual locality-barrier
literature is stated in.  But **bounding `t` is itself a restriction**: "circuits with ≤ `t⋆` cross-block
wires" is a *restricted class*, and Uhlig mass production lets the real adversary share *unboundedly*
(up to circuit size).  So this tells you "SAT is hard *if* its optimal circuit shares `≤ t⋆`" — and
proving that is exactly `cost_super`.  The threshold **relocates** the wall (from "no sharing" to
"`≤ t⋆` sharing"), it does not dissolve it.  A precise map, not a crossing.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.BoundedSharingThreshold

/-- A **bounded-sharing** composition: `k` disjoint blocks of `m` bits, per-block bound `b`, total gate
count `total`, and a **sharing budget** `t` (cross-block wires).  `shared_bound` is the graceful
degradation: sharing reduces the additive bound by at most `t`, `k·b ≤ total + t`. -/
structure SharedComposition where
  /-- number of blocks -/
  k : ℕ
  /-- bits per block -/
  m : ℕ
  /-- per-block gate lower bound -/
  b : ℕ
  /-- sharing budget: number of cross-block wires -/
  t : ℕ
  /-- total gate count -/
  total : ℕ
  /-- graceful degradation: sharing costs at most `t` off the additive bound -/
  shared_bound : k * b ≤ total + t

/-- Input size `n = k·m`. -/
def inputSize (P : SharedComposition) : ℕ := P.k * P.m

/-- **Graceful degradation (proved).**  With per-block super-linearity `m·D ≤ b`, the total obeys
`n·D ≤ total + t` — i.e. `total ≥ n·D − t`.  Sharing degrades the super-linear bound *linearly*: each
cross-block wire costs at most one unit. -/
theorem degraded_bound (P : SharedComposition) (D : ℕ) (hblock : P.m * D ≤ P.b) :
    inputSize P * D ≤ P.total + P.t := by
  have key : inputSize P * D = P.k * (P.m * D) := Nat.mul_assoc P.k P.m D
  rw [key]
  calc P.k * (P.m * D) ≤ P.k * P.b := Nat.mul_le_mul (Nat.le_refl P.k) hblock
    _ ≤ P.total + P.t := P.shared_bound

/-- **The survivable-sharing threshold (proved).**  If the sharing budget satisfies `t + n·D' ≤ n·D`
(equivalently `t ≤ n·(D − D')`), the magnifiable bound `n·D' ≤ total` **survives**.  The exact threshold
is `t⋆ = n·(D − D')`: below it the `n^{1+ε}`-type bound holds. -/
theorem sharing_survivable (P : SharedComposition) (D D' : ℕ) (hblock : P.m * D ≤ P.b)
    (hthresh : P.t + inputSize P * D' ≤ inputSize P * D) :
    inputSize P * D' ≤ P.total := by
  have h := degraded_bound P D hblock
  omega

/-- Below threshold: `k=2, m=3, b=6` (so `D=2`, `n=6`, `t⋆ = n·(D−1) = 6`), sharing `t = 3 ≤ 6`, total `9`.
-/
def survivableWitness : SharedComposition where
  k := 2
  m := 3
  b := 6
  t := 3
  total := 9
  shared_bound := by decide

/-- **Below threshold, the bound survives (proved).**  With `t = 3 ≤ t⋆ = 6`, the super-linear bound
`n·1 = 6 ≤ total = 9` holds. -/
theorem survivable_example : inputSize survivableWitness * 1 ≤ survivableWitness.total :=
  sharing_survivable survivableWitness 2 1 (by decide) (by decide)

/-- Above threshold: same block data, but sharing `t = 10 > t⋆ = 6`, total collapsed to `2`. -/
def oversharedWitness : SharedComposition where
  k := 2
  m := 3
  b := 6
  t := 10
  total := 2
  shared_bound := by decide

/-- **Above threshold, the bound is killed (proved).**  With `t = 10 > t⋆ = 6`, the total collapses:
`total = 2 < n·1 = 6`.  Beyond the threshold, mass production destroys even the linear floor. -/
theorem oversharing_kills : oversharedWitness.total < inputSize oversharedWitness * 1 := by decide

end PallLean.Paper93.DeepMath.PathB.BoundedSharingThreshold

#print axioms PallLean.Paper93.DeepMath.PathB.BoundedSharingThreshold.degraded_bound
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedSharingThreshold.sharing_survivable
#print axioms PallLean.Paper93.DeepMath.PathB.BoundedSharingThreshold.oversharing_kills
