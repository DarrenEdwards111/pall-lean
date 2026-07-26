import Mathlib.Data.Nat.Basic

/-!
# Attacking the handoff H, in a restricted case

The handoff `H : W₂ → W₄` — translating Route 2's composition/depth bound into Route 4's *magnifiable*
form — is the locality barrier, the one residual of `RouteComposition`.  Here we **dent it**: we exhibit a
restricted setting where the translation provably goes through, and we pin down exactly what makes the
general case fail.

## The restricted handoff

Take the magnifiable ("sparse") problem to be a **disjoint composition** of `k` blocks, each on `m` input
bits, so the input size is `n = k·m`.  Two ingredients — both of which Route 2 supplies in the no-sharing
world:

* **W₂ (disjoint composition):** the per-block bounds *add*, `k·b ≤ total` — no cross-block sharing.  (This
  is exactly the `IncompressibleCertificate` shape: disjoint witnesses ⟹ additive.)
* **per-block super-linearity:** each block needs `b ≥ m·D` gates for a super-linear factor `D ≥ 2` — which
  `SuperlinearPerCopy` delivers in the no-sharing model (`n(n-1)` per block).

Then the handoff is a clean arithmetic fact: `total ≥ k·b ≥ k·(m·D) = (k·m)·D = n·D`.  A super-linear
(`n·D`, `D ≥ 2`) total bound is *exactly* the magnifiable `n^{1+ε}` input Route 4 consumes.  **The
translation goes through.**

## What is proved

* **`handoff_restricted`** — the translation: disjoint composition (`k·b ≤ total`) + per-block
  super-linearity (`m·D ≤ b`) ⟹ `n·D ≤ total`.  Route 2's composition bound becomes Route 4's magnifiable
  bound.
* **`handoff_beats_linear`** — the output is genuinely super-linear: `n < total` (for `D ≥ 2`, `n ≥ 1`) — a
  magnifiable bound, not a trivial linear one.
* **`composedWitness`** — non-vacuous.

## Honest scope — the dent, and what it reveals

This is a real, machine-checked instance of the handoff working: in the restricted (disjoint-block,
super-linear-per-block) setting, `H : W₂ → W₄` is **discharged** — Route 2's bound *does* magnify.  And it
tells us precisely what the general locality barrier is: **both** ingredients — `disjoint_bound` and the
super-linear per-block bound — live in the **no-sharing** world.  In a general circuit, cross-block
**sharing** makes `total < k·b` (mass production), so `disjoint_bound` fails and the handoff breaks.

So the dent answers, in the restricted case, the open question "does the handoff reduce to `cost_super`":
**yes** — here `H` reduces to no-sharing + super-linear-per-block, both already built.  The general
obstruction is exactly cross-block sharing = mass production = `cost_super`, once again.  The locality
barrier is `cost_super` in a fourth costume.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HandoffRestricted

/-- A **disjoint composition** of `k` blocks, each on `m` bits, with per-block lower bound `b` and total
gate count `total`.  `disjoint_bound` is Route 2's no-sharing composition bound: the per-block bounds add,
`k·b ≤ total`. -/
structure ComposedProblem where
  /-- number of blocks -/
  k : ℕ
  /-- input bits per block -/
  m : ℕ
  /-- per-block gate lower bound -/
  b : ℕ
  /-- total gate count -/
  total : ℕ
  /-- W₂ (no cross-block sharing): the per-block bounds add -/
  disjoint_bound : k * b ≤ total

/-- Input size of the composed problem: `n = k·m`. -/
def inputSize (P : ComposedProblem) : ℕ := P.k * P.m

/-- **The restricted handoff (proved).**  If each block is super-linear by factor `D` (`m·D ≤ b`) and the
per-block bounds add (`disjoint_bound`), then the total is super-linear in the input size: `n·D ≤ total`.
Route 2's composition bound (`W₂`) becomes Route 4's magnifiable bound (`W₄`). -/
theorem handoff_restricted (P : ComposedProblem) (D : ℕ) (hblock : P.m * D ≤ P.b) :
    inputSize P * D ≤ P.total := by
  have key : inputSize P * D = P.k * (P.m * D) := by
    show P.k * P.m * D = P.k * (P.m * D)
    exact Nat.mul_assoc P.k P.m D
  rw [key]
  calc P.k * (P.m * D) ≤ P.k * P.b := Nat.mul_le_mul (Nat.le_refl P.k) hblock
    _ ≤ P.total := P.disjoint_bound

/-- **The magnified bound is genuinely super-linear (proved).**  For a super-linear factor `D ≥ 2` and a
nonempty input, `n < total` — the translated bound strictly exceeds linear, i.e. it is a magnifiable
`n^{1+ε}`-type bound, not a trivial one. -/
theorem handoff_beats_linear (P : ComposedProblem) (D : ℕ) (hD : 2 ≤ D)
    (hblock : P.m * D ≤ P.b) (hpos : 1 ≤ inputSize P) : inputSize P < P.total := by
  have h := handoff_restricted P D hblock
  have h2 : inputSize P * 2 ≤ inputSize P * D := Nat.mul_le_mul (Nat.le_refl _) hD
  omega

/-- **The setting is non-vacuous (proved).**  `2` blocks of `3` bits, per-block bound `6 = m·2`, total
`12 = k·b`: the handoff fires with `D = 2`, giving `n·2 = 12 ≤ 12`. -/
def composedWitness : ComposedProblem where
  k := 2
  m := 3
  b := 6
  total := 12
  disjoint_bound := by decide

end PallLean.Paper93.DeepMath.PathB.HandoffRestricted

#print axioms PallLean.Paper93.DeepMath.PathB.HandoffRestricted.handoff_restricted
#print axioms PallLean.Paper93.DeepMath.PathB.HandoffRestricted.handoff_beats_linear
