import Mathlib.Data.Nat.Basic

/-!
# The gain-never-sags wall as a geometry problem: constant curvature / AdS

Darren's reframing: "the gain never sags" is a **geometry** problem — the doubling rate is a
*curvature*, constant the way a black hole's spacetime curvature is fixed by its mass, and framing it
holographically (AdS/CFT) makes steady doubling-without-sagging "clear."

This is exactly right as *language*, and it is worth making precise, because it explains both why the
**tree clears the wall** and why the **DAG is hard** — and it shows precisely where "clear" turns into
"assumed."

## The dictionary (all real)

* **volume of the observer's ball at scale `d`** = `vol d` = the cost / number of reachable states at
  depth `d`.  The bulk **radial direction** is the depth / RG scale; the **boundary** is the observer's
  cut (the determining modes).
* **curvature = gain.**  A space of *constant negative curvature* (AdS, hyperbolic) has geodesic balls
  whose volume grows by a **fixed multiplicative factor** every step.  That fixed factor *is* the
  amplifier gain `s`.  Constant curvature ⟺ constant gain ⟺ **scale invariance** (a CFT fixed point).
* **flat = sagging.**  Zero curvature (Euclidean `ℝ^k`, a grid) gives only **polynomial** ball growth
  `r^k` — the gain sags.  **Sharing / mass production adds shortcuts** that reconverge geodesics: it
  *flattens* the tree's curvature toward Euclidean, dropping exponential growth to polynomial.

## What is proved

* **`hyperbolic_exponential`** — constant negative curvature ⟹ exponential volume: `s^d · vol 0 ≤ vol d`.
  Hyperbolicity held at every scale forces the tower to ring to `2^d`.  (The AdS geodesic-ball law; the
  same telescope as the shrinkage engine, read as curvature.)
* **`flat_sags`** — a flat (linear) profile is *not* hyperbolic at rate `2`: zero curvature means the
  gain sags, growth is polynomial.
* **`tree_is_ads`** — the regular binary tree (the formula / bulk) is hyperbolic at rate `2` **exactly**
  (`2·2^d = 2^{d+1}`).  A tree is the discrete model of constant-negative-curvature space; its boundary
  is the CFT.  This is *why* the tree clears the wall — it is genuinely AdS, no sharing, curvature never
  flattens.
* **`curvature_is_cost_super`** — the punchline, a *definitional* identity: "the reachable set is AdS"
  (hyperbolic at `2`) unfolds to `∀ d, 2·vol d ≤ vol (d+1)`, which **is** `cost_super`.

## Honest scope — the geometry names the constant, it doesn't compute it

Framing the reachable set as AdS makes doubling-without-sagging "clear" **because AdS is *defined* to
have constant curvature** — the answer is built into the space.  The open problem is *not* "does doubling
hold in AdS" (it does, `hyperbolic_exponential`, trivially).  It is: **"is SAT's reachable-set geometry
actually AdS?"** — does its curvature stay bounded away from zero when the adversary is allowed to add
shortcuts (share / mass-produce)?  By `curvature_is_cost_super`, *that* question is `cost_super` in a
curvature costume.

So holography gives the right **frame** — the missing Lorentz, again (cf. the mirror duality) — and it
explains tree-vs-DAG geometrically.  But "SAT is AdS" is precisely the wall, not a way through it.
Assuming constant curvature is assuming `cost_super`, exactly as the gauge presupposed it
(`GaugeCircularity`).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HolographicCurvature

/-- **Constant negative curvature = constant gain.**  A volume profile `vol : ℕ → ℕ` (the observer's
ball volume / cost at scale `d`) is *hyperbolic with rate `s`* when each shell grows by at least the
factor `s`: `s · vol d ≤ vol (d+1)`.  This is the discrete constant-curvature (AdS radial expansion)
condition, and it is identical to the amplifier gain not sagging. -/
def Hyperbolic (vol : ℕ → ℕ) (s : ℕ) : Prop := ∀ d, s * vol d ≤ vol (d + 1)

/-- **Constant curvature ⟹ exponential volume (proved).**  A hyperbolic profile grows exponentially:
`s^d · vol 0 ≤ vol d`.  Negative curvature held at every scale forces the ball volume to grow by the
factor `s` forever — the tower rings to `s^d` (`2^d` for the tree).  This is the geodesic-ball growth
law of AdS / a regular tree; the same telescope as the shrinkage engine, read as curvature. -/
theorem hyperbolic_exponential (vol : ℕ → ℕ) (s : ℕ) (h : Hyperbolic vol s) :
    ∀ d, s ^ d * vol 0 ≤ vol d := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep : s * (s ^ d * vol 0) ≤ vol (d + 1) :=
      le_trans (Nat.mul_le_mul (Nat.le_refl s) ih) (h d)
    calc s ^ (d + 1) * vol 0
        = s * (s ^ d * vol 0) := by
          rw [Nat.pow_succ, Nat.mul_comm (s ^ d) s, Nat.mul_assoc]
      _ ≤ vol (d + 1) := hstep

/-- **Flat = sagging (proved).**  A flat profile — linear volume `vol d = d + 1`, the growth of a
Euclidean path, zero curvature — is *not* hyperbolic at rate `2`: at `d = 1`, `2 · vol 1 = 4 > 3 = vol 2`.
Zero curvature means the gain sags and the ball grows only polynomially.  Sharing / mass production
flattens the tree's curvature to this. -/
theorem flat_sags : ¬ Hyperbolic (fun d => d + 1) 2 := by
  intro h
  have h1 : 2 * (1 + 1) ≤ (1 + 1 + 1) := h 1
  omega

/-- **The tree is AdS (proved).**  The regular binary tree — the formula / bulk — has ball volume
`vol d = 2^d` and is hyperbolic at rate `2` exactly: `2 · 2^d = 2^{d+1}`.  A tree is the discrete model
of constant-negative-curvature space; its boundary (leaves / Cantor set) is the CFT.  This is *why* the
tree clears the wall — it is genuinely AdS, curvature never flattens because there is no sharing. -/
theorem tree_is_ads : Hyperbolic (fun d => 2 ^ d) 2 := by
  intro d
  show 2 * 2 ^ d ≤ 2 ^ (d + 1)
  rw [Nat.pow_succ]
  omega

/-- **The curvature IS `cost_super` (proved, definitional).**  "The reachable set is AdS" — constant
negative curvature at rate `2` — unfolds to `∀ d, 2 · vol d ≤ vol (d+1)`, which is *exactly* the doubling
wall `cost_super`.  Framing the geometry as AdS makes doubling "clear" only because AdS is *defined* to
have constant curvature: the answer is built into the space.  The open problem is not "is doubling clear
in AdS" (it is, trivially) but "is SAT's reachable-set geometry actually AdS" — does its curvature stay
negative under the adversary's shortcuts.  That is `cost_super`, in a curvature costume. -/
theorem curvature_is_cost_super (vol : ℕ → ℕ) :
    Hyperbolic vol 2 ↔ ∀ d, 2 * vol d ≤ vol (d + 1) := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.HolographicCurvature

#print axioms PallLean.Paper93.DeepMath.PathB.HolographicCurvature.hyperbolic_exponential
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicCurvature.tree_is_ads
#print axioms PallLean.Paper93.DeepMath.PathB.HolographicCurvature.curvature_is_cost_super
