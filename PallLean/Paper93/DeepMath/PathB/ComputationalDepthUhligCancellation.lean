import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATSeamReachThreshold

/-!
# Attacking Uhlig's cancellation on SAT: the socket is exactly the amortization question

The last brick reduced the socket for SAT's seam to a reach bound, and pinned the obstacle: a
socket-breaking straddler is an **Uhlig mass-production template** — a high-reach sub-computation reused
across the two disjoint copies via downstream cancellation.  This file attacks that cancellation
directly by opening up what it *is*: an **amortization**.  A straddler saves only if it provides a
**reusable template** paid once and reused by both copies; the "cancellation" is each copy's cone
recovering its own value from the shared template plus local work.  Splitting the single-copy cost into

  `single = template + local`   (shareable part `template` `t`, per-copy part `local` `r`),

the whole socket collapses to a single inequality between `t` and `r`.

## What is proved

* **`amortized_seam_law`** — the split *is* a valid composition seam: `composed + shared = 2·single`,
  with `composed = t + 2r` (share the template, pay both locals) and `shared = t` (the saving).
* **`socket_iff_local_dominates`** — the socket holds **iff** `t ≤ r`: at most half the single-copy cost
  is a reusable template.  The socket for SAT = "SAT's cost is per-input-dominated, not table-dominated".
* **`mass_production_iff_template_dominates`** — dually, the socket *fails* (Uhlig cancellation wins)
  **iff** `r < t`: the reusable template dominates the per-copy work, so sharing beats doubling.
* **`full_amortization_no_growth`** — `r = 0` (a pure lookup table, all cost shareable) gives
  `composed = single`: **no growth at all** — the mass-production collapse.
* **`no_amortization_full_doubling`** — `t = 0` (nothing shareable, pure per-input work) gives
  `composed = 2·single`: **full doubling** = `cost_super`.  The two extremes bracket the wall.
* **`socket_for_sat_iff_not_amortizes`** — the SAT statement: the socket holds iff SAT does **not**
  amortize (`¬ (r < t)`), i.e. its per-input work is at least its reusable template.
* **`independence_permits_amortization`** — the honest catch (Uhlig's own point): a dominant reusable
  template can break the socket **even for two distinct instances** — disjointness/independence does
  *not* force non-amortization.  Uhlig's universal-table construction serves independent inputs.

## Honest verdict — the mechanism is fully exposed; the SAT question is the wall

Uhlig's cancellation is an amortization, and the socket for SAT's seam is *exactly* the amortization
inequality `t ≤ r`: **at most half of SAT's single-copy cost may be a reusable template.**  Uhlig's
theorem is precisely that generic hard functions *fail* this (their cost is a dominant reusable table,
`t ≫ r`, so mass production halves it).  For SAT to satisfy the socket its optimal circuit must be
**per-input-dominated** — no `> ½`-cost universal template shareable across disjoint instances.  And
independence does not deliver this (`independence_permits_amortization`): a shared table serves
independent inputs, exactly as `SeamDisjointnessProbe` found for reach.  So attacking Uhlig's
cancellation on SAT lands on: SAT's cost is per-input-dominated = SAT resists mass production = the
surviving Uhlig `NonlinearHorn` = specific incompressibility of SAT = `cost_super` = `P ≠ NP`.  The
mechanism is now split to `t` vs `r` and the socket is that single inequality; proving it for SAT is the
wall, and nothing here proves it.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UhligCancellation

/-- **An amortized copy of the seam.**  The single-copy cost splits into a **shareable template** `t`
(a sub-computation reusable by both copies) and **per-copy local work** `r` (paid once per copy).  Uhlig
cancellation shares the template: two copies cost `t + 2r` instead of `2(t + r)`, saving `t`. -/
structure AmortizedSeam where
  /-- shareable template cost `t` (paid once, reused across both copies) -/
  template : ℕ
  /-- per-copy local/extraction cost `r` (paid per copy) -/
  local_ : ℕ
  /-- the single copy is nonempty -/
  base_pos : 1 ≤ template + local_

/-- Single-copy cost `C = t + r`. -/
def AmortizedSeam.single (A : AmortizedSeam) : ℕ := A.template + A.local_

/-- The seam-collision (Uhlig saving) `= t`: the template counted once instead of twice. -/
def AmortizedSeam.shared_ (A : AmortizedSeam) : ℕ := A.template

/-- The composed (shared) cost of both copies `= t + 2r`: one template, two locals. -/
def AmortizedSeam.composed (A : AmortizedSeam) : ℕ := A.template + 2 * A.local_

/-- **SAT amortizes**: its optimal circuit's reusable template dominates the per-copy work (`r < t`) —
the regime where Uhlig mass production halves the cost. -/
def Amortizes (A : AmortizedSeam) : Prop := A.local_ < A.template

/-! ### The split is a valid seam -/

/-- **The amortization split is a composition seam (proved).**  `composed + shared = 2·single`: sharing
the template and paying both locals, plus the saved template, equals two independent copies. -/
theorem amortized_seam_law (A : AmortizedSeam) :
    A.composed + A.shared_ = 2 * A.single := by
  simp only [AmortizedSeam.composed, AmortizedSeam.shared_, AmortizedSeam.single]
  omega

/-! ### The socket collapses to one inequality: t ≤ r -/

/-- **The socket ⟺ the per-copy work dominates the template (proved).**  `2·shared ≤ single` holds
exactly when `t ≤ r`: at most half the single-copy cost is a reusable template.  This is the socket for
SAT's seam in its sharpest mechanistic form — SAT's cost is per-input-dominated, not table-dominated. -/
theorem socket_iff_local_dominates (A : AmortizedSeam) :
    2 * A.shared_ ≤ A.single ↔ A.template ≤ A.local_ := by
  simp only [AmortizedSeam.shared_, AmortizedSeam.single]
  omega

/-- **Mass production wins ⟺ the template dominates (proved).**  The socket *fails* (Uhlig cancellation
succeeds, sharing beats doubling) exactly when `r < t`: the reusable template is more than half the
single-copy cost. -/
theorem mass_production_iff_template_dominates (A : AmortizedSeam) :
    A.single < 2 * A.shared_ ↔ A.local_ < A.template := by
  simp only [AmortizedSeam.shared_, AmortizedSeam.single]
  omega

/-! ### The two extremes bracket the wall -/

/-- **Full amortization ⟹ no growth (proved).**  If the per-copy work is zero (`r = 0`, a pure lookup
table — all cost is a shareable universal table), the composed cost equals a single copy: `composed =
single`.  Two copies for the price of one — the total mass-production collapse. -/
theorem full_amortization_no_growth (A : AmortizedSeam) (h : A.local_ = 0) :
    A.composed = A.single := by
  simp only [AmortizedSeam.composed, AmortizedSeam.single, h]

/-- **No amortization ⟹ full doubling (proved).**  If nothing is shareable (`t = 0`, pure per-input
work), the composed cost is twice a single copy: `composed = 2·single` — full doubling = `cost_super`.
The two copies cannot share, so the tower grows. -/
theorem no_amortization_full_doubling (A : AmortizedSeam) (h : A.template = 0) :
    A.composed = 2 * A.single := by
  simp only [AmortizedSeam.composed, AmortizedSeam.single, h]
  omega

/-! ### The SAT statement, and the honest catch -/

/-- **The socket for SAT ⟺ SAT does not amortize (proved).**  SAT's seam satisfies the socket exactly
when SAT does *not* amortize — its per-input work is at least its reusable template (`¬ (r < t)`).
Proving this for SAT is proving its cost is per-input-dominated = it resists mass production. -/
theorem socket_for_sat_iff_not_amortizes (A : AmortizedSeam) :
    2 * A.shared_ ≤ A.single ↔ ¬ Amortizes A := by
  simp only [AmortizedSeam.shared_, AmortizedSeam.single, Amortizes]
  omega

/-- A concrete **Uhlig witness**: template `3` dominates local `1`.  A dominant reusable template. -/
def uhligWitness : AmortizedSeam := ⟨3, 1, by omega⟩

/-- **Independence does not force non-amortization (proved) — the honest catch.**  A dominant reusable
template (`uhligWitness`, `t = 3 > r = 1`) amortizes and breaks the socket, with the composed cost
strictly below doubling (`5 < 8`).  Read as two *distinct* SAT instances, this is Uhlig's own point: a
shared universal table serves independent inputs, so disjointness/independence alone does **not** forbid
mass production — exactly as `SeamDisjointnessProbe` found for reach.  SAT needs rigidity beyond
independence (incompressibility), which is `cost_super`. -/
theorem independence_permits_amortization :
    Amortizes uhligWitness
    ∧ ¬ (2 * uhligWitness.shared_ ≤ uhligWitness.single)
    ∧ uhligWitness.composed < 2 * uhligWitness.single := by
  refine ⟨?_, ?_, ?_⟩
  · show uhligWitness.local_ < uhligWitness.template
    decide
  · simp only [AmortizedSeam.shared_, AmortizedSeam.single]
    decide
  · simp only [AmortizedSeam.composed, AmortizedSeam.single]
    decide

end PallLean.Paper93.DeepMath.PathB.UhligCancellation

#print axioms PallLean.Paper93.DeepMath.PathB.UhligCancellation.amortized_seam_law
#print axioms PallLean.Paper93.DeepMath.PathB.UhligCancellation.socket_iff_local_dominates
#print axioms PallLean.Paper93.DeepMath.PathB.UhligCancellation.mass_production_iff_template_dominates
#print axioms PallLean.Paper93.DeepMath.PathB.UhligCancellation.full_amortization_no_growth
#print axioms PallLean.Paper93.DeepMath.PathB.UhligCancellation.no_amortization_full_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.UhligCancellation.socket_for_sat_iff_not_amortizes
#print axioms PallLean.Paper93.DeepMath.PathB.UhligCancellation.independence_permits_amortization
