import Mathlib.Tactic

/-!
# The Global God-Move obligation, made precise — and what it actually is

This formalizes the *logical skeleton* of the paper's "Global God-Move / amplituhedron extraction" route
(`SCOPE_GODMOVE_OBLIGATION.md`), per the plan: state the exact obligation, isolate the two load-bearing
lemmas (`godMove_correct`, `godMove_rank_monotone`), and confront them with the central danger.

The result is a **theorem about the obligation itself**: the God-Move gauge — a rank-monotone, witness-free,
instance-uniform projection `T_Φ` that collapses the P-side rank below `B` yet preserves a rank-`k` identity
minor — **cannot exist when `B < k`** (`B = n²⁰⁰`, `k = C(n/3, log n)`, `B < k` at `n = 2⁸⁰⁴`).  Hence
`GlobalGodMoveHyp` is **equivalent to** "no hard instance exists" — the restricted separation itself.

**Consequence (honest).**  Route G is *not* an independent path to `P ≠ NP`.  Proving `GlobalGodMoveHyp`
cannot be done by *constructing* a gauge — for a hard instance no such gauge exists (it is internally
contradictory by the rank sandwich).  It can only be done by proving no hard instance exists, i.e. by
proving the separation directly.  The amplituhedron / God-Move language is a faithful re-encoding of the
problem, not a reduction of it.
-/

namespace PallLean.Paper93.DeepMath.PathB.GodMoveObligation

/-- A projection `T` is **rank-monotone** for a rank functional `R` if it never increases rank
(the load-bearing `godMove_rank_monotone` property). -/
def RankMonotone {V : Type*} (R : V → ℕ) (T : V → V) : Prop := ∀ p, R (T p) ≤ R p

/-- A **God-Move gauge** for instance `p₀`: a rank-monotone map `T` (the witness-free, instance-uniform
projection `T_Φ`) that collapses the P-side rank to `≤ B` yet preserves a rank-`k` identity minor.  This
bundles the paper's two load-bearing claims — `godMove_correct` (the extracted object is `T_Φ p₀`, with its
preserved minor `k ≤ R (T p₀)`) and `godMove_rank_monotone` (`RankMonotone R T`) — together with the
projected P-side bound `R (T p₀) ≤ B`. -/
def GodMoveGaugeExists {V : Type*} (R : V → ℕ) (p₀ : V) (B k : ℕ) : Prop :=
  ∃ T : V → V, RankMonotone R T ∧ R (T p₀) ≤ B ∧ k ≤ R (T p₀)

/-- **The central danger, made a theorem.**  A God-Move gauge cannot collapse the rank *below* a minor it
preserves: if `B < k`, no such gauge exists.  This is exactly the rank sandwich
`k ≤ R (T p₀) ≤ B < k` — `godMove_rank_monotone` + the projected P-side bound, confronted with the
axiom-free NP-side minor.  **Proved, not assumed.** -/
theorem not_godMoveGaugeExists_of_gap {V : Type*} (R : V → ℕ) (p₀ : V) (B k : ℕ) (hgap : B < k) :
    ¬ GodMoveGaugeExists R p₀ B k := by
  rintro ⟨T, _hmono, hpside, hminor⟩; omega

/-- The **Global God-Move hypothesis**: for every *hard* instance `i` (a SAT-decider's compilation, with
P-side budget `B i` and preserved minor `k i`), the God-Move gauge exists. -/
def GlobalGodMoveHyp {ι V : Type*} (Hard : ι → Prop) (R : ι → V → ℕ) (poly : ι → V) (B k : ι → ℕ) : Prop :=
  ∀ i, Hard i → GodMoveGaugeExists (R i) (poly i) (B i) (k i)

/-- **The honest verdict: `GlobalGodMoveHyp ↔ ¬ ∃ hard instance`** — given the rank gap `B i < k i` on
every instance.  The God-Move is **not a route to** the separation; it **is** the separation, in gauge
language.  Proving `GlobalGodMoveHyp` cannot mean *constructing* a gauge (impossible for a hard instance, by
`not_godMoveGaugeExists_of_gap`); it can only mean proving no hard instance exists — the separation itself.
-/
theorem globalGodMoveHyp_iff_no_hard {ι V : Type*}
    (Hard : ι → Prop) (R : ι → V → ℕ) (poly : ι → V) (B k : ι → ℕ) (hgap : ∀ i, B i < k i) :
    GlobalGodMoveHyp Hard R poly B k ↔ ¬ ∃ i, Hard i := by
  constructor
  · rintro hGM ⟨i, hi⟩
    exact not_godMoveGaugeExists_of_gap (R i) (poly i) (B i) (k i) (hgap i) (hGM i hi)
  · rintro hno i hi; exact absurd ⟨i, hi⟩ hno

/-- Tiny instance (sanity): with `R = id`, `B = 3 < k = 5`, no gauge can both keep `R (T p₀) ≤ 3` and
`5 ≤ R (T p₀)`. -/
theorem tiny_no_gauge : ¬ GodMoveGaugeExists (V := ℕ) (fun m => m) 0 3 5 :=
  not_godMoveGaugeExists_of_gap _ _ 3 5 (by norm_num)

end PallLean.Paper93.DeepMath.PathB.GodMoveObligation

#print axioms PallLean.Paper93.DeepMath.PathB.GodMoveObligation.globalGodMoveHyp_iff_no_hard
#print axioms PallLean.Paper93.DeepMath.PathB.GodMoveObligation.not_godMoveGaugeExists_of_gap
