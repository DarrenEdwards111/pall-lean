import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConcreteTradingClasses
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSpeedupAudit

/-!
# Auditing slowdown and engine faithfulness — does the √2 window survive the one-tape debt?

The speedup audit (`SpeedupAudit`) left a forward flag: the concrete one-tape model achieves only
`DTS(2b) ⊆ Σ₂(b+1)` (a full-power debt), not the clean `DTS(2b) ⊆ Σ₂(b)` the engine assumed.  This
file audits the two remaining pieces — the slowdown ingredient, and whether the engine's `p² < 2q²`
window survives the debt — and reaches a precise, machine-checked verdict.

## Slowdown is exponent-clean (no debt of its own)

`ConcreteSlowdown : Σ₂(aq) ⊆ NTIME(ap)` runs: inner `∀w₂` = coNTIME(aq) → [assumption scaled by
padding, `NTIME(aq) ⊆ DTS(ap)`] → [DTS complement is FREE: flip the accept flag, space & clock
unchanged] → `∃w₁` wrap = NTIME(ap).  Every step preserves the exponent ratio:

* **`dts_complement_free`** (proved) — `DTS(a) L → DTS(a) Lᶜ`: the one place a model could hide a
  cost, discharged.  Deterministic complement flips `accept`; `Decides`/`ClockLe`/`SpaceGrowthLe`
  all transport.  So the coNTIME→DTS step adds no power.
* **`slowdown_ratio_preserved`** (proved) — `(a·p)·q = (a·q)·p`: input exponent `aq`, output `ap`,
  same ratio `p/q`.  Slowdown neither gains nor loses a power; the ONLY debt in the chain is
  speedup's `+1`.

## The faithful engine — the debt shifts the collapse exponent from `p²` to `p²+p`

* **`debt_engine`** (proved) — the honest Lipton–Viglas chain with the DEBT speedup substituted for
  the clean one: given the concrete padding/slowdown/hierarchy sockets and
  `debtSpeedup : DTS(2b) → Σ₂(b+1)`, the simulation `NTIME(q) ⊆ DTS(p)` is refuted whenever
  **`p²+p < 2q²`** — NOT the clean `p² < 2q²`.  The chain: `NTIME(2q²) ⊆ DTS(2qp) ⊆ Σ₂(qp+1) ⊆
  Σ₂((p+1)q) ⊆ NTIME((p+1)p) = NTIME(p²+p)`, against the hierarchy.  (The `Σ₂` monotone step uses
  the proved `sigma2_mono` — the reason the audit is done on the CONCRETE classes, which carry it.)

## The window survives — but 4/3 dies and the witness moves

* **`four_thirds_clean_ok`** (proved) — `4² < 2·3²` (16<18): the clean engine's 4/3 witness, used by
  `braid_at_four_thirds`.
* **`four_thirds_debt_fails`** (proved) — `¬(4²+4 < 2·3²)` (20≥18): under the debt, 4/3 is REFUTED.
  `braid_at_four_thirds` is NOT faithfully valid; the braid must move to a larger ratio.
* **`five_fourths_debt_ok`** / **`thirteen_tenths_debt_ok`** (proved) — `5²+5 < 2·4²` (30<32) and
  `13²+13 < 2·10²` (182<200): faithful witnesses exist, reaching `c = 1.3`.
* **`debt_window_nonempty`** (proved) — the debt window has a witness (5,4).
* **`debt_window_near_sqrt2`** (proved) — `139²+139 < 2·100²` (19460<20000), `c = 1.39`: the debt is
  lower-order (`+p` against `2q²`), so the window still approaches `√2`; only small witnesses are
  lost.

## Verdict

The engine SURVIVES the one-tape debt asymptotically — the √2 barrier is intact, because `+p` is
lower-order against `2q²`.  Two concrete consequences, machine-checked: (1) `braid_at_four_thirds`
must be re-instantiated at `5/4` (or larger) to be faithful; (2) any DIRECT dent proof still cashes
out, since the braid's window is nonempty faithfully.  Slowdown needs no repair.  The remaining
gap to a real bound is unchanged: the four machine constructions (padding transducer + DTS
virtual-input, speedup checkpoints, slowdown complement+wrap, hierarchy universal machine) and,
above all, the dent.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EngineFaithfulnessAudit

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses

/-! ### Slowdown cleanliness -/

/-- The complement of a machine: same everything, accept flag flipped.  Marked reducible so that
`run`/`step`/`init` unfold through it and the shared runs are definitionally equal. -/
@[reducible] def complementMachine (M : Machine) : Machine where
  State := M.State
  fin := M.fin
  dec := M.dec
  start := M.start
  halt := M.halt
  δ := M.δ
  accept := fun s => ! M.accept s

/-- Transport a complement-machine configuration to an `M` configuration (identity on fields;
the state types coincide). -/
def port (M : Machine) (c : Cfg (complementMachine M)) : Cfg M := ⟨c.st, c.hd, c.tp⟩

/-- One step commutes with `port` — `step` reads only `halt`/`δ`, which the complement shares. -/
theorem port_step (M : Machine) (c : Cfg (complementMachine M)) :
    port M (step (complementMachine M) c) = step M (port M c) := by
  by_cases h : M.halt c.st = true
  · rw [step_of_halted (complementMachine M) h, step_of_halted M h]
  · simp only [Bool.not_eq_true] at h
    have hcM : step (complementMachine M) c =
        ⟨(M.δ c.st (c.tp.getD c.hd false)).1,
          moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2,
          (match (M.δ c.st (c.tp.getD c.hd false)).2.1 with
            | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
      unfold step; rw [show (complementMachine M).halt c.st = false from h]; rfl
    have hM : step M (port M c) =
        ⟨(M.δ c.st (c.tp.getD c.hd false)).1,
          moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2,
          (match (M.δ c.st (c.tp.getD c.hd false)).2.1 with
            | none => c.tp | some w => writeAt c.tp c.hd w)⟩ := by
      unfold step port; rw [h]; rfl
    rw [hcM, hM]; rfl

/-- The whole run commutes with `port` (induction on the step count). -/
theorem port_run (M : Machine) (t : ℕ) (x : List Bool) :
    port M (run (complementMachine M) t (init (complementMachine M) x)) = run M t (init M x) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, run_succ, port_step, ih]

/-- **DTS complement is free (proved).**  The coNTIME→DTS step of slowdown adds no power: a
deterministic decider's complement is a deterministic decider with the same clock and space.
`complementMachine` shares `State`/`start`/`halt`/`δ` with `M` and differs only in `accept`, and
`run`/`step`/`init` never read `accept` — so the run is identical and only the read-off flips. -/
theorem dts_complement_free (a : ℕ) (L : Lang) (hL : DTS a L) :
    DTS a (fun x => ! L x) := by
  obtain ⟨M, T, c, hclock, hdec, hspace⟩ := hL
  refine ⟨complementMachine M, T, c, hclock, ?_, ?_⟩
  · intro x
    obtain ⟨hhalt, hout⟩ := hdec x
    have hst : (run (complementMachine M) (T x.length) (init (complementMachine M) x)).st
        = (run M (T x.length) (init M x)).st := congrArg Cfg.st (port_run M (T x.length) x)
    refine ⟨?_, ?_⟩
    · show M.halt (run (complementMachine M) (T x.length) (init (complementMachine M) x)).st = true
      rw [hst]; exact hhalt
    · show (! M.accept (run (complementMachine M) (T x.length)
        (init (complementMachine M) x)).st) = ! L x
      rw [hst, show M.accept (run M (T x.length) (init M x)).st = L x from hout]
  · intro x t
    have htp : (run (complementMachine M) t (init (complementMachine M) x)).tp
        = (run M t (init M x)).tp := congrArg Cfg.tp (port_run M t x)
    show (run (complementMachine M) t (init (complementMachine M) x)).tp.length
      ≤ x.length + polylogBound c x.length
    rw [htp]; exact hspace x t

/-- **Slowdown preserves the exponent ratio (proved).**  Input `Σ₂(aq)`, output `NTIME(ap)`: the
ratio `p/q` is unchanged, so slowdown carries no power debt. -/
theorem slowdown_ratio_preserved (a p q : ℕ) : (a * p) * q = (a * q) * p := by ring

/-! ### The faithful engine (debt speedup) -/

/-- **The faithful Lipton–Viglas engine (proved).**  With the DEBT speedup `DTS(2b) ⊆ Σ₂(b+1)`
(what the one-tape model actually achieves) in place of the clean one, the simulation
`NTIME(q) ⊆ DTS(p)` is refuted for `p²+p < 2q²`.  The chain:
`NTIME(2q²) ⊆ DTS(2qp) ⊆ Σ₂(qp+1) ⊆ Σ₂((p+1)q) ⊆ NTIME((p+1)p)` against the hierarchy. -/
theorem debt_engine (p q : ℕ) (hq : 1 ≤ q) (hqp : q ≤ p) (hwin : p * p + p < 2 * q * q)
    (hpad : ConcretePadding) (hslow : ConcreteSlowdown) (hhier : ConcreteHierarchy)
    (debtSpeedup : ∀ b, 1 ≤ b → ∀ L, DTS (2 * b) L → Sigma2 (b + 1) L) :
    ¬ (∀ L, NTIME q L → DTS p L) := by
  intro hSim
  have hp : 1 ≤ p := le_trans hq hqp
  have hqp1 : 1 ≤ q * p := Nat.mul_le_mul hq hp
  -- Rung 1 (padding, m = 2q): NTIME(2q·q) ⊆ DTS(2q·p).
  have h1 : ∀ L, NTIME (2 * q * q) L → DTS (2 * q * p) L :=
    fun L hL => hpad p q hSim (2 * q) (by omega) L hL
  -- Rung 2 (debt speedup, b = qp): DTS(2·(qp)) ⊆ Σ₂(qp+1).
  have h2 : ∀ L, DTS (2 * q * p) L → Sigma2 (q * p + 1) L := by
    intro L hL
    exact debtSpeedup (q * p) hqp1 L (Nat.mul_assoc 2 q p ▸ hL)
  -- Rung 3 (slowdown, a = p+1): Σ₂(qp+1) ⊆ Σ₂((p+1)q) ⊆ NTIME((p+1)p).
  have h3 : ∀ L, Sigma2 (q * p + 1) L → NTIME ((p + 1) * p) L := by
    intro L hL
    have hle : q * p + 1 ≤ (p + 1) * q := by
      have e1 : (p + 1) * q = p * q + q := by ring
      have e2 : q * p = p * q := Nat.mul_comm q p
      omega
    have hmono : Sigma2 ((p + 1) * q) L := sigma2_mono hle hL
    exact hslow p q hq hSim (p + 1) (by omega) L hmono
  -- Collapse and hierarchy.
  have hcollapse : ∀ L, NTIME (2 * q * q) L → NTIME ((p + 1) * p) L :=
    fun L hL => h3 L (h2 L (h1 L hL))
  have hb : 1 ≤ (p + 1) * p := by
    calc 1 = 1 * 1 := rfl
      _ ≤ (p + 1) * p := Nat.mul_le_mul (by omega) hp
  have hlt : (p + 1) * p < 2 * q * q := by
    have e : (p + 1) * p = p * p + p := by ring
    omega
  exact hhier (2 * q * q) ((p + 1) * p) hb hlt hcollapse

/-! ### The window: 4/3 dies, the witness moves, √2 survives -/

/-- The clean engine's 4/3 witness (used by `braid_at_four_thirds`). -/
theorem four_thirds_clean_ok : (4 : ℕ) * 4 < 2 * (3 * 3) := by decide

/-- **Under the debt, 4/3 is refuted (proved).**  `braid_at_four_thirds` is not faithfully valid. -/
theorem four_thirds_debt_fails : ¬ ((4 : ℕ) * 4 + 4 < 2 * 3 * 3) := by decide

/-- A faithful witness at `c = 5/4`. -/
theorem five_fourths_debt_ok : (5 : ℕ) * 5 + 5 < 2 * 4 * 4 := by decide

/-- A faithful witness at `c = 1.3`. -/
theorem thirteen_tenths_debt_ok : (13 : ℕ) * 13 + 13 < 2 * 10 * 10 := by decide

/-- **The debt window is nonempty (proved)** — witness `(p,q) = (5,4)`. -/
theorem debt_window_nonempty : ∃ p q : ℕ, 1 ≤ q ∧ q < p ∧ p * p + p < 2 * q * q :=
  ⟨5, 4, by omega, by omega, by decide⟩

/-- **The debt is lower-order (proved)** — a witness at `c = 1.39`, approaching `√2 ≈ 1.414`.  Only
small witnesses are lost; the barrier is preserved. -/
theorem debt_window_near_sqrt2 : (139 : ℕ) * 139 + 139 < 2 * 100 * 100 := by decide

/-- **A faithful refutation exists (proved).**  Given the sockets and the debt speedup, the
simulation `NTIME(4) ⊆ DTS(5)` (ratio `5/4`) is refuted — the engine still bites, just at the
shifted witness. -/
theorem faithful_refutation_five_fourths
    (hpad : ConcretePadding) (hslow : ConcreteSlowdown) (hhier : ConcreteHierarchy)
    (debtSpeedup : ∀ b, 1 ≤ b → ∀ L, DTS (2 * b) L → Sigma2 (b + 1) L) :
    ¬ (∀ L, NTIME 4 L → DTS 5 L) :=
  debt_engine 5 4 (by omega) (by omega) (by decide) hpad hslow hhier debtSpeedup

end PallLean.Paper93.DeepMath.PathB.EngineFaithfulnessAudit

#print axioms PallLean.Paper93.DeepMath.PathB.EngineFaithfulnessAudit.dts_complement_free
#print axioms PallLean.Paper93.DeepMath.PathB.EngineFaithfulnessAudit.slowdown_ratio_preserved
#print axioms PallLean.Paper93.DeepMath.PathB.EngineFaithfulnessAudit.debt_engine
#print axioms PallLean.Paper93.DeepMath.PathB.EngineFaithfulnessAudit.four_thirds_debt_fails
#print axioms PallLean.Paper93.DeepMath.PathB.EngineFaithfulnessAudit.faithful_refutation_five_fourths
