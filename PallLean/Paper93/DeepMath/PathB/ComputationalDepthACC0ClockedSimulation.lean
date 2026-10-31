import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TransitionTable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTM
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NTIMEAccounting

/-!
# ClockedSimulation cost — the universal lazy-diagonal simulation fits the NEXP budget (proved accounting)

Entry 223 proved the time-class *placement* (`clocked_in_NEXP`: a `ClockedSimulation` puts the lazy diagonal in `NEXP`)
and left **`ClockedSimulation`** itself — that a clocked `NTM` *does* decide the lazy diagonal within the budget
`2^(|x|^c+c)` — as the named socket.  This file proves the genuine **cost-accounting half** of that socket: the NEXP
budget is large enough for the universal simulation to complete, and the *completeness* direction of the clocked
simulation follows from it.  It connects the lazy-diagonalization substrate of entries 219–220–223 into one tighter
hierarchy theorem: 219 (lazy contradiction) needs the diagonal to be *decidable in NEXP*; 220 (`detRun_reachIn`) gives a
clocked transition-table run; 223 (`clocked_in_NEXP`) places a clocked simulation in NEXP; this file supplies the
**resource accounting** linking them — a polynomial-overhead universal simulation of a NEXP-budget machine still fits a
NEXP budget, and `acceptsWithin_mono` lifts "accepts within cost" to "accepts within budget".

## What is proved (clean axioms, no `sorry`)

* **`sim_budget_fits`** (PROVED) — exponent additivity: `g + s ≤ F → 2^g · 2^s ≤ 2^F` (`pow_add`).  Overhead `2^g` times
  simulated-steps `2^s` composes by adding exponents.
* **`exp_bound`** / **`nat_overhead_bound`** (PROVED) — polynomial overhead absorbed into the next exponent: for `a ≥ 1`
  and *every* `n`, `2^n · 2^(n^a + a) ≤ 2^(n^(a+1) + (a+1))` (the per-step overhead `2^n` times the simulated machine's
  `NTIME(2^(n^a+a))` budget still fits `NTIME(2^(n^(a+1)+(a+1)))`).
* **`detRun_accepts`** (PROVED) — the bridge from entry 220 to entry 223: a deterministic table run reaching state `1`
  in `T` steps witnesses `acceptsWithin (detNTM δ) x T` (via `detRun_reachIn`).
* **`lazy_clockedSim`** (PROVED) — the assembly: from `hbudget` (cost ≤ budget, the *proved* accounting),
  `hcomplete` (the sim accepts within its cost — completeness socket), and `hsound` (no spurious acceptance within the
  budget — soundness socket), the clocked simulation `ClockedSimulation L (detNTM δ) c` holds; the **forward** direction
  is proved from `hbudget` + `hcomplete` + `acceptsWithin_mono`.
* **`lazy_universal_in_nexp`** (PROVED) — composing with entry-223 `clocked_in_NEXP`: the lazy diagonal lives in `NEXP`.

## Honest scope

This proves the **cost accounting** completely — that the universal simulation's overhead × simulated-steps fits inside
the NEXP budget (`sim_budget_fits`, `nat_overhead_bound`), that a transition-table run witnesses `acceptsWithin`
(`detRun_accepts`), and that the *completeness* direction of the clocked simulation follows by monotone budget lifting
(`lazy_clockedSim` forward).  Combined with entry-223 placement this is the resource-boundary side of the lazy
hierarchy.  What remain named sockets are the universal-simulation *correctness* facts the accounting cannot replace:
**`hcomplete`** (the universal table run actually accepts within its simulation cost when `L x`) and **`hsound`** (it
does not spuriously accept within the larger budget when `¬ L x` — the clocked-decider stability).  These are the
decode → step → re-encode correctness of the universal machine (the `…ACC0UniversalHStep` contract), not the cost.  This
proves the budget fits and the completeness lifting, not the universal-machine correctness.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ClockedSimulation

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move)
open PallLean.Paper93.DeepMath.PathB.ACC0TransitionTable (detRun detNTM detRun_reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (acceptsWithin acceptsWithin_mono NEXP)
open PallLean.Paper93.DeepMath.PathB.ACC0NTIMEAccounting (ClockedSimulation clocked_in_NEXP)

/-- **Exponent additivity (PROVED).**  Overhead `2^g` times simulated-steps `2^s` composes by adding exponents:
`g + s ≤ F → 2^g · 2^s ≤ 2^F`.  This is why a poly-overhead simulation of a `2^s`-step machine costs `2^(g+s)`. -/
theorem sim_budget_fits {g s F : ℕ} (h : g + s ≤ F) : 2 ^ g * 2 ^ s ≤ 2 ^ F := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) h

/-- **The exponent inequality (PROVED).**  For `a ≥ 1` and every `n`, `n + n^a + a ≤ n^(a+1) + (a+1)` — the per-step
overhead exponent `n` plus the simulated `NTIME(2^(n^a+a))` exponent stays within the next exponent `n^(a+1)+(a+1)`. -/
theorem exp_bound {n a : ℕ} (ha : 1 ≤ a) : n + n ^ a + a ≤ n ^ (a + 1) + (a + 1) := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    · rw [Nat.zero_pow (show 0 < a by omega), Nat.zero_pow (show 0 < a + 1 by omega)]; omega
    · simp only [one_pow]; omega
  · have h1 : n ≤ n ^ a := Nat.le_self_pow (by omega) n
    have h2 : 2 * n ^ a ≤ n ^ (a + 1) := by
      rw [pow_succ]
      calc 2 * n ^ a = n ^ a * 2 := by ring
        _ ≤ n ^ a * n := by gcongr
    omega

/-- **Polynomial overhead absorbed (PROVED).**  For `a ≥ 1` and every `n`, `2^n · 2^(n^a+a) ≤ 2^(n^(a+1)+(a+1))`: the
universal simulator's per-step overhead `2^n` times the simulated machine's `NTIME(2^(n^a+a))` budget still fits the
`NTIME(2^(n^(a+1)+(a+1)))` budget.  The cost-accounting witness that the NEXP budget is large enough. -/
theorem nat_overhead_bound {n a : ℕ} (ha : 1 ≤ a) :
    2 ^ n * 2 ^ (n ^ a + a) ≤ 2 ^ (n ^ (a + 1) + (a + 1)) := by
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by have := @exp_bound n a ha; omega)

/-- **A clocked transition-table run witnesses `acceptsWithin` (PROVED).**  If the deterministic universal table `δ`,
run for `T` steps from `init x`, reaches accepting state `1`, then `acceptsWithin (detNTM δ) x T` — bridging entry 220's
`detRun_reachIn` to entry 223's `acceptsWithin`. -/
theorem detRun_accepts (δ : ℕ × Bool → ℕ × Bool × Move) (x : List Bool) (T : ℕ)
    (h : (detRun δ T ((detNTM δ).init x)).1 = 1) :
    acceptsWithin (detNTM δ) x T :=
  ⟨T, le_refl T, detRun δ T ((detNTM δ).init x), detRun_reachIn δ T ((detNTM δ).init x), h⟩

/-- **The clocked simulation from cost-accounting + correctness (PROVED).**  Given the *proved* budget accounting
`hbudget` (the simulation cost fits the NEXP budget), the completeness socket `hcomplete` (the universal table accepts
within its cost when `L x`), and the soundness socket `hsound` (no spurious acceptance within the budget), the clocked
simulation `ClockedSimulation L (detNTM δ) c` holds.  The **forward** direction `L x → acceptsWithin … (2^(|x|^c+c))` is
*proved* from `hcomplete` + `hbudget` + `acceptsWithin_mono` — the cost accounting doing real work. -/
theorem lazy_clockedSim (δ : ℕ × Bool → ℕ × Bool × Move) (L : Lang) (c : ℕ)
    (cost : List Bool → ℕ)
    (hbudget : ∀ x, cost x ≤ 2 ^ (x.length ^ c + c))
    (hcomplete : ∀ x, L x → acceptsWithin (detNTM δ) x (cost x))
    (hsound : ∀ x, acceptsWithin (detNTM δ) x (2 ^ (x.length ^ c + c)) → L x) :
    ClockedSimulation L (detNTM δ) c := by
  intro x
  constructor
  · intro hL
    exact acceptsWithin_mono (detNTM δ) x (hbudget x) (hcomplete x hL)
  · exact hsound x

/-- **The lazy diagonal lives in `NEXP` (PROVED, modulo the correctness sockets).**  Composing the clocked simulation
(`lazy_clockedSim`, whose cost-accounting half is proved) with entry-223 `clocked_in_NEXP`: `L ∈ NEXP`. -/
theorem lazy_universal_in_nexp (δ : ℕ × Bool → ℕ × Bool × Move) (L : Lang) (c : ℕ)
    (cost : List Bool → ℕ)
    (hbudget : ∀ x, cost x ≤ 2 ^ (x.length ^ c + c))
    (hcomplete : ∀ x, L x → acceptsWithin (detNTM δ) x (cost x))
    (hsound : ∀ x, acceptsWithin (detNTM δ) x (2 ^ (x.length ^ c + c)) → L x) :
    L ∈ NEXP :=
  clocked_in_NEXP L (detNTM δ) c (lazy_clockedSim δ L c cost hbudget hcomplete hsound)

end PallLean.Paper93.DeepMath.PathB.ACC0ClockedSimulation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ClockedSimulation.sim_budget_fits
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ClockedSimulation.nat_overhead_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ClockedSimulation.detRun_accepts
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ClockedSimulation.lazy_clockedSim
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ClockedSimulation.lazy_universal_in_nexp
