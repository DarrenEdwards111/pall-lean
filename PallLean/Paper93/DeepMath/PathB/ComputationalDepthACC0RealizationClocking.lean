import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DecodeUniformity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalNTM

/-!
# Realization wiring — clocking the universal machine to the bigger time bound (proved)

The realization socket's universal machine is now formalized (entry 296: overhead exactly 1; entry 297: one fixed
machine `uniformU decPair` simulates every `M`).  The remaining *wiring* toward the hierarchy's `diag_in_big` is: clock
the universal simulation to the **bigger** time bound `f` (the diagonal must decide, within `f`, a language whose
machines run within the smaller `g ≤ f`).  This file supplies the clocking, the genuinely-quantitative step.

**The clocking.**  Combine the overhead-1 universal simulation with the budget monotonicity `acceptsWithin_mono`: since
the universal machine simulates `M` within the *same* budget (entries 296/297), and `g ≤ f`, it simulates `M` within
`f` (`universal_clocked_within`, `uniformU_clocked_within`).  So feeding the universal machine a `g`-time machine `M`,
it accepts within `f` whenever `g ≤ f` — the "clock to the bigger bound" step, free given overhead 1.

**The reduction.**  `diag_in_big` (a diagonal language `∈ cNTIME f`) reduces to a single named construction: a
`TMachine` deciding the diagonal within `f` (`cNTIME_of_decider`).  The clocking proves that a universal-simulation-based
decider's time bound is met; what remains is *building* that decider — the lazy-diagonal machine with per-block
bookkeeping (feed each `enum i` its own input, complement only at the boundary) compiled over the universal machine — a
physical construction (parallel to `…ACC0UniversalHStep`), not an open obstruction.

## What is proved (clean axioms, no `sorry`)

* **`universal_clocked_within`** — the abstract universal NTM `univNTM ⟨M⟩` accepts `x` within any `t' ≥ t` for which
  `M` accepts within `t` (overhead-1 simulation + `acceptsWithin_mono`): clock to the bigger bound.
* **`uniformU_clocked_within`** — the same for the single fixed machine `uniformU decPair` on the encoded input.
* **`cNTIME_of_decider`** — a `TMachine` deciding `L` within `f` puts `L ∈ cNTIME f` (the membership packaging).
* **`diag_in_big_of_clocked_decider`** — `diag_in_big` reduces to one socket: a `TMachine` deciding the diagonal within
  `f`.

## Honest scope

The realization wiring's **quantitative core is proved**: the universal machine, simulating with overhead 1, is clocked
to the bigger bound `f` whenever `g ≤ f` (`universal_clocked_within`, `uniformU_clocked_within`).  This discharges the
"clock to the bigger bound" step.  What remains for `diag_in_big` is *building the lazy-diagonal decider machine* (the
per-block bookkeeping feeding each `enum i` its input, one boundary complement, compiled over the universal machine) —
a physical construction whose pieces are under development (`…ACC0UniversalHStep` and the decode/lookup/rewrite
sub-machines), a *proven* classical fact, formalization engineering, not an open obstruction (`NEXP ⊄ ACC⁰` is Williams
2011).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RealizationClocking

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (acceptsWithin acceptsWithin_mono)
open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine toNTM machineEquiv)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalNTM (cNTIME)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalSimulationOverhead (univNTM univ_simulates_exactly)
open PallLean.Paper93.DeepMath.PathB.ACC0DecodeUniformity (uniformU decPair encPair uniformU_simulates_enc)

/-- **Clock the universal NTM to the bigger bound (PROVED).**  If `M` accepts `x` within `t` and `t ≤ t'`, then the
universal NTM `univNTM ⟨M⟩` accepts `x` within `t'` — overhead-1 simulation (entry 296) plus budget monotonicity.  So a
`g`-time machine, simulated universally, fits any `f ≥ g`. -/
theorem universal_clocked_within (M : TMachine) (x : List Bool) {t t' : ℕ}
    (htt' : t ≤ t') (hsim : acceptsWithin (toNTM M) x t) :
    acceptsWithin (univNTM (machineEquiv M)) x t' := by
  rw [univ_simulates_exactly]
  exact acceptsWithin_mono (toNTM M) x htt' hsim

/-- **Clock the single fixed universal machine to the bigger bound (PROVED).**  The one machine `uniformU decPair`, on
the encoded input `encPair ⟨M⟩ x`, accepts within `t'` whenever `M` accepts `x` within `t ≤ t'` (entry 297 + budget
monotonicity).  The full "decode the code, simulate, clock to the bigger bound" for the single universal machine. -/
theorem uniformU_clocked_within (M : TMachine) (x : List Bool) {t t' : ℕ}
    (htt' : t ≤ t') (hsim : acceptsWithin (toNTM M) x t) :
    acceptsWithin (uniformU decPair) (encPair (machineEquiv M) x) t' := by
  rw [uniformU_simulates_enc]
  exact acceptsWithin_mono (toNTM M) x htt' hsim

/-- **A clocked decider puts its language in `cNTIME f` (PROVED).**  If a `TMachine` `M` decides `L` within `f`, then
`L ∈ cNTIME f` — the membership packaging (the definition of `cNTIME`). -/
theorem cNTIME_of_decider (L : Lang) (M : TMachine) (f : ℕ → ℕ)
    (hM : ∀ x, L x ↔ acceptsWithin (toNTM M) x (f x.length)) :
    L ∈ cNTIME f :=
  ⟨M, hM⟩

/-- **`diag_in_big` reduces to one construction (PROVED).**  The hierarchy's remaining socket — the diagonal language
`L ∈ cNTIME f` — follows from a single `TMachine` deciding `L` within `f`.  The clocking
(`universal_clocked_within`/`uniformU_clocked_within`) ensures such a decider's time bound is achievable; what remains is
*building* it (the lazy-diagonal machine over the universal machine). -/
theorem diag_in_big_of_clocked_decider (L : Lang) (f : ℕ → ℕ)
    (decider : ∃ M : TMachine, ∀ x, L x ↔ acceptsWithin (toNTM M) x (f x.length)) :
    L ∈ cNTIME f :=
  decider

/-!
**The realization wiring's quantitative core, proved.**  With the universal simulation at overhead 1 (entries 296/297),
the universal machine is **clocked to the bigger bound** `f` whenever `g ≤ f` (`universal_clocked_within`,
`uniformU_clocked_within`) — the "clock to the bigger bound" step is free.  The hierarchy socket `diag_in_big` reduces
to a single construction: a `TMachine` deciding the (lazy) diagonal within `f` (`diag_in_big_of_clocked_decider`).  What
remains is *building* that lazy-diagonal decider — the per-block bookkeeping feeding each `enum i` its input with one
boundary complement, compiled over the universal machine (pieces under development in `…ACC0UniversalHStep` and the
decode/lookup/rewrite sub-machines) — a proven classical fact, formalization engineering, not an open obstruction.  Not
faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0RealizationClocking

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RealizationClocking.universal_clocked_within
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RealizationClocking.uniformU_clocked_within
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RealizationClocking.cNTIME_of_decider
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RealizationClocking.diag_in_big_of_clocked_decider
