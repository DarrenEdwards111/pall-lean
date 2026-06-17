import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0GuessVerify
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EasyWitness
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FastSATVerifier

/-!
# GuessVerify discharge — connecting the language-level construction, the entry-150 socket, and the fast-SAT verifier

The existing `…ACC0GuessVerify` file proves the guess-and-verify construction *correct* at the language/verifier level
(`gvDecider_eq`: guessing only small witnesses decides exactly `L`; `guessVerify_subset`: the resulting collapse
`NTIME[2ⁿ] ⊆ NTIME[2ⁿ/superpoly]` given verifiers whose guess-and-verify deciders are fast).  This file *connects* that
proved construction to the abstract entry-150/189 **`GuessVerify`** socket
(`SmallWitnessCircuits → ACC0SatSpeedup → NTIME[2ⁿ] ⊆ NTIME[2ⁿ/superpoly]`) and to the entry-187 **fast-`ACC⁰`-SAT
verifier**, discharging the socket from the proved language-level collapse and tying the verify cost to the concrete
quasipolynomial bound.

## What is proved (clean axioms, no `sorry`)

* **`ProvidesFastVerifiers`** — the model socket: small witness circuits + the SAT speedup yield, for every
  `L ∈ NTIME[2ⁿ]`, a verifier with the small-witness reduction whose guess-and-verify decider lies in the fast class.
* **`guessVerify_discharge`** — discharges the entry-150 **`GuessVerify`** socket from `ProvidesFastVerifiers`, *via the
  existing proved* `guessVerify_subset` (the language-level collapse).
* **`guess_verify_beats_bruteforce_abstract`** — the time arithmetic: `verifyWork ≤ (D+1)·n^D + 1` and
  `guessCost + ((D+1)·n^D + 1) < 2ⁿ` ⇒ `guessCost + verifyWork < 2ⁿ`.
* **`guess_verify_beats_bruteforce`** — the concrete tie-in to the entry-187 `fast_sat_verifier`: with the verify work
  the count-cell image it examines, `guessCost + (verify work) < 2ⁿ` — guess the small circuit, verify with fast SAT,
  beat brute force.

## Honest scope

This connects three completed pieces — the proved language-level guess-and-verify collapse (`…ACC0GuessVerify`), the
abstract entry-150 `GuessVerify` socket, and the entry-187 fast-`ACC⁰`-SAT verifier — discharging the socket from the
proved collapse and proving the concrete *time bound* (guess cost + fast-SAT verify cost beats `2ⁿ`).  What remains a
named socket is `ProvidesFastVerifiers`: that small witnesses + the speedup actually place each guess-and-verify decider
in the fast `NTIME` class — the genuine `NTM`-cost content (the verify cost arithmetic here is exactly *why* it should,
but the placement in the formal `NTIME` class needs the machine model).  This proves the discharge glue and the time
bound, not the machine-level `NTIME` placement.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`, `ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyDischarge

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0EasyWitness (GuessVerify)
open PallLean.Paper93.DeepMath.PathB.ACC0GuessVerify (HasWitness SmallWitnessRed gvDecider guessVerify_subset)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount symEval)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0FastSATVerifier (fast_sat_verifier)

variable {n m D : ℕ}

/-- **The fast-verifier provision socket.**  Small witness circuits together with the `ACC⁰`-SAT speedup yield, for
every `L ∈ NTIME[2ⁿ]`, a verifier `V` and decoder `decode` with the small-witness reduction whose guess-and-verify
decider `gvDecider V decode` lies in the fast class `NTIME[2ⁿ/superpoly]` — the hypothesis the proved
`guessVerify_subset` consumes.  Stated, not proved (the `NTM`-cost placement). -/
def ProvidesFastVerifiers (NTIME2n NTIME2nFast : CClass) (ACC0SatSpeedup SmallWitnessCircuits : Prop) : Prop :=
  SmallWitnessCircuits → ACC0SatSpeedup →
    ∀ L ∈ NTIME2n, ∃ (V : List Bool → List Bool → Prop) (decode : List Bool → List Bool),
      HasWitness L V ∧ SmallWitnessRed V decode ∧ gvDecider V decode ∈ NTIME2nFast

/-- **Discharging the entry-150 `GuessVerify` socket (PROVED) — via the proved language-level collapse.**  Given
`ProvidesFastVerifiers` (small witnesses + speedup ⇒ fast verifiers), the *proved* `guessVerify_subset` (the
guess-and-verify decider equals `L`, so `L` inherits its fast complexity) yields `NTIME[2ⁿ] ⊆ NTIME[2ⁿ/superpoly]` —
exactly the entry-150 `GuessVerify` socket. -/
theorem guessVerify_discharge (NTIME2n NTIME2nFast : CClass) (ACC0SatSpeedup SmallWitnessCircuits : Prop)
    (prov : ProvidesFastVerifiers NTIME2n NTIME2nFast ACC0SatSpeedup SmallWitnessCircuits) :
    GuessVerify NTIME2n NTIME2nFast ACC0SatSpeedup SmallWitnessCircuits :=
  fun hsw hspeed => guessVerify_subset NTIME2n NTIME2nFast (prov hsw hspeed)

/-- **Guess-and-verify beats brute force — the arithmetic (PROVED).**  If the verify work is quasipolynomial
(`≤ (D+1)·n^D + 1`) and the guess cost plus that bound is below `2ⁿ`, the total guess-and-verify work
`guessCost + verifyWork` is `< 2ⁿ`. -/
theorem guess_verify_beats_bruteforce_abstract (guessCost verifyWork D n : ℕ)
    (hv : verifyWork ≤ (D + 1) * n ^ D + 1) (hb : guessCost + ((D + 1) * n ^ D + 1) < 2 ^ n) :
    guessCost + verifyWork < 2 ^ n :=
  lt_of_le_of_lt (Nat.add_le_add_left hv guessCost) hb

/-- **Guess-and-verify beats brute force — tied to the entry-187 fast-SAT verifier (PROVED).**  Running the verify step
with the entry-187 `fast_sat_verifier` (work the count-cell image it examines, `≤ (D+1)·n^D + 1`), the total
guess-and-verify work `guessCost + (verify work)` is `< 2ⁿ` whenever `guessCost + ((D+1)·n^D + 1) < 2ⁿ` — the concrete
realisation: guess the small witness circuit (cost `guessCost`), verify with fast `ACC⁰`-SAT, beat `2ⁿ`.  This is *why*
`ProvidesFastVerifiers` should hold. -/
theorem guess_verify_beats_bruteforce (mono : Fin m → Finset (Fin n)) (hh : ℕ → Bool)
    (hinj : Function.Injective mono) (hdeg : ∀ j, (mono j).card ≤ D) (hn : 1 ≤ n)
    (guessCost : ℕ) (hbound : guessCost + ((D + 1) * n ^ D + 1) < 2 ^ n) :
    guessCost + (Finset.univ.image (gateCount (fun j x => monoAND (mono j) x))).card < 2 ^ n :=
  lt_of_le_of_lt (Nat.add_le_add_left (fast_sat_verifier mono hh hinj hdeg hn).2 guessCost) hbound

end PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyDischarge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyDischarge.guessVerify_discharge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessVerifyDischarge.guess_verify_beats_bruteforce
