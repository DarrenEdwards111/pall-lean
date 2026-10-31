import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0GuessableProver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SumCheck

/-!
# MIP ⊆ NEXP — the prover table is the nondeterministic guess (proved mechanism)

Entry 225 left **`MipSubsetNexp`** (the simulation direction of `NEXP = MIP`) as a named socket.  This file proves its
mechanism: an `MIP` acceptance `∃ prover, Ver x prover` is *already* a nondeterministic existential — a `NEXP` machine
guesses the (exponential-size) prover table and deterministically verifies.  So `MIP ⊆ NEXP` reduces to the
verifier being exponential-time checkable given the table.

## What is proved (clean axioms, no `sorry`)

* **`NexpGuessLang Check := fun x => ∃ w, Check x w`** — a `NEXP` guess-and-check language.
* **`mipLang_eq_nexpGuess`** (PROVED, `rfl`) — `MIPLang Ver = NexpGuessLang Ver`: the existential over prover strategies
  *is* the nondeterministic guess.
* **`mipSubsetNexp_of_realized`** (PROVED) — discharges the entry-225 `MipSubsetNexp` socket from `MIPRealizedInNexp`
  (every `MIP` language is an `MIPLang Ver` whose guess-language lands in `NEXP`).

## Honest scope

This proves that the `MIP` existential *is* a nondeterministic guess (`mipLang_eq_nexpGuess`) and threads it into the
class-level `MipSubsetNexp` socket.  What remains the named socket is **`MIPRealizedInNexp`**: that the verifier `Ver`
(given the exponential prover table) is checkable within the `NEXP` time bound — the protocol/time-accounting content.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MipSimulation

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver (MIPLang)
open PallLean.Paper93.DeepMath.PathB.ACC0SumCheck (MipSubsetNexp)

/-- A `NEXP` nondeterministic guess-and-check language: guess a witness `w` (an exponential-size object), then
deterministically check `Check x w`. -/
def NexpGuessLang {W : Type} (Check : List Bool → W → Prop) : Lang := fun x => ∃ w : W, Check x w

/-- **The MIP existential is a nondeterministic guess (PROVED, `rfl`).**  `MIPLang Ver = NexpGuessLang Ver` — the
existential over prover strategies in an `MIP` computation *is* the `NEXP` guess of the (exponential) prover table. -/
theorem mipLang_eq_nexpGuess {Prover : Type} (Ver : List Bool → Prover → Prop) :
    MIPLang Ver = NexpGuessLang Ver := rfl

/-- **The realization socket.**  Under exponential-time verifiability, every `MIP` language is the `MIPLang` of some
verifier whose guess-language lands in `NEXP` (the prover table is the guess, `Ver` is the exp-time check). -/
def MIPRealizedInNexp (MIP NEXP : CClass) : Prop :=
  ∀ L ∈ MIP, ∃ (Prover : Type) (Ver : List Bool → Prover → Prop),
    L = MIPLang Ver ∧ NexpGuessLang Ver ∈ NEXP

/-- **Discharges the entry-225 `MipSubsetNexp` socket (PROVED).**  From `MIPRealizedInNexp`, each `MIP` language equals
`MIPLang Ver = NexpGuessLang Ver ∈ NEXP`. -/
theorem mipSubsetNexp_of_realized (MIP NEXP : CClass) (h : MIPRealizedInNexp MIP NEXP) :
    MipSubsetNexp MIP NEXP := by
  intro L hL
  obtain ⟨Prover, Ver, hLeq, hmem⟩ := h L hL
  rw [hLeq, mipLang_eq_nexpGuess]
  exact hmem

end PallLean.Paper93.DeepMath.PathB.ACC0MipSimulation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MipSimulation.mipLang_eq_nexpGuess
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MipSimulation.mipSubsetNexp_of_realized
