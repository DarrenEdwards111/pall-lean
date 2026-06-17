import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0GuessableProver

/-!
# IKW small-prover — easy-witness vs. an incompressible (hard) strategy (proved extraction)

Entry 224 (`…ACC0GuessableProver`) proved the guessable-prover *collapse mechanism* (`mipLang_eq_maLang`: under
`GuessableProver`, the `MIP` language equals an `MA` language) and left **`GuessableProver`** itself — that under the
circuit hypothesis an accepting prover strategy has a small-circuit description — as the named **Impagliazzo–Kabanets–
Wigderson easy-witness** socket.  This file opens that socket as far as the discipline allows: it proves the genuine
**hardness extraction** at its core — *failure* of the easy-witness property at an input yields an accepting prover
strategy that no circuit describes (an incompressible, i.e. hard, object) — and discharges `GuessableProver` from the
IKW easy-witness lemma.  The honest punchline: the easy-witness lemma's *other horn is a hard function*, so the IKW
small-prover atom bottoms out at the **same separation-strength hard-function atom as step 5** — which is exactly why
hardness magnification / IKW is `P ≠ NP`-strength (cf. the metacomplexity memory entries).

## What is proved (clean axioms, no `sorry`)

* **`IncompressibleAcceptingProver Ver proverOf x`** — an accepting prover strategy `p` (`Ver x p`) that equals *no*
  circuit's decoding (`∀ C, proverOf C ≠ p`): a hard, circuit-incompressible witness.
* **`not_easy_gives_incompressible`** (PROVED, **no axioms**) — if `x` is accepted (`∃ p, Ver x p`) but *no* circuit
  gives an accepting prover (`¬ ∃ C, Ver x (proverOf C)`), then `IncompressibleAcceptingProver Ver proverOf x`: the
  failure of easy-witness *is* an incompressible accepting strategy.  This is the exact hardness object the easy-witness
  lemma must rule out.
* **`EasyWitnessLemma circuitHyp Ver proverOf`** — the IKW easy-witness socket: the circuit hypothesis rules out
  incompressible accepting strategies (`circuitHyp → ∀ x, ¬ IncompressibleAcceptingProver …`).
* **`guessableProver_of_easyWitness`** (PROVED) — discharges the entry-224 `GuessableProver` from `EasyWitnessLemma`:
  if no input has an incompressible accepting strategy, every accepting input has a circuit-describable prover.
* **`not_guessableProver_gives_incompressible`** (PROVED) — the punchline: `GuessableProver` *failure* yields some input
  with an incompressible accepting strategy — pinpointing the hard-function obstruction (the converse is false; see the
  theorem note).

## Honest scope

This proves the **hardness extraction** (`not_easy_gives_incompressible`, no axioms) — that the failure of the
easy-witness property is precisely an incompressible (hard) accepting strategy — and the discharge of `GuessableProver`
from the IKW easy-witness lemma (`guessableProver_of_easyWitness`), plus the exact dichotomy.  What remains the named
socket is **`EasyWitnessLemma`**: that the circuit hypothesis `NEXP ⊆ ACC⁰` *actually rules out* incompressible
accepting witnesses — the Impagliazzo–Kabanets–Wigderson easy-witness theorem (proved via the Karp–Lipton collapse
`NEXP ⊆ ACC⁰ ⟹ NEXP = MA`, entries 202/221, plus the witness-search hardness argument).  Crucially, the obstruction
this socket must defeat — an `IncompressibleAcceptingProver`, a function with no small circuit — is the **same
separation-strength hard-function atom as step 5**: the IKW small-prover does not reduce below the circuit lower bound.
This proves the extraction and the discharge logic, not the easy-witness lemma.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0IKWSmallProver

open PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver (GuessableProver)

variable {Prover Circ : Type} (Ver : List Bool → Prover → Prop) (proverOf : Circ → Prover)

/-- **An incompressible (hard) accepting strategy.**  An accepting prover `p` (`Ver x p`) that equals *no* circuit's
decoding (`∀ C, proverOf C ≠ p`) — a circuit-incompressible witness, i.e. a hard object of the kind the separation
needs. -/
def IncompressibleAcceptingProver (x : List Bool) : Prop :=
  ∃ p : Prover, Ver x p ∧ ∀ C : Circ, proverOf C ≠ p

/-- **The hardness extraction (PROVED, no axioms).**  If `x` is accepted (`∃ p, Ver x p`) but no circuit gives an
accepting prover (`¬ ∃ C, Ver x (proverOf C)`), then there is an *incompressible* accepting prover at `x`: the
accepting strategy `p` cannot equal any circuit's decoding, since otherwise that circuit would be an accepting prover.
This is the exact hard object the easy-witness lemma must rule out — the failure of easy-witness *is* hardness. -/
theorem not_easy_gives_incompressible (x : List Bool) (hw : ∃ p, Ver x p)
    (hne : ¬ ∃ C, Ver x (proverOf C)) :
    IncompressibleAcceptingProver Ver proverOf x := by
  obtain ⟨p, hp⟩ := hw
  refine ⟨p, hp, fun C hC => hne ⟨C, ?_⟩⟩
  rw [hC]; exact hp

/-- **The IKW easy-witness socket.**  The circuit hypothesis `NEXP ⊆ ACC⁰` rules out incompressible accepting
strategies: every accepting prover can be taken circuit-describable.  This is the Impagliazzo–Kabanets–Wigderson
easy-witness theorem (proved via the Karp–Lipton collapse + witness-search hardness).  Stated, not proved. -/
def EasyWitnessLemma (circuitHyp : Prop) : Prop :=
  circuitHyp → ∀ x, ¬ IncompressibleAcceptingProver Ver proverOf x

/-- **Discharges the entry-224 `GuessableProver` socket (PROVED).**  Given the IKW easy-witness lemma (the circuit
hypothesis rules out incompressible accepting strategies), every accepting input has a circuit-describable prover —
exactly `GuessableProver`.  Proof: an accepted `x` with no circuit prover would yield an incompressible accepting
strategy (`not_easy_gives_incompressible`), which the easy-witness lemma forbids. -/
theorem guessableProver_of_easyWitness (circuitHyp : Prop) (hyp : circuitHyp)
    (ew : EasyWitnessLemma Ver proverOf circuitHyp) :
    GuessableProver Ver proverOf := by
  intro x hw
  by_contra hne
  exact ew hyp x (not_easy_gives_incompressible Ver proverOf x hw hne)

/-- **The honest punchline (PROVED): `GuessableProver` failure yields a hard function.**  If `GuessableProver` fails,
some accepted input has an incompressible (circuit-uncomputable) accepting strategy — a hard, separation-strength
function.  So the IKW small-prover atom does not reduce below the circuit lower bound: defeating its obstruction *is*
producing/ruling out a hard function, the same atom as step 5.  (Note: the converse is false — an incompressible
accepting strategy at `x` does not preclude a *different* circuit-describable accepting prover there; the obstruction to
`GuessableProver` is "accepted but *no* circuit prover", which `not_easy_gives_incompressible` then turns into
hardness.) -/
theorem not_guessableProver_gives_incompressible (h : ¬ GuessableProver Ver proverOf) :
    ∃ x, IncompressibleAcceptingProver Ver proverOf x := by
  unfold GuessableProver at h
  push_neg at h
  obtain ⟨x, hw, hne⟩ := h
  exact ⟨x, not_easy_gives_incompressible Ver proverOf x hw (not_exists.mpr hne)⟩

end PallLean.Paper93.DeepMath.PathB.ACC0IKWSmallProver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IKWSmallProver.not_easy_gives_incompressible
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IKWSmallProver.guessableProver_of_easyWitness
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0IKWSmallProver.not_guessableProver_gives_incompressible
