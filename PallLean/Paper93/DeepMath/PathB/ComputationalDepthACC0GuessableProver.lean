import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BFLCollapse

/-!
# The guessable-prover collapse — Merlin guesses the prover circuit, Arthur verifies (proved mechanism)

Entry 221 (`…ACC0BFLCollapse`) factored the deep Karp–Lipton inclusion `NEXP ⊆ ACC⁰ ⟹ NEXP ⊆ MA` as `NEXP = MIP`
(Babai–Fortnow–Lund, entry-221 `NexpEqMIP` socket) composed with the **guessable-prover collapse** `MIP ⊆ ACC⁰ ⟹
MIP ⊆ MA` (entry-221 `MIPSubsetMA_ofCircuits` socket).  This file opens up that second socket into its genuine
mechanism and **proves the collapse mechanism**, isolating the Impagliazzo–Kabanets–Wigderson small-prover content.

The mechanism.  An `MIP` computation accepts `x` iff *some prover strategy* makes the verifier accept:
`MIPLang Ver x := ∃ prover, Ver x prover` (the high-probability soundness/completeness check bundled into `Ver`).  That
existential over *all* prover strategies is the `MIP`/`NEXP`-strength guess.  Under the circuit hypothesis, the optimal
prover strategy is itself computed by a *small circuit* (IKW easy-witness / small-prover), so the existential collapses
to one over small circuits: Merlin guesses the circuit `C` describing the prover, and Arthur evaluates the verifier on
the circuit-computed prover `proverOf C` — an `MA` computation `MALang (fun x C => Ver x (proverOf C))`.

The two directions.  **Backward** (`MA ⊆ MIP`, free): a circuit-described prover *is* a prover, so if Arthur accepts
with circuit `C` then `proverOf C` makes the verifier accept, hence `MIP` accepts.  **Forward** (`MIP ⊆ MA`, the deep
direction): an accepting prover must have a *small-circuit description* — this is the `GuessableProver` socket, the IKW
content.  Their conjunction is the language equality `MIPLang Ver = MALang (…)`.

## What is proved (clean axioms, no `sorry`)

* **`MIPLang Ver`** / **`MALang Arthur`** — the language decided by an `MIP` verifier (`∃ prover, Ver x prover`) and an
  `MA` protocol (`∃ witness, Arthur x witness`).
* **`GuessableProver Ver proverOf`** — the IKW small-prover socket: every accepted input has an accepting prover
  *described by a small circuit* (`∀ x, (∃ p, Ver x p) → ∃ C, Ver x (proverOf C)`).
* **`mipLang_eq_maLang`** — the collapse mechanism (PROVED): given `GuessableProver`, `MIPLang Ver = MALang (fun x C =>
  Ver x (proverOf C))` — the `MIP` language *equals* an `MA` language.  Backward is free (a circuit-prover is a prover);
  forward is the socket.
* **`mipLang_mem_ma`** — the membership form (PROVED): with `GuessableProver` and the collapsed `MA`-language in `MA`,
  `MIPLang Ver ∈ MA`.
* **`mipSubsetMA_of_realized`** — discharges the entry-221 `MIPSubsetMA_ofCircuits` socket (PROVED) from
  `MIPRealizedGuessable` (under the circuit hypothesis every `MIP` language is an `MIPLang` with a guessable prover whose
  collapsed `MA`-language lands in `MA`).

## Honest scope

This proves the **guessable-prover collapse mechanism** — that an `MIP` verifier's language *equals* the `MA` language
"Merlin guesses the prover circuit, Arthur evaluates the verifier" — completely, including the free backward inclusion
(a circuit-prover is a prover) and the threading into the class-level `MIPSubsetMA_ofCircuits` socket.  What remains the
named socket is **`GuessableProver`** (bundled into `MIPRealizedGuessable`): that under the circuit hypothesis an
accepting prover strategy *has a small-circuit description* — the Impagliazzo–Kabanets–Wigderson small-prover /
easy-witness content (small circuits for the `NEXP`/`MIP` language ⟹ the optimal prover is a small circuit), which needs
the IKW machinery absent here.  This proves the collapse mechanism and its composition, not the small-prover theorem.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0BFLCollapse (MIPSubsetMA_ofCircuits)

/-- **The language decided by an `MIP` verifier.**  `x` is accepted iff *some* prover strategy `p` makes the verifier
accept (`Ver` bundles the high-probability soundness/completeness check).  The existential over all prover strategies is
the `MIP`/`NEXP`-strength guess. -/
def MIPLang {Prover : Type} (Ver : List Bool → Prover → Prop) : Lang :=
  fun x => ∃ p : Prover, Ver x p

/-- **The language decided by an `MA` protocol.**  Merlin guesses a witness `w` (a poly-size string), Arthur's
(randomized) check `Arthur x w` accepts. -/
def MALang {Wit : Type} (Arthur : List Bool → Wit → Prop) : Lang :=
  fun x => ∃ w : Wit, Arthur x w

/-- **The guessable-prover socket (the IKW small-prover content).**  Under the circuit hypothesis, every accepted input
has an accepting prover strategy that is *described by a small circuit* `C : Circ` via `proverOf` — `∀ x, (∃ p, Ver x p)
→ ∃ C, Ver x (proverOf C)`.  Stated, not proved: this is the Impagliazzo–Kabanets–Wigderson small-prover / easy-witness
theorem (small circuits for the `NEXP`/`MIP` language ⟹ the optimal prover strategy is itself a small circuit). -/
def GuessableProver {Prover Circ : Type} (Ver : List Bool → Prover → Prop)
    (proverOf : Circ → Prover) : Prop :=
  ∀ x, (∃ p : Prover, Ver x p) → ∃ C : Circ, Ver x (proverOf C)

/-- **The guessable-prover collapse mechanism (PROVED).**  Given the `GuessableProver` hypothesis, the `MIP` language
*equals* the `MA` language "Merlin guesses the prover circuit `C`, Arthur evaluates the verifier on `proverOf C`":
`MIPLang Ver = MALang (fun x C => Ver x (proverOf C))`.

The two directions are visible: the **backward** inclusion (`MA ⊆ MIP`) is free — a circuit-described prover `proverOf C`
*is* a prover, so an accepting `C` yields an accepting prover (`⟨proverOf C, hC⟩`); the **forward** inclusion
(`MIP ⊆ MA`) is exactly the `GuessableProver` socket (an accepting prover has a small-circuit description). -/
theorem mipLang_eq_maLang {Prover Circ : Type} (Ver : List Bool → Prover → Prop)
    (proverOf : Circ → Prover) (hg : GuessableProver Ver proverOf) :
    MIPLang Ver = MALang (fun x C => Ver x (proverOf C)) := by
  funext x
  apply propext
  constructor
  · -- forward: the small-prover socket turns an accepting prover into an accepting prover *circuit*
    intro hx; exact hg x hx
  · -- backward (free): a circuit-described prover is a prover
    rintro ⟨C, hC⟩; exact ⟨proverOf C, hC⟩

/-- **Membership form of the collapse (PROVED).**  If the verifier's provers are guessable and the collapsed
`MA`-language lies in the class `MA`, then `MIPLang Ver ∈ MA` — the `MIP` language is an `MA` language. -/
theorem mipLang_mem_ma {Prover Circ : Type} (Ver : List Bool → Prover → Prop)
    (proverOf : Circ → Prover) (MA : CClass) (hg : GuessableProver Ver proverOf)
    (hmem : MALang (fun x C => Ver x (proverOf C)) ∈ MA) :
    MIPLang Ver ∈ MA := by
  rw [mipLang_eq_maLang Ver proverOf hg]; exact hmem

/-- **The class-level realization socket.**  Under the circuit hypothesis `MIP ⊆ ACC⁰`, every `MIP` language is the
`MIPLang` of some verifier whose provers are guessable (`GuessableProver`) and whose collapsed `MA`-language lands in
`MA`.  This bundles the entry-221 `MIPSubsetMA_ofCircuits` content into the concrete model: the `MIP = ∃-prover`
realization, the IKW small-prover (`GuessableProver`), and the `MA`-class closure. -/
def MIPRealizedGuessable (MIP ACC0 MA : CClass) : Prop :=
  MIP ⊆ ACC0 → ∀ L ∈ MIP, ∃ (Prover Circ : Type) (Ver : List Bool → Prover → Prop)
    (proverOf : Circ → Prover),
      L = MIPLang Ver ∧ GuessableProver Ver proverOf ∧
      MALang (fun x C => Ver x (proverOf C)) ∈ MA

/-- **Discharges the entry-221 `MIPSubsetMA_ofCircuits` socket (PROVED glue).**  From `MIPRealizedGuessable` — that
under the circuit hypothesis every `MIP` language realizes as an `MIPLang` with a guessable prover and an `MA`-class
collapsed language — the guessable-prover collapse (`mipLang_eq_maLang`) gives `MIP ⊆ MA` under circuits, i.e. the
entry-221 `MIPSubsetMA_ofCircuits MIP ACC0 MA`. -/
theorem mipSubsetMA_of_realized (MIP ACC0 MA : CClass)
    (h : MIPRealizedGuessable MIP ACC0 MA) :
    MIPSubsetMA_ofCircuits MIP ACC0 MA := by
  intro hsub L hL
  obtain ⟨Prover, Circ, Ver, proverOf, hLeq, hg, hmem⟩ := h hsub L hL
  rw [hLeq, mipLang_eq_maLang Ver proverOf hg]
  exact hmem

end PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver.mipLang_eq_maLang
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver.mipLang_mem_ma
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessableProver.mipSubsetMA_of_realized
