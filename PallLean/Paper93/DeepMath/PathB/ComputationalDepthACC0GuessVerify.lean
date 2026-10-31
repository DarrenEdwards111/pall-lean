import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsMetaTheorem

/-!
# Guess-and-verify — the construction's *correctness* proved, the complexity socketed

The guess-and-verify ingredient of Williams' route: *small witness circuits together with the `ACC⁰`-SAT speedup
simulate `NTIME[2ⁿ]` within `NTIME[2ⁿ/superpoly]`*.  This file makes the **logical pipeline precise** at the
language/verifier level and proves the part that is genuinely provable without machine details — the **correctness of
the guess-and-verify decider** — leaving only the time/complexity bound as the socket.

Setup (machine details abstract):

* a language `L` is given by a **verifier** `V` (`HasWitness`): `x ∈ L ↔ ∃ w, V x w`;
* the **small-witness reduction** (`SmallWitnessRed`, from IKW): every accepting `x` has a *circuit-described* witness
  `decode cw`;
* the **guess-and-verify decider** `gvDecider V decode x := ∃ cw, V x (decode cw)` — guess a small circuit code `cw`,
  verify `V x (decode cw)`.

## What is proved (clean axioms, no `sorry`)

* **`gvDecider_eq`** — the decider is *correct*: `gvDecider V decode x ↔ L x` (it decides exactly `L`).  This is the
  heart of guess-and-verify: guessing only *small* witnesses loses nothing.
* **`guessVerify_subset`** — the collapse: if every `L ∈ NTIME2n` has such a verifier whose guess-and-verify decider
  lies in `NTIME2nFast`, then `NTIME2n ⊆ NTIME2nFast`.  (The decider equals `L`, so `L` inherits its complexity.)

## Honest scope

The guess-and-verify *construction* is proved correct (`gvDecider_eq`: guessing small witnesses decides the right
language), and the language-level collapse glue is proved.  The remaining socket is bundled in
`guessVerify_subset`'s hypothesis: that the guess-and-verify decider actually lies in `NTIME2nFast` — i.e. guessing a
*small* circuit costs `poly` and verifying it via the `ACC⁰`-SAT speedup costs `2ⁿ/superpoly`.  That time bound needs
the `NTM` cost machinery (it is the genuine complexity content).  This **does not** prove `NTIME2n ⊆ NTIME2nFast`
outright.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0GuessVerify

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)

/-- **Verifier characterisation**: `L` is decided by a verifier `V` — `x ∈ L ↔ ∃ witness w, V x w`. -/
def HasWitness (L : Lang) (V : List Bool → List Bool → Prop) : Prop :=
  ∀ x, L x ↔ ∃ w, V x w

/-- **The small-witness reduction (from IKW)**: every accepting input has a *circuit-described* witness `decode cw`. -/
def SmallWitnessRed (V : List Bool → List Bool → Prop) (decode : List Bool → List Bool) : Prop :=
  ∀ x, (∃ w, V x w) → ∃ cw, V x (decode cw)

/-- **The guess-and-verify decider**: guess a small circuit code `cw`, verify `V x (decode cw)`. -/
def gvDecider (V : List Bool → List Bool → Prop) (decode : List Bool → List Bool) : Lang :=
  fun x => ∃ cw, V x (decode cw)

/-- **The guess-and-verify decider is correct (proved): it decides exactly `L`.**  `gvDecider V decode x ↔ L x`.
Guessing only *small* (circuit-described) witnesses loses nothing: an accepting input has one (`SmallWitnessRed`), and
any small witness is a genuine witness (`HasWitness`). -/
theorem gvDecider_eq (L : Lang) (V : List Bool → List Bool → Prop) (decode : List Bool → List Bool)
    (hw : HasWitness L V) (hs : SmallWitnessRed V decode) (x : List Bool) :
    gvDecider V decode x ↔ L x := by
  rw [hw x]
  constructor
  · rintro ⟨cw, hcw⟩
    exact ⟨decode cw, hcw⟩
  · intro h
    exact hs x h

/-- **Guess-and-verify gives the collapse (proved glue): `NTIME2n ⊆ NTIME2nFast`.**  If every `L ∈ NTIME2n` has a
verifier `V` and decoder `decode` with the small-witness reduction *and* whose guess-and-verify decider lies in
`NTIME2nFast`, then `NTIME2n ⊆ NTIME2nFast`: the decider equals `L` (`gvDecider_eq`), so `L` inherits its complexity. -/
theorem guessVerify_subset (NTIME2n NTIME2nFast : CClass)
    (toVerifier : ∀ L ∈ NTIME2n, ∃ (V : List Bool → List Bool → Prop) (decode : List Bool → List Bool),
        HasWitness L V ∧ SmallWitnessRed V decode ∧ gvDecider V decode ∈ NTIME2nFast) :
    NTIME2n ⊆ NTIME2nFast := by
  intro L hL
  obtain ⟨V, decode, hw, hs, hmem⟩ := toVerifier L hL
  have hEq : gvDecider V decode = L :=
    funext (fun x => propext (gvDecider_eq L V decode hw hs x))
  rwa [hEq] at hmem

end PallLean.Paper93.DeepMath.PathB.ACC0GuessVerify

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessVerify.gvDecider_eq
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0GuessVerify.guessVerify_subset
