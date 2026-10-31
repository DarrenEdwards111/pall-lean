import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NisanWigdersonHardness
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0IKWEasyWitness

/-!
# NoEasyWitnessHardFn — the easy-witness ↔ hardness identification and the extraction (proved)

Entry 150 left **`NoEasyWitnessHardFn`** (`¬ SmallWitnessCircuits → HardFunction`: if witnesses are *not* small-circuit
describable, a hard function exists) as the deepest-looking Williams ingredient.  This file discharges its genuine
**structural content** — but, as with entry 197, it is essential to be exact about *which* half this is.

**What this socket is: the extraction (the easy half).**  A NEXP witness is a truth-table string `w`; it is "easy" iff a
small circuit *describes* `w`.  In the truth-table representation, the function `w : (Fin n → Bool) → Bool` whose table
is that string is the *same object*, and "a small circuit describes the string `w`" is literally "a small circuit
*computes* the function `w`".  Hence **`¬ EasyWitness w s ↔ HardFor w s`** holds by `rfl`, and the extraction
`¬ EasyWitness w s → ∃ f, HardFor f s` is simply *the witness `w` itself is the hard function* (`fun h => ⟨w, h⟩`).
This identification is the entire structural content of `NoEasyWitnessHardFn`.

**What this socket is NOT: the easy-witness lemma.**  The deep IKW content — that `NEXP ⊆ P/poly` *implies* easy
witnesses (equivalently, that some NEXP language genuinely *lacks* easy witnesses, i.e. `¬ EasyWitness` actually holds) —
is a circuit lower bound of **separation strength** and is *not* discharged here.  This file proves only that *if* a
witness lacks a small circuit *then* it is a hard function; that the hypothesis `¬ EasyWitness` ever holds is the
irreducible assumption (equivalent to the separation).

## What is proved (clean axioms, no `sorry`)

* **`EasyWitness w s := HasCircuitOfSize w s`** — a witness is easy iff its truth-table function has a size-`≤s` circuit
  (describe = compute, in the truth-table representation).
* **`noEasyWitness_iff_hard`** — the identification: `¬ EasyWitness w s ↔ HardFor w s` (`rfl`).
* **`noEasyWitness_extracts_hard`** — the extraction: `¬ EasyWitness w s → ∃ f, HardFor f s`, the witness `w` itself.
* **`noEasyWitnessHardFn_discharge`** — discharges the **entry-150 `NoEasyWitnessHardFn` socket** for the concrete
  predicates over the `Circ` model.

## Honest scope

This proves only the **identification/extraction** content of `NoEasyWitnessHardFn` — that a witness lacking a small
circuit *is* a hard function (describe = compute in the truth-table representation) — concretely over the entry-196/197
`Circ` model.  It does **not** prove the easy-witness lemma, nor that any NEXP language lacks easy witnesses; that the
hypothesis `¬ EasyWitness` holds is the genuine circuit lower bound, of separation strength, and is *not* discharged
here.  Closing this socket isolates the irreducible Williams-side assumption to a single statement — *a NEXP language
without easy witnesses exists* (equivalently, a hard function exists) — exactly the separation.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonEasyWitness

open PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonHardness (HasCircuitOfSize HardFor)
open PallLean.Paper93.DeepMath.PathB.ACC0IKWEasyWitness (NoEasyWitnessHardFn)

/-- **A witness is easy.**  The witness truth-table function `w` is describable — equivalently computable — by a circuit
of size `≤ s`.  (In the truth-table representation, a circuit describing the string `w` and one computing the function
`w` are the same object.) -/
def EasyWitness {n : ℕ} (w : (Fin n → Bool) → Bool) (s : ℕ) : Prop := HasCircuitOfSize w s

/-- **The easy-witness ↔ hardness identification (PROVED).**  A witness has no small circuit iff its truth-table
function is hard — `rfl`, since `EasyWitness w s` *is* `HasCircuitOfSize w s` and `HardFor w s` *is* its negation.  This
is the structural pivot of `NoEasyWitnessHardFn`: "no easy witness" and "the witness is a hard function" are the same
statement. -/
theorem noEasyWitness_iff_hard {n : ℕ} (w : (Fin n → Bool) → Bool) (s : ℕ) :
    ¬ EasyWitness w s ↔ HardFor w s := Iff.rfl

/-- **A hard function exists (against size `s`).** -/
def ExistsHardFunction (n s : ℕ) : Prop := ∃ f : (Fin n → Bool) → Bool, HardFor f s

/-- **The extraction (PROVED).**  If the witness `w` has no small describing circuit, then a hard function exists —
namely `w` itself.  This is the entire content of the contrapositive easy-witness direction: the witness that defeats
small description *is* the hard function. -/
theorem noEasyWitness_extracts_hard {n : ℕ} (w : (Fin n → Bool) → Bool) (s : ℕ)
    (h : ¬ EasyWitness w s) : ExistsHardFunction n s := ⟨w, h⟩

/-- **Discharging the entry-150 `NoEasyWitnessHardFn` socket (PROVED).**  For the concrete predicates over the `Circ`
model, `¬ EasyWitness w s → ExistsHardFunction n s` by `fun h => ⟨w, h⟩` — the witness `w` is the hard function.  This
closes the socket's *structural* content; that the hypothesis `¬ EasyWitness w s` (a NEXP language lacking easy
witnesses) ever holds is the irreducible circuit lower bound, of separation strength, NOT discharged here. -/
theorem noEasyWitnessHardFn_discharge {n : ℕ} (w : (Fin n → Bool) → Bool) (s : ℕ) :
    NoEasyWitnessHardFn (EasyWitness w s) (ExistsHardFunction n s) :=
  fun h => ⟨w, h⟩

end PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonEasyWitness

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonEasyWitness.noEasyWitness_iff_hard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonEasyWitness.noEasyWitness_extracts_hard
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0NisanWigdersonEasyWitness.noEasyWitnessHardFn_discharge
