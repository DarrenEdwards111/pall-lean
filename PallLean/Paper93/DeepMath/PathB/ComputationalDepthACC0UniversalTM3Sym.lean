import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMKeyMatchNe

/-!
# Entry 383 — universal-TM-table build: the 3-symbol (marker) tape model (proved)

The rule-table scan-and-match loop must compare the configuration's key against *each* rule's key, and successive rules
sit at *varying* distance on the tape — which the fixed-gap, 2-symbol (`Bool`) machines of entries 344–382 cannot do
(one machine hardcodes a single gap; a `Bool` tape has no spare *marker* symbol to cross off compared cells).  The
standard fix is a richer alphabet.  This brick founds a **3-symbol tape model** — symbols `O`/`I`/`M` (blank/one/marker)
— reusing the generic `NTM`/`reachIn` layer (entry NTM), with the same machine shape as the `Bool` model
(`ACC0ConcreteNTM`).  The marker `M` will let a comparison cross off cells and shuttle between two regions at arbitrary
distance.

## What is proved (clean axioms, no `sorry`)

* **`Sym3`** (`O`/`I`/`M`), **`CConfig3`**, **`TMTrans3`**, **`TMachine3`**, **`readSym3`**, **`writeAt3`**,
  **`applyTrans3`**, **`concreteStep3`**, **`toNTM3`** — the 3-symbol concrete machine model.
* **`writeAt3_getD`** (PROVED) — `(writeAt3 tape p w).getD q O = if q = p then w else tape.getD q O`.
* **`writeAt3_id_of_lt`** (PROVED) — `p < tape.length → writeAt3 tape p (tape.getD p O) = tape` (in-bounds write-back is
  the list identity, the foundation for list-preserving 3-symbol scans).

## Honest scope

This **founds the 3-symbol model** for the marker-based varying-distance comparison the rule-loop needs.  It does
**not** yet build any marker comparison, nor the rule-table loop, nor the apply.  Building those fragment by fragment is
the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (Move moveHead)
open PallLean.Paper93.DeepMath.PathB.ACC0NTM (NTM reachIn)

/-- **The 3-symbol tape alphabet**: `O` (blank/zero), `I` (one), `M` (marker). -/
inductive Sym3 | O | I | M
  deriving DecidableEq, Repr

/-- A 3-symbol configuration: `(state, head, tape)`. -/
abbrev CConfig3 := ℕ × ℕ × List Sym3

/-- A 3-symbol transition rule: `((state, read), (state, write, move))`. -/
abbrev TMTrans3 := (ℕ × Sym3) × (ℕ × Sym3 × Move)

/-- A 3-symbol machine: a list of transition rules. -/
abbrev TMachine3 := List TMTrans3

/-- Read the symbol under the head (default `O` past the tape end). -/
def readSym3 (c : CConfig3) : Sym3 := c.2.2.getD c.2.1 Sym3.O

/-- Write symbol `w` at position `p`, extending with `O` if needed. -/
def writeAt3 (tape : List Sym3) (p : ℕ) (w : Sym3) : List Sym3 :=
  (tape ++ List.replicate (p + 1 - tape.length) Sym3.O).set p w

/-- Apply a transition rule to a configuration. -/
def applyTrans3 (c : CConfig3) (t : TMTrans3) : CConfig3 :=
  (t.2.1, moveHead c.2.1 t.2.2.2, writeAt3 c.2.2 c.2.1 t.2.2.1)

/-- The 3-symbol step relation: some rule whose left side matches `(state, read)` fires. -/
def concreteStep3 (M : TMachine3) (c d : CConfig3) : Prop :=
  ∃ t ∈ M, t.1 = (c.1, readSym3 c) ∧ d = applyTrans3 c t

/-- The 3-symbol machine as an abstract `NTM`: start state `0`, head `0`, tape = input (mapped `true ↦ I`, `false ↦
O`); accept iff state `1`. -/
def toNTM3 (M : TMachine3) : NTM where
  Config := CConfig3
  step := concreteStep3 M
  init := fun x => (0, 0, x.map (fun b => if b then Sym3.I else Sym3.O))
  accept := fun c => c.1 = 1

@[simp] theorem toNTM3_step (M : TMachine3) (c d : CConfig3) :
    (toNTM3 M).step c d ↔ concreteStep3 M c d := Iff.rfl

/-- **A write changes only the written cell (PROVED).** -/
theorem writeAt3_getD (tape : List Sym3) (p q : ℕ) (w : Sym3) :
    (writeAt3 tape p w).getD q Sym3.O = if q = p then w else tape.getD q Sym3.O := by
  unfold writeAt3
  rcases eq_or_ne q p with rfl | hne
  · have hlen : q < (tape ++ List.replicate (q + 1 - tape.length) Sym3.O).length := by
      simp only [List.length_append, List.length_replicate]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hlen, if_pos rfl, Option.getD_some]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm, if_neg hne,
        ← List.getD_eq_getElem?_getD]
    rcases lt_or_ge q tape.length with hlt | hge
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge,
          List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hge]
      simp only [List.getElem?_replicate, Option.getD_none]
      split <;> rfl

/-- **A write-back within bounds is the identity (PROVED).** -/
theorem writeAt3_id_of_lt (tape : List Sym3) (p : ℕ) (hp : p < tape.length) :
    writeAt3 tape p (tape.getD p Sym3.O) = tape := by
  unfold writeAt3
  rw [show p + 1 - tape.length = 0 from by omega, List.replicate_zero, List.append_nil,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some,
    List.set_getElem_self]

/-!
**The 3-symbol model, founded.**  `Sym3`/`concreteStep3`/`toNTM3` mirror the `Bool` model over a 3-symbol alphabet
(blank/one/marker), with the foundational write lemmas (`writeAt3_getD`, `writeAt3_id_of_lt`) reused intact.  Next:
marker-based varying-distance comparison primitives, then the rule-table scan-and-match loop and the apply — fragment by
verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym.writeAt3_getD
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym.writeAt3_id_of_lt
