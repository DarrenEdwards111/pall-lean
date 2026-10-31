import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedInfoCap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBranchingProgramWidth

/-!
# Step (4), items 4–5: the `Prog → LevBP` bridge and the CONDITIONAL `hardF` wire bound

A charged program on `w` wires with its fixed gate list is an **oblivious** computation: the input-read schedule
is part of the program description.  `toBP` realizes it as an oblivious leveled branching program of width `2^w`
(one level per gate; states = wire assignments; logic gates read a dummy variable and ignore the bit), with
`toBP_eval : (toBP dummy P).eval = P.run` and `len = cost`.

`hardF_prog_width_conditional` — **the conditional wire bound** (audit-corrected statement): any charged program
computing `hardF` **whose read schedule reads the chosen address block in one contiguous gate interval** (and
nowhere else, with logic levels labeled by a dummy off-block variable) needs `2^b − 1 ≤ 2·2^w`, i.e.
`w ≥ b − O(1)` wires.

**The unconditional version is FALSE** and is not claimed: `hardF` is computable with `O(1)` wires by re-reading
(compare each address against each hardwired cell on the fly), exactly as `qfProg A` (3 wires, quadratically many
re-reads) warns — static ordering bounds do not transfer to repeated-read programs.  The contiguous-schedule
hypothesis is load-bearing and is stated explicitly.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ProgBPBridge

open PallLean.Paper93.DeepMath.PathB.ChargedGate
open PallLean.Paper93.DeepMath.PathB.ChargedCircuit
open PallLean.Paper93.DeepMath.PathB.BranchingProgram
open PallLean.Paper93.DeepMath.PathB.NecHard

variable {n w : ℕ}

/-- Wire states as BP states. -/
noncomputable def E (w : ℕ) : (Fin w → Bool) ≃ Fin (2 ^ w) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin])

/-- The variable read at gate `ℓ` (a dummy for logic gates / out of range). -/
def gateVar (dummy : Fin n) (gs : List (Gate n w)) (ℓ : ℕ) : Fin n :=
  ((gs[ℓ]?).bind Gate.readsInput).getD dummy

/-- The bit-parametric step (an input gate takes the read bit; logic gates ignore it). -/
def stepB (s : Fin w → Bool) (b : Bool) : Gate n w → (Fin w → Bool)
  | .input _ t => Function.update s t b
  | .notg a t => Function.update s t (! s a)
  | .andg a b' t => Function.update s t (s a && s b')
  | .xorg a b' t => Function.update s t (xor (s a) (s b'))

/-- Feeding a gate the bit of its own read variable is the ordinary step. -/
theorem stepB_read (y : Fin n → Bool) (s : Fin w → Bool) (d : Fin n) (g : Gate n w) :
    stepB s (y ((Gate.readsInput g).getD d)) g = step y s g := by
  cases g <;> rfl

/-- **The bridge**: a charged program on `w` wires as an oblivious leveled BP of width `2^w`. -/
noncomputable def toBP (dummy : Fin n) (P : Prog n w) : LevBP n (2 ^ w) where
  len := P.gates.length
  var := gateVar dummy P.gates
  δ := fun ℓ st b =>
    match P.gates[ℓ]? with
    | none => st
    | some g => E w (stepB ((E w).symm st) b g)
  start := E w (fun _ => false)
  accept := fun st => (E w).symm st P.out

theorem toBP_δ_some (dummy : Fin n) (P : Prog n w) {ℓ : ℕ} (h : ℓ < P.gates.length)
    (st : Fin (2 ^ w)) (b : Bool) :
    (toBP dummy P).δ ℓ st b = E w (stepB ((E w).symm st) b (P.gates[ℓ])) := by
  show (match P.gates[ℓ]? with
    | none => st
    | some g => E w (stepB ((E w).symm st) b g)) = _
  rw [List.getElem?_eq_getElem h]

theorem toBP_δ_none (dummy : Fin n) (P : Prog n w) {ℓ : ℕ} (h : P.gates.length ≤ ℓ)
    (st : Fin (2 ^ w)) (b : Bool) : (toBP dummy P).δ ℓ st b = st := by
  show (match P.gates[ℓ]? with
    | none => st
    | some g => E w (stepB ((E w).symm st) b g)) = _
  rw [List.getElem?_eq_none h]

/-- The BP state after `ℓ` levels is the wire state after `ℓ` gates. -/
theorem toBP_runUpto (dummy : Fin n) (P : Prog n w) (y : Fin n → Bool) (ℓ : ℕ) :
    (toBP dummy P).runUpto y ℓ = E w (runGates y (P.gates.take ℓ) (fun _ => false)) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    show (toBP dummy P).δ ℓ ((toBP dummy P).runUpto y ℓ) (y ((toBP dummy P).var ℓ)) = _
    rw [ih]
    by_cases hℓ : ℓ < P.gates.length
    · have hvar : (toBP dummy P).var ℓ = (Gate.readsInput (P.gates[ℓ])).getD dummy := by
        show gateVar dummy P.gates ℓ = _
        rw [gateVar, List.getElem?_eq_getElem hℓ]
        rfl
      have htake : P.gates.take (ℓ + 1) = P.gates.take ℓ ++ [P.gates[ℓ]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hℓ]
        rfl
      rw [toBP_δ_some dummy P hℓ, Equiv.symm_apply_apply, hvar, stepB_read, htake,
        runGates_append']
      rfl
    · rw [toBP_δ_none dummy P (by omega),
        List.take_of_length_le (show P.gates.length ≤ ℓ by omega),
        List.take_of_length_le (show P.gates.length ≤ ℓ + 1 by omega)]

/-- **Semantic correspondence**: the BP computes exactly the program's function. -/
theorem toBP_eval (dummy : Fin n) (P : Prog n w) (y : Fin n → Bool) :
    (toBP dummy P).eval y = P.run y := by
  show ((E w).symm ((toBP dummy P).runUpto y P.gates.length)) P.out = P.run y
  rw [toBP_runUpto, Equiv.symm_apply_apply, List.take_length]
  rfl

/-- **The CONDITIONAL `hardF` wire bound.**  Any charged program computing `hardF` whose read schedule reads the
address block `blockS k` exactly in the contiguous gate interval `[a, a+s)` (logic levels labeled by `dummy`)
needs `2^b − 1 ≤ 2·2^w`.  The unconditional version is FALSE (`hardF` has `O(1)`-wire re-reading programs);
the schedule hypothesis is load-bearing. -/
theorem hardF_prog_width_conditional {b m w : ℕ} (k : Fin m) (P : Prog (nn b m) w)
    (hP : ∀ x, P.run x = hardF x) (dummy : Fin (nn b m)) (a s : ℕ) (has : a + s ≤ P.cost)
    (hsched : ∀ ℓ, ℓ < P.cost →
      (gateVar dummy P.gates ℓ ∈ blockS k ↔ a ≤ ℓ ∧ ℓ < a + s)) :
    Dsize b - 1 ≤ 2 * 2 ^ w :=
  hardF_bp_width_ge k (toBP dummy P) (fun x => by rw [toBP_eval, hP]) a s has hsched

end PallLean.Paper93.DeepMath.PathB.ProgBPBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ProgBPBridge.toBP_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ProgBPBridge.hardF_prog_width_conditional
