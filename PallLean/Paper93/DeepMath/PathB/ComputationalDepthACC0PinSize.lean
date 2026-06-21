import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ResidueFamily
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ToBoolSyntax
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Agreement

/-!
# Bridge (size bound through `pinTrue`) — subcircuit count is monotone under input-pinning (proved)

The quantitative step completing the residue-family construction.  Input-pinning (`pinTrue`) only shrinks circuits: it turns
`var` leaves into `const`/`var` leaves and shrinks `mod` supports, never adding structure.  So the subcircuit count of the
translated pinned circuit is bounded by that of the original (`pinTrue_card_le`), which lets a size bound on the residue-`0`
circuit transfer to every pinned residue indicator — exactly what `modq_indicators_false_acc0` consumes.

## What is proved (clean axioms, no `sorry`)

* **`pinTrue_tbs_length_le`** (PROVED) — `(subcircuits (toBoolSyntax (pinTrue C))).length ≤ (subcircuits (toBoolSyntax C)).length`.
* **`pinTrue_card_le`** (PROVED) — `(subcircuits (toBoolSyntax (pinTrue C))).toFinset.card ≤ (subcircuits (toBoolSyntax C)).length`
  — the size bound through `pinTrue`, feeding the `Layer4` discharge's subcircuit-count hypothesis.

## Honest scope

This is the size-monotonicity lemma for `pinTrue`.  Together with the residue shift (`pinTrue_residue_shift`) and the Layer4
discharge (`modq_indicators_false_acc0`), it supplies the size transfer for the single-`MOD_q` reduction; the *final
assembly* (a uniform residue-`0` family across arities `n .. n+q−1`, with the arity/window bookkeeping) is the remaining
wiring.  Williams cash-out still open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PinSize

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueFamily (pinTrue lowSupport)
open PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax (toBoolSyntax)
open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits subcircuitsList)

variable {n k : ℕ}

/-- The subcircuit list of a list of input gates has length equal to the index list. -/
theorem subcircuitsList_map_input_length {m : ℕ} (l : List (Fin m)) :
    (subcircuitsList (l.map (fun i => (BoolCircuitSyntax.input i : BoolCircuitSyntax m)))).length
      = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [subcircuitsList, subcircuits, ih]

/-- **Subcircuit-list length is monotone under input-pinning (PROVED).** -/
theorem pinTrue_tbs_length_le (C : ACC0Circuit (n + k)) :
    (subcircuits (toBoolSyntax (pinTrue C))).length ≤ (subcircuits (toBoolSyntax C)).length := by
  induction C with
  | const b => simp [pinTrue, toBoolSyntax, subcircuits]
  | var i => by_cases h : (i : ℕ) < n <;> simp [pinTrue, toBoolSyntax, subcircuits, h]
  | not c ih => simp only [pinTrue, toBoolSyntax, subcircuits, List.length_cons]; omega
  | and a b iha ihb =>
      simp only [pinTrue, toBoolSyntax, subcircuits, subcircuitsList, List.length_cons,
        List.length_append, List.length_nil]
      omega
  | or a b iha ihb =>
      simp only [pinTrue, toBoolSyntax, subcircuits, subcircuitsList, List.length_cons,
        List.length_append, List.length_nil]
      omega
  | mod q S t =>
      simp only [pinTrue, toBoolSyntax, subcircuits, List.length_cons]
      rw [subcircuitsList_map_input_length, subcircuitsList_map_input_length,
        Finset.length_toList, Finset.length_toList]
      have hcard : (lowSupport S).card ≤ S.card := by
        apply Finset.card_le_card_of_injOn (Fin.castAdd k)
        · intro i hi; simpa [lowSupport, Finset.mem_preimage] using hi
        · exact (Fin.castAdd_injective n k).injOn
      omega

open Classical in
/-- **The size bound through `pinTrue` (PROVED).**  The translated pinned circuit's subcircuit count is bounded by the
original's subcircuit-list length — so a size bound on the residue-`0` circuit transfers to every pinned residue indicator. -/
theorem pinTrue_card_le (C : ACC0Circuit (n + k)) :
    (subcircuits (toBoolSyntax (pinTrue C))).toFinset.card ≤ (subcircuits (toBoolSyntax C)).length :=
  le_trans (List.toFinset_card_le _) (pinTrue_tbs_length_le C)

/-!
**The size bound through `pinTrue`, proved.**  `pinTrue` never grows the subcircuit count, so the residue-`0` size bound
transfers to every pinned residue indicator — the quantitative ingredient of the single-`MOD_q` reduction.  Remaining (open,
not faked): the final uniform-family assembly + arity/window bookkeeping; and the Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PinSize

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PinSize.pinTrue_card_le
