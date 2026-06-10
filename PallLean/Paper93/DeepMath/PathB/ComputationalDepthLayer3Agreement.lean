import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRung4CircuitReal
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pApprox

/-!
# Layer 3 — recursive agreement lift (OR/NOT/leaf fragment)

The per-gate agreement steps (`genOrApprox_eval_orOfChildren`, `one_sub_boolToZMod`) are lifted through
the circuit recursion here.  We build a **faithful** OR/NOT/leaf approximant `toAgree` (single-function,
`termination_by sizeOf`, so children are indexed cleanly by `Fin cs.length`), a per-input **goodness**
predicate `AgreeGood` (at each `∨` gate: when the gate is true, some sampled form over the children's
true values is nonzero), and prove by structural induction:
\[
  \text{AgreeGood } x\,R\,C \;\Longrightarrow\;
  \operatorname{eval}_x(\texttt{toAgree}\,C) = \texttt{boolToZMod}\,(C.\operatorname{eval} x).
\]
i.e. the circuit approximant computes the circuit exactly on every *good* input.  `AND`/`MOD` gates are
excluded from this fragment (`AgreeGood` is `False` there); handling them (De Morgan / Fermat) and the
probabilistic "most inputs are good" step are the remaining pieces.  No lower bound; far below P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer3

open MvPolynomial

variable {n : ℕ}

/-- Faithful OR/NOT/leaf circuit approximant: `∨` → `genOrApprox` over children, `¬` → `1 - child`,
leaves → `X i`/`C b`; `AND`/`MOD` are placeholders (excluded by `AgreeGood`). -/
noncomputable def toAgree (p t : ℕ) (R : (k : ℕ) → Fin t → Fin k → ZMod p) :
    BoolCircuitSyntax n → MvPolynomial (Fin n) (ZMod p)
  | .const b => C (boolToZMod p b)
  | .input i => X i
  | .not c => 1 - toAgree p t R c
  | .orGate cs => genOrApprox p (R cs.length) (fun j => toAgree p t R (cs.get j))
  | .andGate _ => 0
  | .modGate _ _ _ => 0
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact lt_of_lt_of_le (List.sizeOf_lt_of_mem (List.getElem_mem _)) (by omega)

/-- Per-input goodness: children good, and at each `∨` gate, when the gate evaluates to `true` some
sampled form over the children's *true* values is nonzero (so the OR approximant fires correctly). -/
def AgreeGood (p t : ℕ) (R : (k : ℕ) → Fin t → Fin k → ZMod p) (x : Fin n → Bool) :
    BoolCircuitSyntax n → Prop
  | .const _ => True
  | .input _ => True
  | .not c => AgreeGood p t R x c
  | .orGate cs => (∀ j : Fin cs.length, AgreeGood p t R x (cs.get j)) ∧
      ((∃ j : Fin cs.length, (cs.get j).eval x = true) →
        ∃ s, ∑ j, R cs.length s j * boolToZMod p ((cs.get j).eval x) ≠ 0)
  | .andGate _ => False
  | .modGate _ _ _ => False
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact lt_of_lt_of_le (List.sizeOf_lt_of_mem (List.getElem_mem _)) (by omega)

/-- **OR-gate evaluation ↔ some child true** (`.any` ↔ indexed existential). -/
theorem orGate_eval_iff (cs : List (BoolCircuitSyntax n)) (x : Fin n → Bool) :
    (BoolCircuitSyntax.orGate cs).eval x = true ↔ ∃ j : Fin cs.length, (cs.get j).eval x = true := by
  simp only [BoolCircuitSyntax.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨b, ⟨c, hc, rfl⟩, hb⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hc
    exact ⟨j, by rw [hj]; exact hb⟩
  · rintro ⟨j, hj⟩
    exact ⟨(cs.get j).eval x, ⟨cs.get j, List.get_mem cs j, rfl⟩, hj⟩

/-- **The recursive agreement lift.**  On any *good* input, the OR/NOT/leaf circuit approximant
evaluates to the true circuit value. -/
theorem toAgree_eval (p t : ℕ) [Fact p.Prime] (R : (k : ℕ) → Fin t → Fin k → ZMod p)
    (x : Fin n → Bool) :
    ∀ (C : BoolCircuitSyntax n), AgreeGood p t R x C →
      eval (fun i => boolToZMod p (x i)) (toAgree p t R C) = boolToZMod p (C.eval x)
  | .const b, _ => by simp [toAgree, BoolCircuitSyntax.eval]
  | .input i, _ => by simp [toAgree, BoolCircuitSyntax.eval]
  | .not c, hg => by
      simp only [AgreeGood] at hg
      simp only [toAgree, map_sub, map_one]
      rw [toAgree_eval p t R x c hg, one_sub_boolToZMod]
      simp only [BoolCircuitSyntax.eval]
  | .orGate cs, hg => by
      simp only [AgreeGood] at hg
      obtain ⟨hchildren, hgood⟩ := hg
      simp only [toAgree]
      rw [genOrApprox_eval_orOfChildren p (R cs.length) (fun j => toAgree p t R (cs.get j))
        (fun i => boolToZMod p (x i)) (fun j => (cs.get j).eval x)
        (fun j => toAgree_eval p t R x (cs.get j) (hchildren j)) hgood]
      by_cases hev : (BoolCircuitSyntax.orGate cs).eval x = true
      · rw [if_pos ((orGate_eval_iff cs x).mp hev), hev]
        exact (boolToZMod_true p).symm
      · have hne : ¬ ∃ j : Fin cs.length, (cs.get j).eval x = true :=
          fun h => hev ((orGate_eval_iff cs x).mpr h)
        rw [Bool.not_eq_true] at hev
        rw [if_neg hne, hev]
        exact (boolToZMod_false p).symm
  | .andGate _, hg => by simp only [AgreeGood] at hg
  | .modGate _ _ _, hg => by simp only [AgreeGood] at hg
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | exact lt_of_lt_of_le (List.sizeOf_lt_of_mem (List.getElem_mem _)) (by omega)

end PallLean.Paper93.DeepMath.PathB.Layer3

#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toAgree
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.AgreeGood
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.orGate_eval_iff
#print axioms PallLean.Paper93.DeepMath.PathB.Layer3.toAgree_eval
