import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameAC0pInputError

/-!
# The AND and MOD input-level error bounds (RS repair, step 3b)

Completes the per-gate analytic content begun in `NFrameAC0pInputError` (which did OR):

* **AND** — dual to OR by De Morgan (`AND b = ¬ OR (¬b)`).  The amplified AND readout is
  `andReadout W b := !(orReadout W (¬b))`, and its error set on any children family `v` equals the OR error set
  on the complemented family, so `and_input_error_bound` follows directly from `or_input_error_bound`.

* **MOD_p** — *exact*, no seed and no error.  `modReadout b := decide (Σⱼ bⱼ = 0)` over `F_p` equals the true
  `MOD_p` gate on Boolean inputs (`modReadout_eq`, Fermat/`Finset.sum_boole`), so the MOD gate contributes zero
  local error.

## Honest scope

The AND and MOD input-level bounds; together with `or_input_error_bound` this covers all `AC⁰[p]` gate types.
Still to do: the `List`↔`Fin` wiring that plugs these into the approximator's `loc` to make `hAnd/hOr/hMod`
literal theorems.  No ACC⁰ lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameAC0pANDMOD

open Finset
open PallLean.Paper93.DeepMath.PathB.NFrameFpDegree
open PallLean.Paper93.DeepMath.PathB.NFrameFpANDOR
open PallLean.Paper93.DeepMath.PathB.NFrameAC0pInputError

section
variable (p : Nat) [Fact p.Prime]

/-! ## AND -/

/-- Pointwise complement. -/
def complBool {k : Nat} (b : Fin k → Bool) : Fin k → Bool := fun j => !(b j)

/-- The amplified AND readout: `AND = ¬ OR(¬)`. -/
def andReadout {k t : Nat} (W : Fin t → (Fin k → ZMod p)) (b : Fin k → Bool) : Bool :=
  !(orReadout p W (complBool b))

/-- `AND b = ¬ OR(¬b)`. -/
theorem ANDb_eq_not_ORb_compl {k : Nat} (b : Fin k → Bool) : ANDb b = !(ORb (complBool b)) := by
  rw [ANDb, ORb, ← decide_not, decide_eq_decide, not_exists]
  refine forall_congr' (fun j => ?_)
  simp only [complBool]
  cases b j <;> simp

/-- The AND readout errs exactly where the OR readout errs on the complement. -/
theorem andReadout_err {k t : Nat} (W : Fin t → (Fin k → ZMod p)) (b : Fin k → Bool) :
    (andReadout p W b ≠ ANDb b) ↔ (orReadout p W (complBool b) ≠ ORb (complBool b)) := by
  rw [andReadout, ANDb_eq_not_ORb_compl]
  cases orReadout p W (complBool b) <;> cases ORb (complBool b) <;> simp

/-- **Input-level error bound for AND.**  There is a seed whose amplified AND readout errs on at most `2^n / p^t`
inputs. -/
theorem and_input_error_bound {n k t : Nat} (ht : 0 < t) (v : (Fin n → Bool) → (Fin k → Bool)) :
    ∃ W : Fin t → (Fin k → ZMod p),
      p ^ t * (univ.filter (fun x : Fin n → Bool => andReadout p W (v x) ≠ ANDb (v x))).card ≤ 2 ^ n := by
  obtain ⟨W, hW⟩ := or_input_error_bound p ht (fun x => complBool (v x))
  refine ⟨W, ?_⟩
  have hset : (univ.filter (fun x : Fin n → Bool => andReadout p W (v x) ≠ ANDb (v x)))
      = (univ.filter (fun x : Fin n → Bool => orReadout p W (complBool (v x)) ≠ ORb (complBool (v x)))) := by
    apply Finset.filter_congr; intro x _; rw [andReadout_err]
  rw [hset]; exact hW

/-! ## MOD_p (exact) -/

/-- The `MOD_p` readout over `F_p`: fires iff the `F_p`-sum of the inputs is `0`. -/
def modReadout {k : Nat} (b : Fin k → Bool) : Bool := decide ((∑ j, boolToZMod p (b j)) = 0)

/-- **`MOD_p` is exact.**  The readout equals the true `MOD_p` gate (`#trues ≡ 0 mod p`) on Boolean inputs — no
seed, no error. -/
theorem modReadout_eq {k : Nat} (b : Fin k → Bool) :
    modReadout p b = decide ((univ.filter (fun j => b j)).card % p = 0) := by
  haveI : NeZero p := ⟨Nat.Prime.ne_zero Fact.out⟩
  have hsum : (∑ j, boolToZMod p (b j)) = ((univ.filter (fun j => b j)).card : ZMod p) := by
    simp only [boolToZMod]
    rw [Finset.sum_boole]
  rw [modReadout, hsum]
  refine decide_eq_decide.mpr ?_
  rw [ZMod.natCast_eq_zero_iff]
  exact Nat.dvd_iff_mod_eq_zero

end

end PallLean.Paper93.DeepMath.PathB.NFrameAC0pANDMOD

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pANDMOD.and_input_error_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameAC0pANDMOD.modReadout_eq
