import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PinSize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0Layer4Discharge

/-!
# Bridge (final assembly) — `MOD_q ∉ AC⁰[p]` from a uniform residue-`0` family (proved)

The final wiring of the Layer4 route.  Assembling the model translation, the Layer4 family bound, the residue-family
construction (`pinTrue`), the size bound through `pinTrue`, and depth preservation, we obtain: **if `MOD_q` (the residue-`0`
indicator `[weight ≡ 0 mod q]`) is computed by a uniform family of `AC⁰[p]` circuits — one at every arity, with bounded
depth and subcircuit-list size — then `False`** (for `q ∤ p`, `p,q` prime, in the Razborov–Smolensky window).

Each residue indicator `[weight ≡ j mod q]` at the fixed arity `2m+1` is realised as `pinTrue (D ((2m+1)+(q−j)))`: padding the
residue-`0` circuit at arity `(2m+1)+(q−j)` with `q−j` true bits shifts its residue to `j` (`pinTrue_residue_shift` +
`mod_shift`).  `pinTrue` preserves `AC⁰[p]`, does not grow depth (`pinTrue_tbs_depth_le`) or subcircuit count
(`pinTrue_card_le`), so the uniform bounds on `D` transfer to the whole family, which then contradicts
`modq_indicators_false_acc0`.

## What is proved (clean axioms, no `sorry`)

* **`mod_shift`** (PROVED) — `j < q → ((w + (q−j)) % q = 0 ↔ w % q = j)`.
* **`tbs_depth_eq`** / **`pinTrue_tbs_depth_le`** (PROVED) — `BoolCircuitSyntax`-depth equals `ACC0`-depth under
  `toBoolSyntax`, and is non-increasing under `pinTrue`.
* **`modq_not_acc0p_uniform`** (PROVED) — no uniform `AC⁰[p]` family computes `MOD_q` within the RS window.

## Honest scope

This closes the Layer4 route to `MOD_q ∉ AC⁰[p]`: the hypothesis is a *uniform residue-`0` family* with a depth bound and a
*subcircuit-list size* bound `4q·(subcircuits (toBoolSyntax (D N))).length ≤ p^t`, in the RS window `16((p−1)t)^d)² < 2m+3`.
This is the standard Razborov–Smolensky resource regime (constant depth, the polynomial-method window).  The **Williams
cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains **open** / not faked.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModqUniform

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax (toBoolSyntax)
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueFamily
  (pinTrue pinTrue_modpOnly pinTrue_depth pinTrue_residue_shift)
open PallLean.Paper93.DeepMath.PathB.ACC0PinSize (pinTrue_card_le)
open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)

variable {n k : ℕ}

/-- **Residue arithmetic: padding by `q−j` shifts residue `0` to `j` (PROVED).** -/
theorem mod_shift {q : ℕ} (w j : ℕ) (hjq : j < q) :
    ((w + (q - j)) % q = 0) ↔ (w % q = j) := by
  haveI : NeZero q := ⟨by omega⟩
  have hR : ((w : ZMod q) = (j : ZMod q)) ↔ (w % q = j) := by
    rw [ZMod.natCast_eq_natCast_iff]
    show (w ≡ j [MOD q]) ↔ (w % q = j)
    unfold Nat.ModEq; rw [Nat.mod_eq_of_lt hjq]
  rw [← Nat.dvd_iff_mod_eq_zero, ← ZMod.natCast_eq_zero_iff, ← hR,
    Nat.cast_add, Nat.cast_sub (le_of_lt hjq), ZMod.natCast_self, zero_sub, ← sub_eq_add_neg,
    sub_eq_zero]

/-- Folding the depth-max over a list of input gates leaves the accumulator unchanged. -/
theorem foldl_depth_map_input {m : ℕ} (l : List (Fin m)) (acc : ℕ) :
    (l.map (fun i => (BoolCircuitSyntax.input i : BoolCircuitSyntax m))).foldl
        (fun a C => max a (BoolCircuitSyntax.depth C)) acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.foldl_cons, BoolCircuitSyntax.depth, Nat.max_zero]
      exact ih acc

/-- **`toBoolSyntax` preserves depth (PROVED).** -/
theorem tbs_depth_eq (C : ACC0Circuit n) :
    BoolCircuitSyntax.depth (toBoolSyntax C) = ACC0CircuitModel.depth C := by
  induction C with
  | const b => simp [toBoolSyntax, ACC0CircuitModel.depth]
  | var i => simp [toBoolSyntax, ACC0CircuitModel.depth]
  | not c ih => simp only [toBoolSyntax, BoolCircuitSyntax.depth, ACC0CircuitModel.depth, ih]; omega
  | and a b iha ihb =>
      simp only [toBoolSyntax, BoolCircuitSyntax.depth, ACC0CircuitModel.depth, List.foldl_cons,
        List.foldl_nil]
      rw [iha, ihb]; omega
  | or a b iha ihb =>
      simp only [toBoolSyntax, BoolCircuitSyntax.depth, ACC0CircuitModel.depth, List.foldl_cons,
        List.foldl_nil]
      rw [iha, ihb]; omega
  | mod q S t =>
      simp only [toBoolSyntax, BoolCircuitSyntax.depth, ACC0CircuitModel.depth]
      rw [foldl_depth_map_input]

/-- **`pinTrue` does not increase `BoolCircuitSyntax` depth (PROVED).** -/
theorem pinTrue_tbs_depth_le (C : ACC0Circuit (n + k)) :
    BoolCircuitSyntax.depth (toBoolSyntax (pinTrue C)) ≤ BoolCircuitSyntax.depth (toBoolSyntax C) := by
  rw [tbs_depth_eq, tbs_depth_eq]; exact pinTrue_depth C

open Classical in
/-- **`MOD_q ∉ AC⁰[p]`: no uniform `AC⁰[p]` family computes `MOD_q` in the RS window (PROVED).** -/
theorem modq_not_acc0p_uniform (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {m t d : ℕ} (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t)
    (hwindow : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3)
    (D : (N : ℕ) → ACC0Circuit N)
    (hDind : ∀ N, ∀ y : Fin N → Bool,
      ACC0CircuitModel.eval (D N) y = decide ((Finset.univ.filter (fun i => y i = true)).card % q = 0))
    (hDmod : ∀ N, ModpOnly p (D N))
    (hDdepth : ∀ N, BoolCircuitSyntax.depth (toBoolSyntax (D N)) ≤ d)
    (hDsize : ∀ N, 4 * q * (subcircuits (toBoolSyntax (D N))).length ≤ p ^ t) : False := by
  refine ACC0Layer4Discharge.modq_indicators_false_acc0 p q hpq ht1 hpt1
    (fun j => pinTrue (D ((2 * m + 1) + (q - j)))) ?_ ?_ ?_ ?_ hwindow
  · intro j _; exact pinTrue_modpOnly p _ (hDmod _)
  · intro j hj x
    rw [pinTrue_residue_shift q (D ((2 * m + 1) + (q - j))) x (hDind _)]
    exact decide_eq_decide.mpr (mod_shift _ j (Finset.mem_range.mp hj))
  · intro j _
    calc 4 * q * (subcircuits (toBoolSyntax (pinTrue (D ((2 * m + 1) + (q - j)))))).toFinset.card
        ≤ 4 * q * (subcircuits (toBoolSyntax (D ((2 * m + 1) + (q - j))))).length := by
          gcongr; exact pinTrue_card_le _
      _ ≤ p ^ t := hDsize _
  · intro j _; exact le_trans (pinTrue_tbs_depth_le _) (hDdepth _)

/-!
**The Layer4 route to `MOD_q ∉ AC⁰[p]`, assembled.**  No uniform `AC⁰[p]` family computes `MOD_q` within the
Razborov–Smolensky window — built end to end from the model translation, the Layer4 family bound, the residue-family
construction (`pinTrue`), the size bound through `pinTrue`, and depth preservation.  Remaining (open, not faked): the Williams
cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModqUniform

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqUniform.modq_not_acc0p_uniform
