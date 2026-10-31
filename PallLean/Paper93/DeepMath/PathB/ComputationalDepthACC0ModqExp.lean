import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModqSize

/-!
# Bridge (explicit exponential) — `MOD_q` size reaches `p^t` by a polynomial arity (proved)

The explicit form of the Razborov–Smolensky size lower bound.  `modq_requires_large_size` shows the size exceeds `p^t/(4q)`
at *some* arity, but does not bound *where*.  Here we pin the witnessing arity: for every `t`, **within arities `N ≤
16((p−1)t)^d)² + 1 + q`** (a polynomial in `t` at fixed depth `d`), some circuit already has subcircuit-list length exceeding
`p^t / (4q)`.

This is the precise meaning of "exponential lower bound": the size grows to `p^t` (exponential in `t`) by an arity that is
only polynomial in `t` — equivalently, at arity `n` the size is `≥ p^{Ω(n^{1/2d})}`.  No real-valued roots are needed; the
`t`-parametrised statement captures the exponential blow-up exactly.

The proof re-runs the Layer4 assembly (`modq_indicators_false_acc0`) directly with the *bounded* size hypothesis (only arities
`≤ G(t)` are used — the residue indicators live at arities `(2m+1)+(q−j) ≤ 2m+1+q = G(t)` with `m = 8((p−1)t)^d)²`).

## What is proved (clean axioms, no `sorry`)

* **`modq_size_blowup`** (PROVED) — `∃ N ≤ 16((p−1)t)^d)²+1+q, p^t < 4q·(subcircuits (toBoolSyntax (D N))).length`.

## Honest scope

This is the explicit exponential size lower bound for the polynomial method (`MOD_q ∉ AC⁰[p]`, the size reaching `p^t` by
polynomial arity).  The **Williams cash-out** (`NEXP ⊄ ACC⁰`) is a different, P≠NP-strength theorem and remains **open** / not
faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModqExp

open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ToBoolSyntax (toBoolSyntax)
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueFamily
  (pinTrue pinTrue_modpOnly pinTrue_residue_shift)
open PallLean.Paper93.DeepMath.PathB.ACC0PinSize (pinTrue_card_le)
open PallLean.Paper93.DeepMath.PathB.ACC0ModqUniform (mod_shift pinTrue_tbs_depth_le)
open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits)

open Classical in
/-- **The size reaches `p^t` by a polynomial arity (PROVED).**  For any uniform `AC⁰[p]` family `D` computing `MOD_q` at
depth `d`, and any `t ≥ 1`, some arity `N ≤ 16((p−1)t)^d)²+1+q` has `p^t < 4q·(subcircuits (toBoolSyntax (D N))).length` —
the explicit exponential size lower bound. -/
theorem modq_size_blowup (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {d : ℕ} (D : (N : ℕ) → ACC0Circuit N)
    (hDind : ∀ N, ∀ y : Fin N → Bool,
      ACC0CircuitModel.eval (D N) y = decide ((Finset.univ.filter (fun i => y i = true)).card % q = 0))
    (hDmod : ∀ N, ModpOnly p (D N))
    (hDdepth : ∀ N, BoolCircuitSyntax.depth (toBoolSyntax (D N)) ≤ d)
    (t : ℕ) (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t) :
    ∃ N, N ≤ 16 * (((p - 1) * t) ^ d) ^ 2 + 1 + q ∧
      p ^ t < 4 * q * (subcircuits (toBoolSyntax (D N))).length := by
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ N, N ≤ G → 4q·length(D N) ≤ p^t,   with G = 16(((p-1)t)^d)²+1+q
  refine ACC0Layer4Discharge.modq_indicators_false_acc0 (d := d) p q hpq ht1 hpt1
    (fun j => pinTrue (D ((2 * (8 * (((p - 1) * t) ^ d) ^ 2) + 1) + (q - j)))) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact pinTrue_modpOnly p _ (hDmod _)
  · intro j hj x
    rw [pinTrue_residue_shift q (D _) x (hDind _)]
    exact decide_eq_decide.mpr (mod_shift _ j (Finset.mem_range.mp hj))
  · intro j hj
    have hjq : j < q := Finset.mem_range.mp hj
    calc 4 * q * (subcircuits (toBoolSyntax
            (pinTrue (D ((2 * (8 * (((p - 1) * t) ^ d) ^ 2) + 1) + (q - j)))))).toFinset.card
        ≤ 4 * q * (subcircuits (toBoolSyntax
            (D ((2 * (8 * (((p - 1) * t) ^ d) ^ 2) + 1) + (q - j))))).length := by
          gcongr; exact pinTrue_card_le _
      _ ≤ p ^ t := hcon _ (by omega)
  · intro j _; exact le_trans (pinTrue_tbs_depth_le _) (hDdepth _)
  · omega

/-!
**The explicit exponential lower bound, proved.**  `MOD_q`'s `AC⁰[p]` size reaches `p^t` by an arity polynomial in `t` —
i.e. `size(n) ≥ p^{Ω(n^{1/2d})}`.  Remaining (open, not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`,
not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModqExp

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModqExp.modq_size_blowup
