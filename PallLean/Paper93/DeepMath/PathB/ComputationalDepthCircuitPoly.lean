import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthModPoly
import Mathlib

/-!
# Bridging the circuit model to the polynomial representation (PROVED)

The polynomial-method files built `modPoly`, the `𝔽_p`-polynomial of a `MOD_p` gate; the `ACC0` file built the
`Circuit` model.  This file connects them: the `ACC0` circuit consisting of a single `MOD_p` gate over the `n`
input variables is **exactly represented** by `modPoly` on `{0,1}ⁿ`.

  `modCircuit` — the `ACC0` circuit `MOD_p(x₁,…,xₙ)`.
  `modCircuit_eval` — it fires iff the number of true inputs is `≡ 0 (mod p)`.
  `modCircuit_repr` — **the bridge**: `eval (modPoly p n) = [MOD_p circuit fires]` on every Boolean input —
        the circuit gate and its degree-`(p-1)` polynomial agree exactly.

So the circuit model and the polynomial representation are the same object on `MOD_p` gates; the general
`AC⁰`-arithmetisation (every circuit ↦ a polynomial) and the lower bound remain targets / cited axioms.
-/

open MvPolynomial PallLean.Paper93.DeepMath.PathB.SymAnd

namespace PallLean.Paper93.DeepMath.PathB.ACC0

variable {n : ℕ}

/-- The `ACC0` circuit computing `MOD_p` over the `n` input variables. -/
def modCircuit (p n : ℕ) : Circuit n := Circuit.mod p ((List.finRange n).map Circuit.var)

/-- The `MOD_p` circuit fires iff the number of true inputs is `≡ 0 (mod p)`. -/
theorem modCircuit_eval (p n : ℕ) (x : Fin n → Bool) :
    (modCircuit p n).eval x = decide ((List.finRange n).countP (fun i => x i) % p = 0) := by
  rw [modCircuit, Circuit.eval_mod, List.countP_map]
  rfl

set_option linter.unnecessarySeqFocus false in
/-- The number of true inputs, cast into `𝔽_p`, equals the `𝔽_p`-weight `modSum`. -/
theorem countP_cast_eq_modSum (p n : ℕ) [Fact p.Prime] (x : Fin n → Bool) :
    (((List.finRange n).countP (fun i => x i) : ℕ) : ZMod p) = modSum p n x := by
  have key : ∀ l : List (Fin n),
      ((l.countP (fun i => x i) : ℕ) : ZMod p) = (l.map (fun i => ((x i).toNat : ZMod p))).sum := by
    intro l; induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.countP_cons, List.map_cons, List.sum_cons, ← ih]
      cases x a <;> simp <;> ring
  rw [key, modSum, Fin.sum_univ_def]

/-- **The bridge: the `MOD_p` circuit and its polynomial `modPoly` agree on every Boolean input.**  The
degree-`(p-1)` polynomial `1 - (Σ Xᵢ)^(p-1)` evaluated at `x` equals `1` if the `MOD_p` circuit fires there and
`0` otherwise — the circuit model and the polynomial-method representation are the same object on `MOD_p`. -/
theorem modCircuit_repr (p n : ℕ) [Fact p.Prime] (x : Fin n → Bool) :
    eval (fun i => ((x i).toNat : ZMod p)) (modPoly p n) = if (modCircuit p n).eval x then 1 else 0 := by
  rw [modPoly_eval, modCircuit_eval]
  have hequiv : (modSum p n x = 0)
      ↔ ((List.finRange n).countP (fun i => x i) % p = 0) := by
    rw [← countP_cast_eq_modSum, CharP.cast_eq_zero_iff (ZMod p) p, Nat.dvd_iff_mod_eq_zero]
  simp only [hequiv]
  by_cases hc : (List.finRange n).countP (fun i => x i) % p = 0 <;> simp [hc]

end PallLean.Paper93.DeepMath.PathB.ACC0

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.modCircuit_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0.modCircuit_repr
