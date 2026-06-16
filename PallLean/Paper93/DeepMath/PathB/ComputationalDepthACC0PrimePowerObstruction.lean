import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimePowerGate

/-!
# The prime-power obstruction, made precise — `MOD_{p^e}` is not a function of the mod-`p` residue

The squarefree composite-`MOD` route works because each `MOD_p` indicator is a function of the *mod-`p`* residue,
computed by the field polynomial `1 − X^{p−1}` over `F_p`.  This file pins down *why* that route cannot reach prime
powers: for `e ≥ 2`, **`MOD_{p^e}` is not a function of the mod-`p` residue at all** — so *no* polynomial over `F_p`
in the prime-`p` residue (regardless of degree) can compute it.  A constructive low-degree replacement would have to
carry mod-`p^e` information, which is exactly the open `ACC⁰[composite]` problem; honesty requires recording the
obstruction rather than fabricating a field indicator.

## What is proved (clean axioms, no `sorry`)

* **`modPrimePower_not_function_of_modP`** — a concrete witness: `0` and `p` have the *same* mod-`p` residue
  (`(0 : ZMod p) = (p : ZMod p)`), yet `MOD_{p^e}` accepts `0` (`p^e ∣ 0`) and rejects `p` (`¬ p^e ∣ p`) for `e ≥ 2`.
  Hence `MOD_{p^e}` is not determined by the mod-`p` residue.
* **`modPrimePower_needs_ring`** (re-export) — the residue observer that *does* decide `MOD_{p^e}` lives in the ring
  `ZMod (p^e)` (`(s : ZMod (p^e)) = 0 ↔ p^e ∣ s`), not a low-degree `F_p` polynomial.

## Honest scope

This is the **obstruction**, not a circumvention.  It proves that the prime-`p` field observer is *information-theoretically*
insufficient for prime powers (`MOD_{p^e}` depends on more than the mod-`p` residue), which is precisely why the
squarefree route stops here and why a low-degree-field prime-power gate polynomial would be the open `ACC⁰[composite]`
lower bound.  No approximate/probabilistic field replacement is claimed — constructing one is the open problem.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerObstruction

/-- **The prime-power obstruction (proved): `MOD_{p^e}` is not a function of the mod-`p` residue.**  The inputs `0` and
`p` share the mod-`p` residue (both `0`), yet `MOD_{p^e}` accepts `0` and rejects `p` for `e ≥ 2`.  So no `F_p`
polynomial in the prime-`p` residue can compute `MOD_{p^e}` — the field observer is information-theoretically
insufficient. -/
theorem modPrimePower_not_function_of_modP (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e) :
    ((0 : ℕ) : ZMod p) = ((p : ℕ) : ZMod p) ∧ p ^ e ∣ 0 ∧ ¬ p ^ e ∣ p := by
  refine ⟨by simp, dvd_zero _, ?_⟩
  intro h
  have hle := Nat.le_of_dvd hp.pos h
  have hlt : p < p ^ e := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ e := Nat.pow_lt_pow_right hp.one_lt (by omega)
  omega

/-- **The deciding observer for `MOD_{p^e}` is the ring residue (re-export).**  `(s : ZMod (p^e)) = 0 ↔ p^e ∣ s` — the
observer that works lives in the *ring* `ZMod (p^e)`, not a low-degree field polynomial. -/
theorem modPrimePower_needs_ring (p e s : ℕ) :
    ((s : ZMod (p ^ e)) = 0) ↔ p ^ e ∣ s :=
  ACC0PrimePowerGate.modPrimePower_observer_decides p e s

end PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerObstruction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerObstruction.modPrimePower_not_function_of_modP
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerObstruction.modPrimePower_needs_ring
