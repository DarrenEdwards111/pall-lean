import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimePowerGate

/-!
# Prime-power observer candidates — refute the field family, confirm the richer observers

The prime-power obstruction (`…ACC0PrimePowerObstruction`) showed `MOD_{p^e}` is not a function of the mod-`p`
residue.  This file tests the candidate *richer* observers the tri-aspect boundary could select, proving honestly which
fail and which carry enough information.

* **Refuted — any characteristic-`p` field** (`F_p`, `F_{p^k}`, `F̄_p`, …).  The count's image in *any* field of
  characteristic `p` depends only on the mod-`p` residue (`p ↦ 0`), so it cannot see `MOD_{p^e}`.  This generalises the
  `F_p` obstruction to the whole field family.

* **Confirmed (information-sufficient) — the ring `ZMod (p^e)`** (characteristic `p^e`, *not* a field; has zero
  divisors).  It sees the mod-`p^e` residue and decides `MOD_{p^e}`.

* **Confirmed (information-sufficient) — the `p`-adic valuation `v_p`** (candidate: `x ↦ min(v_p x, e)`).
  `MOD_{p^e}(x) ⟺ v_p(x) ≥ e` — the valuation threshold decides `MOD_{p^e}`.

So the boundary must select a **filtered ring / valuation observer**, not a field one.  The remaining wall is whether
any such richer observer admits a *quasipolynomial low-degree sparse* representation (over `ZMod (p^e)` the zero
divisors break the Fermat indicator; the valuation is a threshold, not an obvious low-degree polynomial).

## What is proved (clean axioms, no `sorry`)

* **`charP_field_observer_fails`** — every characteristic-`p` field observer fails: `(0 : F) = (p : F)` yet `MOD_{p^e}`
  separates `0` and `p`.
* **`ringPrimePower_observer_decides`** — `ZMod (p^e)` decides `MOD_{p^e}` (`(s : ZMod (p^e)) = 0 ↔ p^e ∣ s`).
* **`valuation_observer_decides`** — the valuation decides it: `p^e ∣ x ↔ e ≤ v_p(x)` (`x ≠ 0`).

## Honest scope

This refutes the field-observer family (proved) and confirms two richer information-sufficient observers (ring residue,
`p`-adic valuation; proved).  It does **not** give either a quasipolynomial low-degree sparse representation — that is
the open `ACC⁰[composite]` crux.  The candidate test is honest: the field family is out, the filtered/valuation
observers are in *information-theoretically*, and the low-degree representation over them is the remaining wall.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerObserverCandidates

/-- **Refuted — any characteristic-`p` field observer fails (proved).**  In a field `F` of characteristic `p`, the
count's image depends only on the mod-`p` residue: `(0 : F) = (p : F)` (both `0`), yet `MOD_{p^e}` accepts `0` and
rejects `p` for `e ≥ 2`.  So no characteristic-`p` field (`F_p`, `F_{p^k}`, …) can compute `MOD_{p^e}`. -/
theorem charP_field_observer_fails (F : Type*) [Field F] (p e : ℕ) [hp : Fact p.Prime] [CharP F p]
    (he : 2 ≤ e) :
    ((0 : ℕ) : F) = ((p : ℕ) : F) ∧ p ^ e ∣ 0 ∧ ¬ p ^ e ∣ p := by
  refine ⟨by simp [CharP.cast_eq_zero], dvd_zero _, ?_⟩
  intro h
  have hle := Nat.le_of_dvd hp.out.pos h
  have hlt : p < p ^ e := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ e := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  omega

/-- **Confirmed — the ring `ZMod (p^e)` decides `MOD_{p^e}` (proved).**  It sees the mod-`p^e` residue (characteristic
`p^e`, not a field): `(s : ZMod (p^e)) = 0 ↔ p^e ∣ s`. -/
theorem ringPrimePower_observer_decides (p e s : ℕ) :
    ((s : ZMod (p ^ e)) = 0) ↔ p ^ e ∣ s :=
  ACC0PrimePowerGate.modPrimePower_observer_decides p e s

/-- **Confirmed — the `p`-adic valuation decides `MOD_{p^e}` (proved): `p^e ∣ x ↔ e ≤ v_p(x)`.**  The valuation
observer `x ↦ min(v_p x, e)` (accept iff `= e`) carries enough information; `MOD_{p^e}` is the threshold `v_p(x) ≥ e`. -/
theorem valuation_observer_decides (p x e : ℕ) (hp : p.Prime) (hx : x ≠ 0) :
    p ^ e ∣ x ↔ e ≤ x.factorization p :=
  hp.pow_dvd_iff_le_factorization hx

end PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerObserverCandidates

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerObserverCandidates.charP_field_observer_fails
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerObserverCandidates.ringPrimePower_observer_decides
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerObserverCandidates.valuation_observer_decides
