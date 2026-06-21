import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModSymAndForm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeMODFactor

/-!
# Brick A.3 — prime-power `MOD_{p^e}`: single gate done; composition obstruction documented (proved + honest)

The prime-power case, handled honestly.  Two genuinely-true facts, and a precise statement of the real obstruction.

**What is true and proved:**
* A `MOD_{p^e}` gate is decided by the residue `(weight : ZMod (p^e)) = 0` (`primePowerMod_iff_residue`).
* A *single* `MOD_{p^e}` gate is in exact `SYM∘AND` form — it is a symmetric function of the weight, so Brick D-assembly
  (`modGate_hasExactSymAndForm`, which holds for *any* modulus) applies (`primePowerMod_hasExactSymAndForm`).  Combined with
  Brick A.1 (CRT), **every** single composite-`MOD` gate (any modulus) is exact `SYM∘AND`.

**The honest obstruction (NOT socket-faked):** the genuine "Toda lifting" difficulty is the *low-degree polynomial*
representation needed for **composition** (depth ≥ 2).  Over `F_p` the `MOD_{p^e}` indicator is *not* low-degree for `e ≥ 2`
(no Fermat lift; RS-barrier-adjacent), and even over the non-field `ZMod (p^e)` there is no Fermat indicator.  So a clean
low-degree `F_p`/`ZMod (p^e)` representation of `MOD_{p^e}` **does not exist** — the Beigel–Tarui method uses a different
integer/symmetric representation.  Formalizing *that* is the genuine open content; it is **not** done here and **not** faked.

## What is proved (clean axioms, no `sorry`)

* **`primePowerMod_iff_residue`** (PROVED) — `modm (p^e) x ↔ (hammingWeight x : ZMod (p^e)) = 0`.
* **`primePowerMod_hasExactSymAndForm`** (PROVED) — the single `MOD_{p^e}` gate has the exact `SYM∘AND` form.

## Honest scope

Single-gate prime-power case: done.  The composition-level low-degree lift for `e ≥ 2` (the real Toda content) does **not**
admit a clean `F_p` representation and is **not** formalized here.  General YBT / `composite_BT_degree` remains open.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerMOD

open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT (hammingWeight)
open PallLean.Paper93.DeepMath.PathB.ACC0CompositeMODFactor (modm)
open PallLean.Paper93.DeepMath.PathB.ACC0ModSymAndForm (modGateFn modGate_hasExactSymAndForm)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (symEval)

/-- **A prime-power `MOD` gate is decided by the `ZMod (p^e)` residue (PROVED).** -/
theorem primePowerMod_iff_residue (p e : ℕ) [Fact p.Prime] {n : ℕ} (x : Fin n → Bool) :
    modm (p ^ e) x ↔ (hammingWeight x : ZMod (p ^ e)) = 0 := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e (Fact.out : p.Prime).pos.ne'⟩
  exact (ZMod.natCast_eq_zero_iff (hammingWeight x) (p ^ e)).symm

/-- **A single prime-power `MOD` gate has the exact `SYM∘AND` form (PROVED).**  It is a symmetric function of the weight, so
the any-modulus single-gate assembly (Brick D-assembly) applies. -/
theorem primePowerMod_hasExactSymAndForm (p e : ℕ) {n : ℕ} (hn : n + 1 < 2 ^ n) :
    ∃ (M : ℕ) (mono : Fin M → Finset (Fin n)) (h : ℕ → Bool),
      (modGateFn (p ^ e) : (Fin n → Bool) → Bool) = symEval (fun j x => monoAND (mono j) x) h ∧ M + 1 < 2 ^ n :=
  modGate_hasExactSymAndForm (p ^ e) hn

/-!
**Prime-power single gate, proved; composition obstruction documented.**  Every single composite-`MOD` gate (any modulus,
via A.1 + this) is exact `SYM∘AND`.  The prime-power *composition* lift (low-degree representation for depth ≥ 2) has no
clean `F_p`/`ZMod (p^e)` form and is the genuine open Toda content — **not** faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerMOD

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerMOD.primePowerMod_iff_residue
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimePowerMOD.primePowerMod_hasExactSymAndForm
