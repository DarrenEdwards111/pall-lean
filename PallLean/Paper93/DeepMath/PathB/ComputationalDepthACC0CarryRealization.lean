import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarryObserverSize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarryInvariant

/-!
# Carry observer realisation — the decode is realisable over fields; the count is the barrier (conservative)

Entry 239 showed the carry observer's *state count* is quasipolynomial (not the obstruction).  This file attacks the
**algebraic realisation** (`CarryRefinementCrossing`, entry 238): realising the count-decode as a polynomial.  The
honest finding parallels 239 — the **decode is realisable over a field** (every count→boolean map is a degree-`≤(p-1)`
polynomial, via the Fermat point-indicator) — which *relocates* the barrier precisely onto the **exact count
computation** for composite modulus (entry 234 `ApproxToExactCount`), not the decode.

⚠️ **Two honest caveats (no overclaim).**  (i) The realised object is the **decode** (count → boolean), which in a
`SYM∘AND` is the *free symmetric part* — the degree cost is in computing the *count* (the `AND` layer), addressed by
entry 234, not here.  (ii) The Fermat realisation has degree `p-1` = (field size) − 1, and faithfulness needs field
`≥ N+1` (entry 239), so a *faithful* single-field realisation has degree `~N`, **not** low-degree — the low-degree
realisation for composite `m` remains the open barrier.  Nothing here crosses it.

## Definitions

* `pointIndicator p a := 1 - (X - C a)^(p-1)` — the Fermat indicator of `{a}` over a prime field.
* `RealizesCarryObserver m D` — every decode `dec : ZMod m → Bool` is realised by a degree-`≤D` polynomial over `ZMod m`
  (`P.eval y = if dec y then 1 else 0`).

## What is proved (clean axioms, no `sorry`)

* **`pointIndicator_eval`** (PROVED) — `(pointIndicator p a).eval y = if y = a then 1 else 0` (Fermat:
  `(y-a)^(p-1) = [y ≠ a]`).
* **`pointIndicator_natDegree_le`** (PROVED) — degree `≤ p-1`.
* **`decPoly_eval` / `decPoly_natDegree_le`** (PROVED) — the decode polynomial `∑_{a : dec a} pointIndicator a`
  evaluates to `[dec y]` and has degree `≤ p-1`.
* **`prime_realizes`** (PROVED) — *prime field realises via Fermat*: `RealizesCarryObserver p (p-1)` — every decode over
  a prime field is a degree-`≤(p-1)` polynomial.
* **`faithful_of_size`** (PROVED, re-export entry 239) — *if `m ≥ N+1`, the exact count observer is faithful*.

## Residual fragments (honest sockets / supporting facts)

* **squarefree via CRT**: for squarefree `m`, `ZMod m ≃+* ∏ ZMod pᵢ` (entry-235 `crt_residue_observer_suffices`); each
  prime-field factor realises (`prime_realizes`), so the realisation reduces to the per-prime decodes — the CRT
  assembly into one `ZMod m` polynomial is the residual glue (`squarefree_crt_reduction`, the iso re-exported).
* **prime-power needs digit/carry layers**: over `ZMod (p^e)` (`e ≥ 2`) the Fermat/power route *fails* — no power
  indicator exists (entry-235 `not_powerIndicator_primePow`); the realisation needs the p-adic digit decomposition (the
  named open layer-realisation, not the single-power field method).
* **composite low-degree realisation**: the open barrier — a *low-degree* (in the inputs) exact-count realisation for
  composite `m` — is entry-234 `ApproxToExactCount` / entry-238 `CarryRefinementCrossing`.

## Honest scope

The proved core shows the **count-decode is realisable over a field** (`prime_realizes`, via the Fermat point-indicator)
and that exactness needs `m ≥ N+1` (`faithful_of_size`).  Combined with the caveats, this confirms the obstruction is
neither the observer's size (entry 239) nor the decode (here) but the **exact, low-degree count computation for
composite modulus** — entry-234 `ApproxToExactCount`, the open `ACC⁰[m]` separation-strength wall.  This file does not
cross it.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

open Polynomial Finset

namespace PallLean.Paper93.DeepMath.PathB.ACC0CarryRealization

variable (p : ℕ) [Fact p.Prime]

/-- The Fermat indicator of the singleton `{a}` over a prime field: `1 - (X - a)^(p-1)`, degree `p-1`. -/
noncomputable def pointIndicator (a : ZMod p) : (ZMod p)[X] := 1 - (X - C a) ^ (p - 1)

/-- `(y - a)^(p-1) = [y ≠ a]` over a prime field (Fermat: nonzero ↦ 1, zero ↦ 0). -/
theorem sub_pow_card_sub_one (y a : ZMod p) :
    (y - a) ^ (p - 1) = if y = a then 0 else 1 := by
  by_cases h : y = a
  · subst h
    simp [sub_self, zero_pow (by have := (Fact.out : p.Prime).two_le; omega : p - 1 ≠ 0)]
  · rw [if_neg h, ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr h)]

/-- **The Fermat point-indicator evaluates to the singleton indicator (PROVED).**
`(pointIndicator p a).eval y = if y = a then 1 else 0`. -/
theorem pointIndicator_eval (a y : ZMod p) :
    (pointIndicator p a).eval y = if y = a then 1 else 0 := by
  unfold pointIndicator
  rw [eval_sub, eval_one, eval_pow, eval_sub, eval_X, eval_C, sub_pow_card_sub_one]
  by_cases h : y = a <;> simp [h]

/-- **The point-indicator has degree `≤ p-1` (PROVED).** -/
theorem pointIndicator_natDegree_le (a : ZMod p) :
    (pointIndicator p a).natDegree ≤ p - 1 := by
  unfold pointIndicator
  calc (1 - (X - C a) ^ (p - 1) : (ZMod p)[X]).natDegree
      ≤ max (1 : (ZMod p)[X]).natDegree ((X - C a) ^ (p - 1)).natDegree := natDegree_sub_le _ _
    _ ≤ p - 1 := by
        rw [natDegree_one]
        refine max_le (Nat.zero_le _) ?_
        calc ((X - C a) ^ (p - 1)).natDegree
            ≤ (p - 1) * (X - C a).natDegree := natDegree_pow_le
          _ ≤ p - 1 := by
              have h1 : (X - C a : (ZMod p)[X]).natDegree ≤ 1 := by
                calc (X - C a).natDegree
                    ≤ max (X : (ZMod p)[X]).natDegree (C a).natDegree := natDegree_sub_le _ _
                  _ ≤ 1 := by rw [natDegree_X, natDegree_C]; omega
              calc (p - 1) * (X - C a).natDegree ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ h1
                _ = p - 1 := mul_one _

/-- The decode polynomial over a prime field: the sum of point-indicators over the accepting set. -/
noncomputable def decPoly (dec : ZMod p → Bool) : (ZMod p)[X] :=
  ∑ a ∈ Finset.univ.filter (fun a => dec a = true), pointIndicator p a

/-- **The decode polynomial computes `dec` (PROVED).**  `(decPoly p dec).eval y = if dec y then 1 else 0` — exactly the
`a = y` term fires iff `dec y`. -/
theorem decPoly_eval (dec : ZMod p → Bool) (y : ZMod p) :
    (decPoly p dec).eval y = if dec y then 1 else 0 := by
  unfold decPoly
  rw [eval_finset_sum]
  simp only [pointIndicator_eval]
  rw [Finset.sum_ite_eq (Finset.univ.filter (fun a => dec a = true)) y (fun _ => (1 : ZMod p))]
  simp [Finset.mem_filter]

/-- **The decode polynomial has degree `≤ p-1` (PROVED).** -/
theorem decPoly_natDegree_le (dec : ZMod p → Bool) :
    (decPoly p dec).natDegree ≤ p - 1 := by
  unfold decPoly
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ (fun a _ => pointIndicator_natDegree_le p a)

/-- **A carry observer over `ZMod m` is realised at degree `D`**: every decode `dec : ZMod m → Bool` is a degree-`≤D`
polynomial (its singleton arithmetisation). -/
def RealizesCarryObserver (m D : ℕ) : Prop :=
  ∀ dec : ZMod m → Bool, ∃ P : (ZMod m)[X], P.natDegree ≤ D ∧ ∀ y, P.eval y = if dec y then 1 else 0

/-- **Prime field realises via the Fermat indicator (PROVED).**  `RealizesCarryObserver p (p-1)`: over a prime field
every decode (count → boolean) is a degree-`≤(p-1)` polynomial (the decode polynomial `decPoly`).  Note: degree `p-1`
scales with the field size, so a *faithful* single-field realisation (`p ≥ N+1`, entry 239) has degree `~N`, not
low-degree — this realises the free symmetric decode, not the low-degree count. -/
theorem prime_realizes : RealizesCarryObserver p (p - 1) :=
  fun dec => ⟨decPoly p dec, decPoly_natDegree_le p dec, decPoly_eval p dec⟩

/-- **If `m ≥ N+1`, the exact count observer is faithful (PROVED, entry 239).**  Re-export of
`ACC0CarryObserverSize.faithful_iff_le`: enough states ⟹ the count is recovered exactly. -/
theorem faithful_of_size (m N : ℕ) (hm : 0 < m) (hle : N + 1 ≤ m) :
    ACC0CarryObserverSize.Faithful m N :=
  (ACC0CarryObserverSize.faithful_iff_le m N hm).mpr hle

/-- **Squarefree via CRT (supporting fact).**  For coprime `a, b`, `ZMod (a·b) ≃+* ZMod a × ZMod b`
(entry-235 `crt_residue_observer_suffices`); each prime-field factor realises by `prime_realizes`, reducing the
squarefree realisation to the per-prime decodes.  The CRT assembly into one `ZMod (a·b)` polynomial is the residual glue. -/
theorem squarefree_crt_reduction (a b : ℕ) (h : Nat.Coprime a b) :
    Nonempty (ZMod (a * b) ≃+* ZMod a × ZMod b) :=
  PallLean.Paper93.DeepMath.PathB.ACC0CarryInvariant.crt_residue_observer_suffices a b h

/-- **Prime-power needs digit/carry layers (supporting obstruction).**  Over `ZMod (p^e)` (`e ≥ 2`) the Fermat/power
route fails — no power indicator exists (entry-235 `not_powerIndicator_primePow`) — so the single-power field method
does not realise the indicator; the realisation needs the p-adic digit decomposition (the open layer-realisation). -/
theorem primePow_no_power_indicator (e : ℕ) (he : 2 ≤ e) :
    ¬ PallLean.Paper93.DeepMath.PathB.ACC0CarryInvariant.PowerIndicator (p ^ e) :=
  PallLean.Paper93.DeepMath.PathB.ACC0CarryInvariant.not_powerIndicator_primePow p e he

end PallLean.Paper93.DeepMath.PathB.ACC0CarryRealization

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryRealization.pointIndicator_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryRealization.prime_realizes
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryRealization.faithful_of_size
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CarryRealization.primePow_no_power_indicator
