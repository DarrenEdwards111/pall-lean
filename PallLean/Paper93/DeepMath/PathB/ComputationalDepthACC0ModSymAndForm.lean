import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MonomialCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PolyToSymAnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CompositeBTTarget

/-!
# Brick D-assembly — a single `MOD_m` gate has an exact `SYM∘AND` form (proved)

The `SYM∘AND` normal form `eval = symEval (monoAND mono) h ∧ m+1 < 2^n` (the shape of `HasExactSymAndForm`) for a single
`MOD_m` gate is in fact *trivial*: the gate is a symmetric function of the Hamming weight, and the weight is exactly the
`gateCount` of the `n` **singleton** `AND`-gates `monoAND {i} = xᵢ`.  So `MOD_m = symEval (singletons) (fun c => decide (m ∣
c))`, with `m_form = n` monomials — `n+1 < 2^n` for `n ≥ 2`.

This makes the honest point sharp: a *single* gate is trivially `SYM∘AND` (degree-1, `n` terms).  The real YBT difficulty is
**depth composition** — where the degree grows to `polylog` and the monomial count to Brick D's `(n+1)^D` — not the single
gate.  This brick discharges the single-gate case exactly and connects it to the existing searchability cash-out.

## What is proved (clean axioms, no `sorry`)

* **`monoAND_singleton`** (PROVED) — `monoAND {i} x = x i`.
* **`gateCount_singletons`** (PROVED) — `gateCount (singletons) x = hammingWeight x`.
* **`modGate_eq_symEval`** (PROVED) — `(fun x => decide (m ∣ hammingWeight x)) = symEval (singletons) (fun c => decide (m ∣
  c))`.
* **`modGate_hasExactSymAndForm`** (PROVED) — the `HasExactSymAndForm` shape for the `MOD_m` *function*: `∃ M mono h, … ∧
  M+1 < 2^n` (with `M = n`).

## Honest scope

This is the **single-gate** exact `SYM∘AND` form (the easy case).  It does **not** handle composed `ACC⁰` circuits (depth
≥ 2, where degree → polylog and Brick D's count applies), the prime-power Toda lifting, nor wraps it as `eval C` for an
`ACC0Circuit C` — i.e. general YBT / `composite_BT_degree` remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModSymAndForm

open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount symEval)
open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT (hammingWeight)

/-- **The Boolean `MOD_m` gate.** -/
def modGateFn (m : ℕ) {n : ℕ} (x : Fin n → Bool) : Bool := decide (m ∣ hammingWeight x)

/-- **A singleton `AND` is just the bit (PROVED).** -/
theorem monoAND_singleton {n : ℕ} (i : Fin n) (x : Fin n → Bool) : monoAND {i} x = x i := by
  simp [monoAND]

/-- **The singleton `AND`s' count is the Hamming weight (PROVED).** -/
theorem gateCount_singletons {n : ℕ} (x : Fin n → Bool) :
    gateCount (fun (i : Fin n) y => monoAND {i} y) x = hammingWeight x := by
  unfold gateCount hammingWeight
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [monoAND_singleton]

/-- **A `MOD_m` gate equals `symEval` over the singleton `AND`s (PROVED).** -/
theorem modGate_eq_symEval {n : ℕ} (m : ℕ) :
    (modGateFn m : (Fin n → Bool) → Bool)
      = symEval (fun (i : Fin n) y => monoAND {i} y) (fun c => decide (m ∣ c)) := by
  funext x
  simp only [modGateFn, symEval, gateCount_singletons]

/-- **A `MOD_m` gate has the exact `SYM∘AND` form (`HasExactSymAndForm` shape) (PROVED).** -/
theorem modGate_hasExactSymAndForm {n : ℕ} (m : ℕ) (hn : n + 1 < 2 ^ n) :
    ∃ (M : ℕ) (mono : Fin M → Finset (Fin n)) (h : ℕ → Bool),
      (modGateFn m : (Fin n → Bool) → Bool) = symEval (fun j x => monoAND (mono j) x) h ∧ M + 1 < 2 ^ n :=
  ⟨n, fun i => {i}, fun c => decide (m ∣ c), modGate_eq_symEval m, hn⟩

/-!
**The single-gate exact `SYM∘AND` form, proved.**  A `MOD_m` gate is exactly `symEval` over `n` singleton `AND`s — the
easy, trivially-symmetric case, with `n+1 < 2^n` giving searchability via the existing cash-out (`lowDegreePoly_searchable`).
Next: composed circuits (depth ≥ 2, where Brick D's `(n+1)^D` count applies) and the prime-power lifting — the remaining
content of general YBT.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModSymAndForm

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModSymAndForm.modGate_eq_symEval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModSymAndForm.modGate_hasExactSymAndForm
