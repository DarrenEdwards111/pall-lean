import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitModel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MiniBTTwoCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModSymAndForm

/-!
# Every `ACC0Circuit` evaluates to an exact single-count SYM∘AND (PROVED)

The syntactic lift of the exact-composition thread.  The closures (`hasSymAndRep_not`/`and`/`or`) and
the MOD base case have been proved at the *function* level; this file lifts them to the **syntactic**
`ACC0Circuit` type by structural induction:

  `acc0circuit_eval_hasSymAndRep` — for **any** `ACC0Circuit C`, `eval C` is *exactly* a single-count
  `SYM∘AND` (`HasSymAndRep`).

Base cases: `const`; `var i` (`= monoAND {i}`, via `monoAND_singleton`); `mod q S t`
(`= decide((weightOn S : ZMod q) = t)`, symmetric in the subset count — `modGateOn_hasSymAndRep`).
Inductive cases: `not`/`and`/`or` via the unconditional `SYM∘AND` closures (`and`/`or` = the two-count
mixed-radix collapse of `ACC0MiniBTTwoCount`).

## What is proved (clean axioms, no `sorry`)

* `satCount_orderEmb_eq_weightOn` — `satCount` over the `S`-enumerated singletons `= weightOn S`.
* `modGateOn_hasSymAndRep` — the subset MOD gate is exactly single-count `SYM∘AND`.
* `acc0circuit_eval_hasSymAndRep` — every `ACC0Circuit`'s `eval` is `HasSymAndRep`.

## Honest scope

This is **exactness**, not size: the `SYM∘AND` produced by `and`/`or` composition has the iterated
mixed-radix **tower** size (`ACC0MiniBTSize`), so it is searchable only when that size stays `< 2^n`
(bounded depth and fan-in).  Keeping the size quasipoly across unbounded depth is the open Beigel–Tarui
content.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0CircuitToSymAnd

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel
open PallLean.Paper93.DeepMath.PathB.ACC0Mod6SymAndDepth2 (satCount)
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd (monoAND)
open PallLean.Paper93.DeepMath.PathB.ACC0ModSymAndForm (monoAND_singleton)
open PallLean.Paper93.DeepMath.PathB.ACC0SymAndComposition
open PallLean.Paper93.DeepMath.PathB.ACC0MiniBTTwoCount (hasSymAndRep_and hasSymAndRep_or)
open PallLean.Paper93.DeepMath.PathB.TwoGateCorrelation (weightOn modQStatOn)

variable {n : ℕ}

/-- **`satCount` over the `S`-enumerated singletons equals `weightOn S` (proved).** -/
theorem satCount_orderEmb_eq_weightOn (S : Finset (Fin n)) (x : Fin n → Bool) :
    satCount (fun j : Fin S.card => ({S.orderEmbOfFin rfl j} : Finset (Fin n))) x = weightOn S x := by
  rw [weightOn, ← Finset.card_filter]
  simp only [satCount, monoAND]
  apply Finset.card_bij (fun (j : Fin S.card) _ => S.orderEmbOfFin rfl j)
  · intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨S.orderEmbOfFin_mem rfl j, ?_⟩
    have h2 := hj.2
    simp only [decide_eq_true_eq, Finset.mem_singleton, forall_eq] at h2
    exact h2
  · intro j1 _ j2 _ h
    exact (S.orderEmbOfFin rfl).injective h
  · intro i hi
    rw [Finset.mem_filter] at hi
    have hmem : i ∈ Set.range (S.orderEmbOfFin rfl) := by rw [S.range_orderEmbOfFin rfl]; exact hi.1
    obtain ⟨j, hj⟩ := hmem
    refine ⟨j, ?_, hj⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    simp only [decide_eq_true_eq, Finset.mem_singleton, forall_eq, hj]
    exact hi.2

/-- **The subset MOD gate is exactly single-count `SYM∘AND` (proved).** -/
theorem modGateOn_hasSymAndRep (q : ℕ) (S : Finset (Fin n)) (t : ZMod q) :
    HasSymAndRep (fun x => decide (modQStatOn S q x = t)) := by
  refine ⟨S.card, fun j => {S.orderEmbOfFin rfl j}, fun c => decide ((c : ZMod q) = t), fun x => ?_⟩
  rw [satCount_orderEmb_eq_weightOn]
  rfl

/-- **Every `ACC0Circuit` evaluates to an exact single-count `SYM∘AND` (proved).** -/
theorem acc0circuit_eval_hasSymAndRep (C : ACC0Circuit n) : HasSymAndRep (eval C) := by
  induction C with
  | const b => exact ⟨0, Fin.elim0, fun _ => b, fun _ => rfl⟩
  | var i =>
    refine ⟨1, fun _ => {i}, fun c => decide (0 < c), fun x => ?_⟩
    show eval (ACC0Circuit.var i) x = decide (0 < satCount (fun _ : Fin 1 => ({i} : Finset (Fin n))) x)
    simp only [eval, satCount, monoAND, decide_eq_true_eq, Finset.mem_singleton, forall_eq]
    by_cases hxi : x i = true <;> simp [hxi]
  | not c ih =>
    simp only [eval]; exact hasSymAndRep_not ih
  | and a b iha ihb =>
    simp only [eval]; exact hasSymAndRep_and iha ihb
  | or a b iha ihb =>
    simp only [eval]; exact hasSymAndRep_or iha ihb
  | mod q S t => exact modGateOn_hasSymAndRep q S t

/-!
**Syntactic lift proved.**  Every `ACC0Circuit`'s `eval` is *exactly* a single-count `SYM∘AND` — the
front-half exact representation for the real circuit type, no approximation.  The size is the iterated
mixed-radix tower (`ACC0MiniBTSize`), so searchability holds only when it stays `< 2^n`; quasipoly
across unbounded depth is the open Beigel–Tarui content.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0CircuitToSymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0CircuitToSymAnd.acc0circuit_eval_hasSymAndRep
