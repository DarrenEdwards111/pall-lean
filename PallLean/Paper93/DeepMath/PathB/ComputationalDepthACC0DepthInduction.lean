import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CircuitApprox
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OrStep

/-!
# The depth induction: every (`MOD`-free) circuit is approximable

This closes the Razborov–Smolensky depth induction for the `MOD`-free fragment (`AC⁰`): by structural recursion on the
circuit, every `Circ` built from `inp`/`const`/`not`/`or`/`and` has a low-degree `F₂` approximant.  The base cases are
`…ACC0CircuitApprox`; the `or`/`and` steps are `…ACC0OrStep` (`or_step`/`and_step`), bridged from the `List` fan-in to
the `Fin`-indexed family the step uses.

## What is proved (clean axioms, no `sorry`)

* `or_eval_bridge` / `and_eval_bridge` — `Circ.eval (or/and cs)` equals the `Fin cs.length`-indexed `orTarget`/
  `andTarget` of the subcircuit values (the `List`-to-`Fin` packaging).
* **`approximable_exists`** — `∀ C : Circ n, ∃ D E, Approximable C D E`: every `MOD`-free circuit has a low-degree
  approximant (by well-founded recursion on `sizeOf`, using `choose` + `Finset.sup` for the uniform subgate bounds).

## Honest scope

This completes the depth induction for the `MOD`-free (`AC⁰`) fragment — a clean from-scratch Razborov–Smolensky
construction, end to end.  It is **classical** (`AC⁰`/`AC⁰[2]`-level, the corpus's Tier 1/2), **not** new mathematics
and **not** progress toward `P ≠ NP`.  The bounds here are existential (`∃ D E`); the quantitative `degree ≤ t^depth`,
`error ≤ size·2^{-t}` follow by tracking `sup`/`size` through the same recursion.  Extending to `MOD` gates works only
for **prime-power** moduli (`mod2_mem_monoAND_span` is the `MOD₂` case); **composite `MOD_m` has no low-degree
representation over any field** — the genuine `ACC⁰` barrier, **Wall 1**, which the polynomial method cannot cross
(why `NEXP ⊄ ACC⁰` needed Williams' algorithmic method).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DepthInduction

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox
open PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm
open PallLean.Paper93.DeepMath.PathB.ACC0OrStep

variable {n : ℕ}

/-- **`OR` `List`-to-`Fin` bridge (proved): `Circ.eval (or cs)` is the `orTarget` of the subcircuit values.** -/
theorem or_eval_bridge (x : Fin n → Bool) (cs : List (Circ n)) :
    Circ.eval x (Circ.or cs) = orTarget (fun i : Fin cs.length => Circ.eval x (cs.get i)) := by
  simp only [Circ.eval, orTarget]
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_attach, true_and, Subtype.exists, decide_eq_true_eq]
  constructor
  · rintro ⟨c, hc, hev⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hc
    exact ⟨i, by rw [hi]; exact hev⟩
  · rintro ⟨i, hi⟩
    exact ⟨cs.get i, List.get_mem cs i, hi⟩

/-- **`AND` `List`-to-`Fin` bridge (proved).** -/
theorem and_eval_bridge (x : Fin n → Bool) (cs : List (Circ n)) :
    Circ.eval x (Circ.and cs) = andTarget (fun i : Fin cs.length => Circ.eval x (cs.get i)) := by
  simp only [Circ.eval, andTarget]
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_attach, Subtype.forall, decide_eq_true_eq]
  constructor
  · rintro hall i
    exact hall (cs.get i) (List.get_mem cs i) trivial
  · rintro hall a ha _
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    rw [← hi]; exact hall i

/-- `errCard` is `perr` against the circuit's Boolean value (definitional). -/
theorem errCard_eq_perr (P : MvPolynomial (Fin n) (ZMod 2)) (C : Circ n) :
    errCard P C = (perr P (fun x => Circ.eval x C)).card := rfl

/-- **The depth induction (proved): every `MOD`-free circuit has a low-degree `F₂` approximant.** -/
theorem approximable_exists : ∀ C : Circ n, ∃ D E, Approximable C D E
  | .inp i => ⟨1, 0, approximable_inp i⟩
  | .const b => ⟨0, 0, approximable_const b⟩
  | .not c => by
      obtain ⟨D, E, h⟩ := approximable_exists c
      exact ⟨D, E, approximable_not h⟩
  | .or cs => by
      have hforall : ∀ i : Fin cs.length, ∃ (D E : ℕ) (P : MvPolynomial (Fin n) (ZMod 2)),
          P.totalDegree ≤ D ∧ (perr P (fun x => Circ.eval x (cs.get i))).card ≤ E := by
        intro i
        obtain ⟨D, E, Q, hd, he⟩ := approximable_exists (cs.get i)
        exact ⟨D, E, Q, hd, he⟩
      choose D E P hP using hforall
      obtain ⟨Q, Eg, hdegQ, herrQ, _hgate⟩ :=
        or_step (t := 1) (fun i => fun x => Circ.eval x (cs.get i)) P
          (Finset.univ.sup D) (Finset.univ.sup E)
          (fun i => le_trans (hP i).1 (Finset.le_sup (Finset.mem_univ i)))
          (fun i => le_trans (hP i).2 (Finset.le_sup (Finset.mem_univ i)))
      refine ⟨1 * Finset.univ.sup D, cs.length * Finset.univ.sup E + Eg, Q, hdegQ, ?_⟩
      have hbridge : (fun x => Circ.eval x (Circ.or cs))
          = (fun x => orTarget (fun i : Fin cs.length => Circ.eval x (cs.get i))) := by
        funext x; exact or_eval_bridge x cs
      rw [errCard_eq_perr, hbridge]
      exact herrQ
  | .and cs => by
      have hforall : ∀ i : Fin cs.length, ∃ (D E : ℕ) (P : MvPolynomial (Fin n) (ZMod 2)),
          P.totalDegree ≤ D ∧ (perr P (fun x => Circ.eval x (cs.get i))).card ≤ E := by
        intro i
        obtain ⟨D, E, Q, hd, he⟩ := approximable_exists (cs.get i)
        exact ⟨D, E, Q, hd, he⟩
      choose D E P hP using hforall
      obtain ⟨Q, Eg, hdegQ, herrQ, _hgate⟩ :=
        and_step (t := 1) (fun i => fun x => Circ.eval x (cs.get i)) P
          (Finset.univ.sup D) (Finset.univ.sup E)
          (fun i => le_trans (hP i).1 (Finset.le_sup (Finset.mem_univ i)))
          (fun i => le_trans (hP i).2 (Finset.le_sup (Finset.mem_univ i)))
      refine ⟨1 * Finset.univ.sup D, cs.length * Finset.univ.sup E + Eg, Q, hdegQ, ?_⟩
      have hbridge : (fun x => Circ.eval x (Circ.and cs))
          = (fun x => andTarget (fun i : Fin cs.length => Circ.eval x (cs.get i))) := by
        funext x; exact and_eval_bridge x cs
      rw [errCard_eq_perr, hbridge]
      exact herrQ
  termination_by C => sizeOf C
  decreasing_by
    all_goals simp_wf
    all_goals (have h := List.sizeOf_lt_of_mem (List.get_mem cs i)
               simp only [List.get_eq_getElem] at h
               omega)

end PallLean.Paper93.DeepMath.PathB.ACC0DepthInduction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DepthInduction.or_eval_bridge
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DepthInduction.approximable_exists
