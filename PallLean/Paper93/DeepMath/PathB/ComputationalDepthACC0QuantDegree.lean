import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthInduction

/-!
# Quantitative degree bound: every `MOD`-free circuit has an approximant of degree `≤ t^depth`

`…ACC0DepthInduction` proved every `MOD`-free circuit is approximable with *existential* bounds.  This file sharpens
the degree to the Razborov–Smolensky form: degree `≤ t^(depth)`.  Each `OR`/`AND` layer multiplies the boosted
degree by `t`, so over depth `d` the degree is `t^d` — polylog in the circuit size when `t = polylog` and `d` is
constant (the `(log s)^{O(d)}` bound).

## What is proved (clean axioms, no `sorry`)

* `cdepth` — circuit depth (`OR`/`AND` add a layer, `NOT` is free).
* `cdepth_or_get_lt` / `cdepth_and_get_lt` — a subcircuit's depth is strictly less than its `OR`/`AND` parent's.
* **`approximable_quant`** — for `t ≥ 1`, `∀ C, ∃ E, Approximable C (t ^ cdepth C) E`: degree bounded by `t^depth`.

## Honest scope

This is the quantitative (degree) form of the `MOD`-free (`AC⁰`) Razborov–Smolensky construction — still **classical**
(`AC⁰`/`AC⁰[2]`-level, Tier 1/2), **not** new mathematics and **not** progress toward `P ≠ NP`.  The error bound stays
existential here (it accumulates as `≤ k·E + 2^{-t}` per layer, `…ACC0OrStep`).  Extending to `MOD` works only for
prime-power moduli; composite `MOD_m` is the genuine `ACC⁰` barrier, **Wall 1**.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0QuantDegree

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitApprox
open PallLean.Paper93.DeepMath.PathB.ACC0SmallErrorForm
open PallLean.Paper93.DeepMath.PathB.ACC0OrStep
open PallLean.Paper93.DeepMath.PathB.ACC0DepthInduction

variable {n : ℕ}

/-- Circuit depth: `OR`/`AND` add a layer, `NOT` is free, leaves are depth `0`. -/
def cdepth : Circ n → ℕ
  | .inp _ => 0
  | .const _ => 0
  | .not c => cdepth c
  | .or cs => 1 + (cs.attach.map (fun c => cdepth c.1)).foldr max 0
  | .and cs => 1 + (cs.attach.map (fun c => cdepth c.1)).foldr max 0
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    all_goals (have h := List.sizeOf_lt_of_mem c.2; omega)

/-- Every list element is `≤` the `foldr max 0` of the list (proved). -/
theorem le_foldr_max : ∀ (l : List ℕ) (a : ℕ), a ∈ l → a ≤ l.foldr max 0
  | [], a, h => by simp at h
  | b :: l, a, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max l a h') (le_max_right _ _)

/-- A subcircuit's depth is strictly less than its `OR` parent's (proved). -/
theorem cdepth_or_get_lt (cs : List (Circ n)) (i : Fin cs.length) :
    cdepth (cs.get i) < cdepth (Circ.or cs) := by
  have hmem : cdepth (cs.get i) ∈ (cs.attach.map (fun c => cdepth c.1)) :=
    List.mem_map.mpr ⟨⟨cs.get i, List.get_mem cs i⟩, List.mem_attach cs _, rfl⟩
  have hle := le_foldr_max _ _ hmem
  simp only [cdepth]
  omega

/-- A subcircuit's depth is strictly less than its `AND` parent's (proved). -/
theorem cdepth_and_get_lt (cs : List (Circ n)) (i : Fin cs.length) :
    cdepth (cs.get i) < cdepth (Circ.and cs) := by
  have hmem : cdepth (cs.get i) ∈ (cs.attach.map (fun c => cdepth c.1)) :=
    List.mem_map.mpr ⟨⟨cs.get i, List.get_mem cs i⟩, List.mem_attach cs _, rfl⟩
  have hle := le_foldr_max _ _ hmem
  simp only [cdepth]
  omega

/-- Weakening the degree bound (proved). -/
theorem Approximable.mono_deg {C : Circ n} {D D' E : ℕ} (h : Approximable C D E) (hD : D ≤ D') :
    Approximable C D' E := by
  obtain ⟨P, hd, he⟩ := h
  exact ⟨P, le_trans hd hD, he⟩

variable {t : ℕ}

/-- **The quantitative degree bound (proved): `∀ C, ∃ E, Approximable C (t^depth C) E` for `t ≥ 1`.** -/
theorem approximable_quant (ht : 1 ≤ t) : ∀ C : Circ n, ∃ E, Approximable C (t ^ cdepth C) E
  | .inp i => ⟨0, by simp only [cdepth, pow_zero]; exact approximable_inp i⟩
  | .const b => ⟨0, by
      simp only [cdepth, pow_zero]; exact Approximable.mono_deg (approximable_const b) (Nat.zero_le 1)⟩
  | .not c => by
      obtain ⟨E, h⟩ := approximable_quant ht c
      exact ⟨E, by simp only [cdepth]; exact approximable_not h⟩
  | .or cs => by
      have hforall : ∀ i : Fin cs.length, ∃ (E : ℕ) (P : MvPolynomial (Fin n) (ZMod 2)),
          P.totalDegree ≤ t ^ cdepth (cs.get i)
            ∧ (perr P (fun x => Circ.eval x (cs.get i))).card ≤ E := by
        intro i
        obtain ⟨E, Q, hd, he⟩ := approximable_quant ht (cs.get i)
        exact ⟨E, Q, hd, he⟩
      choose E P hd he using hforall
      have hpos : 1 ≤ cdepth (Circ.or cs) := by
        simp only [cdepth]; omega
      have hdeg' : ∀ i, (P i).totalDegree ≤ t ^ (cdepth (Circ.or cs) - 1) := fun i =>
        le_trans (hd i) (Nat.pow_le_pow_right ht (by have := cdepth_or_get_lt cs i; omega))
      obtain ⟨Q, Eg, hdegQ, herrQ, _hgate⟩ :=
        or_step (t := t) (fun i => fun x => Circ.eval x (cs.get i)) P
          (t ^ (cdepth (Circ.or cs) - 1)) (Finset.univ.sup E) hdeg'
          (fun i => le_trans (he i) (Finset.le_sup (Finset.mem_univ i)))
      refine ⟨cs.length * Finset.univ.sup E + Eg, Q, ?_, ?_⟩
      · have heq : t * t ^ (cdepth (Circ.or cs) - 1) = t ^ cdepth (Circ.or cs) := by
          rw [← pow_succ']; congr 1; omega
        exact le_of_le_of_eq hdegQ heq
      · have hbridge : (fun x => Circ.eval x (Circ.or cs))
            = (fun x => orTarget (fun i : Fin cs.length => Circ.eval x (cs.get i))) := by
          funext x; exact or_eval_bridge x cs
        rw [errCard_eq_perr, hbridge]
        exact herrQ
  | .and cs => by
      have hforall : ∀ i : Fin cs.length, ∃ (E : ℕ) (P : MvPolynomial (Fin n) (ZMod 2)),
          P.totalDegree ≤ t ^ cdepth (cs.get i)
            ∧ (perr P (fun x => Circ.eval x (cs.get i))).card ≤ E := by
        intro i
        obtain ⟨E, Q, hd, he⟩ := approximable_quant ht (cs.get i)
        exact ⟨E, Q, hd, he⟩
      choose E P hd he using hforall
      have hpos : 1 ≤ cdepth (Circ.and cs) := by
        simp only [cdepth]; omega
      have hdeg' : ∀ i, (P i).totalDegree ≤ t ^ (cdepth (Circ.and cs) - 1) := fun i =>
        le_trans (hd i) (Nat.pow_le_pow_right ht (by have := cdepth_and_get_lt cs i; omega))
      obtain ⟨Q, Eg, hdegQ, herrQ, _hgate⟩ :=
        and_step (t := t) (fun i => fun x => Circ.eval x (cs.get i)) P
          (t ^ (cdepth (Circ.and cs) - 1)) (Finset.univ.sup E) hdeg'
          (fun i => le_trans (he i) (Finset.le_sup (Finset.mem_univ i)))
      refine ⟨cs.length * Finset.univ.sup E + Eg, Q, ?_, ?_⟩
      · have heq : t * t ^ (cdepth (Circ.and cs) - 1) = t ^ cdepth (Circ.and cs) := by
          rw [← pow_succ']; congr 1; omega
        exact le_of_le_of_eq hdegQ heq
      · have hbridge : (fun x => Circ.eval x (Circ.and cs))
            = (fun x => andTarget (fun i : Fin cs.length => Circ.eval x (cs.get i))) := by
          funext x; exact and_eval_bridge x cs
        rw [errCard_eq_perr, hbridge]
        exact herrQ
  termination_by C => sizeOf C
  decreasing_by
    all_goals simp_wf
    all_goals (first
      | omega
      | (have h := List.sizeOf_lt_of_mem (List.get_mem cs i)
         simp only [List.get_eq_getElem] at h
         omega))

end PallLean.Paper93.DeepMath.PathB.ACC0QuantDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0QuantDegree.approximable_quant
