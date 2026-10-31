import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyUnion

/-!
# Beigel–Tarui, rung 8: the RS instantiation — choosing good subsets by averaging

Rung 5 gave a fixed subset-family that makes the RS approximator *exactly* correct (zero error) for `t > n` — but at
degree `(n+1)(p-1)`.  For the **degree win** one keeps `t` small and accepts a small error.  This file does exactly
that: by **averaging** rung 4's `2^{-t}` per-input bound over inputs, it produces a *fixed* subset-family whose RS
approximator errs on only a `2^{-t}` fraction of inputs — the per-gate object rung 7's union bound consumes.

  `orApprox_allFail` — **PROVED**: if every subset has zero sum on `x`, the approximator is `0` there (it fails).
  `orApprox_ne_one_iff` — **PROVED**: the approximator fails to fire at `x` iff the family is "all-fail" at `x`.
  `numErr` — the number of nonzero inputs on which the family's RS approximator errs.
  `sum_numErr` — **PROVED (double counting)**: `∑` over families of `numErr` `=` `∑` over nonzero inputs of the all-fail
        count (Fubini).
  `exists_low_error` / `exists_low_error_orApprox` — **PROVED, the instantiation**: some fixed subset-family makes the
        RS approximator err on at most a `2^{-t}` fraction of inputs (`2^t · #errors ≤ 2ⁿ`) — the averaging existence
        that chooses good subsets.

## Honest scope

This is the per-gate RS instantiation: a *fixed* degree-`t(p-1)` (rung 2) approximator polynomial that errs on a
`2^{-t}` fraction of inputs, obtained by averaging rung 4's amplification (double count over the choice space, then
pigeonhole).  It is exactly the object rung 7 consumes: taking each gate's `bad` set to be its `≤ 2^{n-t}` error inputs,
rung 7's `error_card_le` bounds the whole-circuit error by `∑_gates 2^{n-t} = #gates · 2^{n-t}`, while rung 6 bounds the
degree by `(t(p-1))^depth`.  Choosing `t` with `#gates · 2^{n-t} < 2ⁿ` (e.g. `t = O(log #gates)`) then keeps both the
degree `polylog` and the error small.  Wiring these per-gate bad sets into rung 7 for a concrete `ACC⁰` circuit, and
folding the resulting low-degree polynomial into one `SYM∘AND` with `m` quasipolynomial, are the remaining Beigel–Tarui
content.  This file supplies the averaging that turns rung 4's amplification into a fixed low-error approximator.
Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

variable {p n : ℕ} [Fact p.Prime]

open scoped Classical

/-- **The approximator fails when every subset has zero sum (proved)**: generalising `orApprox_zero` to any input on
which all subset-sums vanish. -/
theorem orApprox_allFail (subsets : List (Finset (Fin n))) (x : Fin n → Bool)
    (h : ∀ S ∈ subsets, ssum (p := p) S x = 0) : orApprox (p := p) subsets x = 0 := by
  simp only [orApprox]
  rw [List.prod_eq_one]
  · ring
  · intro y hy
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hy
    rw [ind_eq, h S hS, if_pos rfl]; ring

/-- **The approximator errs at `x` iff the family is all-fail there (proved)**: `orApprox (ofFn f) x ≠ 1` iff every
subset of `f` has zero sum on `x`. -/
theorem orApprox_ne_one_iff (t : ℕ) (f : Fin t → Finset (Fin n)) (x : Fin n → Bool) :
    (orApprox (p := p) (List.ofFn f) x ≠ 1) ↔ f ∈ allFail (p := p) x t := by
  rw [mem_allFail]
  constructor
  · intro h1
    by_contra hnall
    push_neg at hnall
    obtain ⟨j, hj⟩ := hnall
    exact h1 (orApprox_fires _ x ⟨f j, List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩)
  · intro hall h1
    have hz : orApprox (p := p) (List.ofFn f) x = 0 := by
      apply orApprox_allFail
      intro S hS; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hS; exact hall j
    rw [hz] at h1; exact one_ne_zero h1.symm

/-- The nonzero inputs. -/
noncomputable def NZ (n : ℕ) : Finset (Fin n → Bool) := Finset.univ.filter (fun x => ∃ i, x i = true)

/-- The number of nonzero inputs on which the family `f`'s RS approximator errs. -/
noncomputable def numErr (t : ℕ) (f : Fin t → Finset (Fin n)) : ℕ :=
  ((NZ n).filter (fun x => f ∈ allFail (p := p) x t)).card

/-- `numErr` counts exactly the nonzero inputs on which `orApprox (ofFn f)` fails to compute `OR`. -/
theorem numErr_eq (t : ℕ) (f : Fin t → Finset (Fin n)) :
    numErr (p := p) t f
      = ((NZ n).filter (fun x => orApprox (p := p) (List.ofFn f) x ≠ 1)).card := by
  simp only [numErr]
  congr 1
  ext x
  simp only [Finset.mem_filter, orApprox_ne_one_iff]

/-- **Double counting (proved)**: summing `numErr` over all families equals summing the all-fail count over nonzero
inputs (Fubini). -/
theorem sum_numErr (t : ℕ) :
    ∑ f : Fin t → Finset (Fin n), numErr (p := p) t f = ∑ x ∈ NZ n, (allFail (p := p) x t).card := by
  simp only [numErr, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.card_filter]
  congr 1
  exact Finset.filter_univ_mem _

/-- The summed amplification bound: `2^t · (∑ over nonzero inputs of the all-fail count) ≤ 2ⁿ · (2ⁿ)^t`. -/
theorem sum_allFail_bound (t : ℕ) :
    2 ^ t * (∑ x ∈ NZ n, (allFail (p := p) x t).card) ≤ 2 ^ n * (2 ^ n) ^ t := by
  rw [Finset.mul_sum]
  calc ∑ x ∈ NZ n, 2 ^ t * (allFail (p := p) x t).card
      ≤ ∑ _x ∈ NZ n, (2 ^ n) ^ t := by
        apply Finset.sum_le_sum
        intro x hx
        rw [NZ, Finset.mem_filter] at hx
        exact amplification x hx.2 t
    _ = (NZ n).card * (2 ^ n) ^ t := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ n * (2 ^ n) ^ t := by
        apply Nat.mul_le_mul_right
        calc (NZ n).card ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_filter_le _ _
          _ = 2 ^ n := by rw [Finset.card_univ]; simp

/-- **The averaging existence (proved)**: some fixed subset-family `f` has `2^t · numErr f ≤ 2ⁿ` — its RS approximator
errs on at most a `2^{-t}` fraction of inputs.  Proof: if every family exceeded this, the total error would exceed the
summed amplification bound. -/
theorem exists_low_error (t : ℕ) :
    ∃ f : Fin t → Finset (Fin n), 2 ^ t * numErr (p := p) t f ≤ 2 ^ n := by
  by_contra hc
  push_neg at hc
  have hcard : (Finset.univ : Finset (Fin t → Finset (Fin n))).card = (2 ^ n) ^ t := by
    rw [Finset.card_univ]; simp [Fintype.card_finset]
  have hlow : (Finset.univ : Finset (Fin t → Finset (Fin n))).card * (2 ^ n + 1)
      ≤ ∑ f : Fin t → Finset (Fin n), 2 ^ t * numErr (p := p) t f := by
    calc (Finset.univ : Finset (Fin t → Finset (Fin n))).card * (2 ^ n + 1)
        = ∑ _f : Fin t → Finset (Fin n), (2 ^ n + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ f : Fin t → Finset (Fin n), 2 ^ t * numErr (p := p) t f :=
          Finset.sum_le_sum (fun f _ => hc f)
  have hhigh : ∑ f : Fin t → Finset (Fin n), 2 ^ t * numErr (p := p) t f ≤ 2 ^ n * (2 ^ n) ^ t := by
    rw [← Finset.mul_sum, sum_numErr]; exact sum_allFail_bound t
  rw [hcard] at hlow
  have hcomb := le_trans hlow hhigh
  have h2 : 0 < (2 ^ n) ^ t := pow_pos (pow_pos (by norm_num) n) t
  rw [mul_comm (2 ^ n) ((2 ^ n) ^ t)] at hcomb
  have := Nat.le_of_mul_le_mul_left hcomb h2
  omega

/-- **The instantiation, in terms of `orApprox` (proved)**: a fixed subset-family makes the RS approximator
`orApprox (ofFn f)` err on at most a `2^{-t}` fraction of inputs — a degree-`t(p-1)` polynomial (rung 2) with input
error `≤ 2^{-t}`, the per-gate object rung 7's union bound consumes. -/
theorem exists_low_error_orApprox (t : ℕ) :
    ∃ f : Fin t → Finset (Fin n),
      2 ^ t * ((NZ n).filter (fun x => orApprox (p := p) (List.ofFn f) x ≠ 1)).card ≤ 2 ^ n := by
  obtain ⟨f, hf⟩ := exists_low_error (p := p) t
  exact ⟨f, by rw [← numErr_eq]; exact hf⟩

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_low_error
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.exists_low_error_orApprox
