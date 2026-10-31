import Mathlib

/-!
# Beigel–Tarui, rung 2: the Razborov–Smolensky probabilistic polynomial (degree reduction)

Rung 1 (`…BeigelTaruiBase`) gave the *exact* arithmetisation (degree up to `n`).  The Beigel–Tarui / Razborov–Smolensky
**degree reduction** replaces `OR` by a *low-degree* polynomial over `F_p` that agrees with `OR` with high probability:
each `(subset-sum)^{p-1}` gadget has degree `p-1` (Fermat: it is the nonzero-indicator over `F_p`), and combining `t`
random-subset gadgets gives a degree-`t(p-1)` approximator — degree independent of `n`, controlled by the gadget count.

This file builds that approximator and proves its two load-bearing properties: the **exact degree bound** and the
**one-sided correctness** (exact on the all-zero input; correct whenever a subset "fires").

  `fermatInd` — **PROVED**: over `F_p`, `a^{p-1} = [a ≠ 0]` (Fermat) — the degree-`(p-1)` nonzero-indicator gadget.
  `orApprox` — the `OR` approximator (function): `1 - ∏_S (1 - (∑_{i∈S} xᵢ)^{p-1})` over a list of subsets.
  `orApprox_zero` — **PROVED**: on the all-`false` input the approximator is `0` — *exactly* `OR(0)`, no error.
  `orApprox_fires` — **PROVED**: whenever some subset has nonzero sum, the approximator is `1` — *exactly* `OR` on a
        nonzero input.
  `orApproxP` / `orApproxP_totalDegree_le` — **PROVED, the degree reduction**: the approximator as an `MvPolynomial` has
        total degree `≤ (#subsets)·(p-1)` — bounded by the gadget count, *independent of `n`*.
  `eval_orApproxP` — **PROVED**: the polynomial evaluates to the function `orApprox` on every Boolean point — the degree
        bound and the correctness are about the same object.

## Honest scope

This is the RS approximator with its **degree bound** and **one-sided correctness** — the degree-reduction gadget at the
heart of Beigel–Tarui.  What is **not** here is the *probability* estimate: that for random subsets, "some subset fires"
for every fixed nonzero input with probability `≥ 1 - 2^{-t}` (the subset-sum-nonzero counting: fixing a coordinate with
`xᵢ ≠ 0` and pairing subsets by toggling it shows `Pr[∑ = 0] ≤ 1/2`).  That amplification, and then composing the
low-degree `OR`/`AND` approximators through a depth-`d` circuit to degree `polylog` and folding into a single `SYM∘AND`,
are the remaining Beigel–Tarui content.  This file supplies the degree-reduced gadget and its exactness where it fires.
Nothing here is the Beigel–Tarui reduction, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial

variable {p n : ℕ} [Fact p.Prime]

/-! ### The Fermat nonzero-indicator gadget -/

/-- **The Fermat nonzero-indicator (proved)**: over `F_p`, `a^{p-1}` is `1` if `a ≠ 0` and `0` if `a = 0` — a
degree-`(p-1)` polynomial detecting nonzero-ness. -/
theorem fermatInd (a : ZMod p) : a ^ (p - 1) = if a = 0 then 0 else 1 := by
  by_cases h : a = 0
  · rw [if_pos h, h, zero_pow (by have := (Fact.out : p.Prime).two_le; omega)]
  · rw [if_neg h, ZMod.pow_card_sub_one_eq_one h]

/-- A Boolean input embedded in `F_p`. -/
def xf (x : Fin n → Bool) (i : Fin n) : ZMod p := if x i then 1 else 0

/-- The sum of a subset's coordinates over `F_p`. -/
def ssum (S : Finset (Fin n)) (x : Fin n → Bool) : ZMod p := ∑ i ∈ S, xf x i

/-- The RS gadget on an input: `(subset-sum)^{p-1}` = nonzero-indicator of the subset sum. -/
def ind (S : Finset (Fin n)) (x : Fin n → Bool) : ZMod p := (ssum S x) ^ (p - 1)

/-- The `OR` approximator over a list of subsets. -/
def orApprox (subsets : List (Finset (Fin n))) (x : Fin n → Bool) : ZMod p :=
  1 - (subsets.map (fun S => 1 - ind S x)).prod

theorem ind_eq (S : Finset (Fin n)) (x : Fin n → Bool) :
    ind (p := p) S x = if ssum (p := p) S x = 0 then 0 else 1 := fermatInd _

/-- **Exact on the all-`false` input (proved)**: `orApprox = 0 = OR(0)`, no approximation error. -/
theorem orApprox_zero (subsets : List (Finset (Fin n))) (x : Fin n → Bool)
    (hx : ∀ i, x i = false) : orApprox (p := p) subsets x = 0 := by
  have hssum : ∀ S, ssum (p := p) S x = 0 := fun S => by simp [ssum, xf, hx]
  simp only [orApprox]
  rw [List.prod_eq_one]
  · ring
  · intro y hy
    obtain ⟨S, _, rfl⟩ := List.mem_map.mp hy
    rw [ind_eq, hssum, if_pos rfl]; ring

/-- **Correct whenever a subset fires (proved)**: if some subset has nonzero sum, `orApprox = 1 = OR` on a nonzero
input. -/
theorem orApprox_fires (subsets : List (Finset (Fin n))) (x : Fin n → Bool)
    (hfire : ∃ S ∈ subsets, ssum (p := p) S x ≠ 0) : orApprox (p := p) subsets x = 1 := by
  obtain ⟨S, hS, hne⟩ := hfire
  have hprod : (subsets.map (fun S => 1 - ind (p := p) S x)).prod = 0 :=
    List.prod_eq_zero (List.mem_map.mpr ⟨S, hS, by rw [ind_eq, if_neg hne]; ring⟩)
  simp [orApprox, hprod]

/-! ### The polynomial and its degree bound (the degree reduction) -/

/-- The linear form `∑_{i∈S} Xᵢ` as a polynomial. -/
noncomputable def linFormP (S : Finset (Fin n)) : MvPolynomial (Fin n) (ZMod p) := ∑ i ∈ S, X i

/-- The RS gadget as a polynomial: `(∑_{i∈S} Xᵢ)^{p-1}`, of degree `≤ p-1`. -/
noncomputable def indP (S : Finset (Fin n)) : MvPolynomial (Fin n) (ZMod p) := (linFormP S) ^ (p - 1)

/-- The `OR` approximator as a polynomial. -/
noncomputable def orApproxP (subsets : List (Finset (Fin n))) : MvPolynomial (Fin n) (ZMod p) :=
  1 - (subsets.map (fun S => 1 - indP S)).prod

theorem linFormP_totalDegree_le (S : Finset (Fin n)) : (linFormP (p := p) S).totalDegree ≤ 1 :=
  le_trans (totalDegree_finset_sum S _) (Finset.sup_le (fun i _ => (totalDegree_X i).le))

theorem indP_totalDegree_le (S : Finset (Fin n)) : (indP (p := p) S).totalDegree ≤ p - 1 := by
  refine le_trans (totalDegree_pow _ _) ?_
  calc (p - 1) * _ ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ (linFormP_totalDegree_le S)
    _ = p - 1 := Nat.mul_one _

/-- Degree of `1 - q` is bounded by the degree of `q`. -/
theorem one_sub_totalDegree_le (q : MvPolynomial (Fin n) (ZMod p)) (d : ℕ) (hq : q.totalDegree ≤ d) :
    ((1 : MvPolynomial (Fin n) (ZMod p)) - q).totalDegree ≤ d := by
  refine le_trans (totalDegree_sub 1 q) ?_
  simp only [totalDegree_one]; omega

theorem listprod_totalDegree_le (l : List (MvPolynomial (Fin n) (ZMod p))) (d : ℕ)
    (h : ∀ q ∈ l, q.totalDegree ≤ d) : l.prod.totalDegree ≤ l.length * d := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.prod_cons, List.length_cons]
    refine le_trans (totalDegree_mul a t.prod) ?_
    have ht := ih (fun q hq => h q (by simp [hq]))
    have ha := h a (by simp)
    have he : (t.length + 1) * d = d + t.length * d := by ring
    omega

/-- **The degree reduction (proved)**: the `OR` approximator polynomial has total degree `≤ (#subsets)·(p-1)` —
controlled by the number of gadgets, *independent of the number of variables `n`*. -/
theorem orApproxP_totalDegree_le (subsets : List (Finset (Fin n))) :
    (orApproxP (p := p) subsets).totalDegree ≤ subsets.length * (p - 1) := by
  refine one_sub_totalDegree_le _ _ ?_
  have hlen : (subsets.map (fun S => (1 : MvPolynomial (Fin n) (ZMod p)) - indP S)).length
      = subsets.length := List.length_map ..
  rw [← hlen]
  refine listprod_totalDegree_le _ (p - 1) (fun q hq => ?_)
  obtain ⟨S, _, rfl⟩ := List.mem_map.mp hq
  exact one_sub_totalDegree_le _ _ (indP_totalDegree_le S)

/-- **The polynomial computes the function (proved)**: evaluating `orApproxP` at a Boolean point gives `orApprox` — so
the degree bound and the correctness lemmas are about the same object. -/
theorem eval_orApproxP (subsets : List (Finset (Fin n))) (x : Fin n → Bool) :
    (eval (fun i => xf (p := p) x i)) (orApproxP (p := p) subsets) = orApprox (p := p) subsets x := by
  simp only [orApproxP, orApprox, indP, linFormP, ind, ssum, map_sub, map_one, map_list_prod,
    List.map_map, map_pow, map_sum, eval_X, Function.comp_def]

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.fermatInd
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.orApprox_fires
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.orApproxP_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.eval_orApproxP
