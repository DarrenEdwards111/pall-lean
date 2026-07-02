import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRazborovSmolenskyPoly

/-!
# Beigel–Tarui, rung 20: unbounded fan-in gates and the genuine RS degree win

Rungs 16–19 built the RS substitution for **binary** `AND`/`OR`/`NOT` formulas — but there the degree bound
`(2(p-1))^depth` gives no asymptotic win, because a 2-input gate is trivially exact.  The Razborov–Smolensky degree
reduction only bites for **unbounded fan-in** gates: an `OR`/`AND` of `m` sub-circuits, whose *exact* arithmetisation has
degree `~m` (a product/inclusion–exclusion over all `m` inputs), but whose RS approximator has degree only `t(p-1)` per
level — **independent of the fan-in `m`**.  This file reformulates the substitution over unbounded fan-in and proves
exactly that fan-in-independent bound.

  `UForm` — unbounded fan-in formulas: `var`, `NOT`, `OR` of a *list* of sub-formulas, `AND` of a list (`UForm.eval`,
        `UForm.depth`).
  `orApproxN` — the RS `OR`-approximator on a **list** of input polynomials, with subsets indexed by `ℕ` (so the same
        `subsets` list applies at every gate regardless of its fan-in): `1 - ∏_S (1 - (∑_{j∈S} inputsⱼ)^{p-1})`.
  `orApproxN_totalDegree_le` — **PROVED**: `deg ≤ (#subsets)·(p-1)·d` when the inputs have degree `≤ d` — crucially
        **independent of `#inputs` (the fan-in)**.
  `uArithApprox` — the whole-circuit substitution: `OR`/`AND` gates approximated by `orApproxN` on the (negated, for
        `AND`) sub-approximators, `NOT` exact.
  `uArithApprox_totalDegree_le` — **PROVED, the genuine degree win**: `deg ≤ ((#subsets)(p-1))^depth`, with the fan-in of
        every gate absorbed into the constant `(#subsets)(p-1)` per level.  So an unbounded fan-in depth-`d` circuit has a
        degree-`polylog` approximator (for `#subsets = t = polylog`) — the RS degree reduction the binary arc could not
        exhibit.

## Honest scope

This is the degree half of the *unbounded* fan-in RS approximation, and it is where the fan-in-independence — the whole
point of the polynomial method — actually appears (`orApproxN_totalDegree_le` has no `#inputs` factor).  What remains: the
**error bound** for unbounded gates — that with `t` subsets chosen by rung 8's averaging, each gate errs on `≤ 2^{n-t}`
inputs, and (the genuinely deep part) a correlated-inputs analysis of how the sub-circuit errors combine through the
circuit, giving whole-circuit error `< 2^n`; then the degree-`polylog`, error-`<2^n` polynomial feeds rung 15's quasipoly
AND count and the Toda `SYM` top to reach `SYM∘AND`.  The composite-`MOD_m` case remains the proven two-fields barrier.
Nothing here is the Beigel–Tarui reduction in full, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

open MvPolynomial
open scoped Classical

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **Unbounded fan-in formulas**: variables, `NOT`, and `OR`/`AND` of a *list* of sub-formulas. -/
inductive UForm (n : ℕ)
  | var (i : Fin n)
  | unot (a : UForm n)
  | uor (l : List (UForm n))
  | uand (l : List (UForm n))

/-- Boolean semantics: `OR` = `any`, `AND` = `all` (via `map` + `foldr`, structural over the children list). -/
def UForm.eval : UForm n → (Fin n → Bool) → Bool
  | .var i, x => x i
  | .unot a, x => !(a.eval x)
  | .uor l, x => (l.map (fun a => a.eval x)).foldr (· || ·) false
  | .uand l, x => (l.map (fun a => a.eval x)).foldr (· && ·) true

/-- The depth of an unbounded formula (max over the children list). -/
def UForm.depth : UForm n → ℕ
  | .var _ => 0
  | .unot a => a.depth + 1
  | .uor l => (l.map UForm.depth).foldr max 0 + 1
  | .uand l => (l.map UForm.depth).foldr max 0 + 1

/-- **A list-max membership bound**: every element is `≤` the `foldr max` of the list. -/
theorem mem_le_foldr_max (x : ℕ) (L : List ℕ) (h : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at h
  | cons a t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | ht
    · exact le_max_left _ _
    · exact le_trans (ih ht) (le_max_right _ _)

/-- The RS linear form over a `ℕ`-indexed subset of a **list** of input polynomials (`getD` with default `0` for
out-of-range indices). -/
noncomputable def linSumN (inputs : List (MvPolynomial (Fin n) (ZMod p))) (S : Finset ℕ) :
    MvPolynomial (Fin n) (ZMod p) := ∑ j ∈ S, inputs.getD j 0

/-- **The RS `OR`-approximator on a list of input polynomials**, subsets indexed by `ℕ` (fan-in-independent). -/
noncomputable def orApproxN (inputs : List (MvPolynomial (Fin n) (ZMod p)))
    (subsets : List (Finset ℕ)) : MvPolynomial (Fin n) (ZMod p) :=
  1 - (subsets.map (fun S => 1 - (linSumN inputs S) ^ (p - 1))).prod

/-- **Degree of an indexed input (proved)**: `≤ d` when all inputs have degree `≤ d` (out-of-range is `0`). -/
theorem getD_totalDegree_le (inputs : List (MvPolynomial (Fin n) (ZMod p))) (j d : ℕ)
    (h : ∀ q ∈ inputs, q.totalDegree ≤ d) : (inputs.getD j 0).totalDegree ≤ d := by
  rcases lt_or_ge j inputs.length with hj | hj
  · rw [List.getD_eq_getElem inputs 0 hj]; exact h _ (List.getElem_mem hj)
  · rw [List.getD_eq_default inputs 0 hj]; simp

/-- **Degree of the linear form (proved)**: `≤ d` when all inputs have degree `≤ d` — independent of `|S|` and of the
fan-in. -/
theorem linSumN_totalDegree_le (inputs : List (MvPolynomial (Fin n) (ZMod p))) (S : Finset ℕ) (d : ℕ)
    (h : ∀ q ∈ inputs, q.totalDegree ≤ d) : (linSumN inputs S).totalDegree ≤ d :=
  le_trans (totalDegree_finset_sum S _) (Finset.sup_le (fun j _ => getD_totalDegree_le inputs j d h))

/-- **The fan-in-independent degree bound (proved)**: the RS `OR`-approximator on inputs of degree `≤ d` has degree
`≤ (#subsets)·(p-1)·d` — **no `#inputs` (fan-in) factor**.  This is the crux of the polynomial method: an unbounded `OR`
costs only `t(p-1)` in degree, not `m`. -/
theorem orApproxN_totalDegree_le (inputs : List (MvPolynomial (Fin n) (ZMod p)))
    (subsets : List (Finset ℕ)) (d : ℕ) (h : ∀ q ∈ inputs, q.totalDegree ≤ d) :
    (orApproxN inputs subsets).totalDegree ≤ subsets.length * ((p - 1) * d) := by
  refine one_sub_totalDegree_le _ _ ?_
  have hlen : (subsets.map
      (fun S => (1 : MvPolynomial (Fin n) (ZMod p)) - (linSumN inputs S) ^ (p - 1))).length
      = subsets.length := List.length_map ..
  rw [← hlen]
  refine listprod_totalDegree_le _ ((p - 1) * d) (fun q hq => ?_)
  obtain ⟨S, _, rfl⟩ := List.mem_map.mp hq
  refine one_sub_totalDegree_le _ _ ?_
  exact le_trans (totalDegree_pow _ _) (Nat.mul_le_mul_left _ (linSumN_totalDegree_le inputs S d h))

/-- **The whole-circuit unbounded RS substitution**: `OR l` via `orApproxN` on the sub-approximators; `AND l` via
De Morgan (`orApproxN` on the negated sub-approximators); `NOT` exact; `var → Xᵢ`. -/
noncomputable def uArithApprox (subsets : List (Finset ℕ)) :
    UForm n → MvPolynomial (Fin n) (ZMod p)
  | .var i => X i
  | .unot a => 1 - uArithApprox subsets a
  | .uor l => orApproxN (l.map (fun a => uArithApprox subsets a)) subsets
  | .uand l => 1 - orApproxN (l.map (fun a => 1 - uArithApprox subsets a)) subsets

/-- **The genuine RS degree win (proved)**: the unbounded fan-in substituted polynomial has degree
`≤ ((#subsets)(p-1))^depth` — every gate's fan-in absorbed into the per-level constant `(#subsets)(p-1)`.  Polylog for
constant depth and `#subsets = t = polylog`, *regardless of fan-in*. -/
theorem uArithApprox_totalDegree_le' (subsets : List (Finset ℕ))
    (hD1 : 1 ≤ subsets.length * (p - 1)) :
    ∀ f : UForm n,
      (uArithApprox (p := p) subsets f).totalDegree ≤ (subsets.length * (p - 1)) ^ f.depth
  | .var i => by rw [uArithApprox]; simp only [UForm.depth, pow_zero]; exact (totalDegree_X i).le
  | .unot a => by
      rw [uArithApprox, UForm.depth]
      exact one_sub_totalDegree_le _ _ (le_trans (uArithApprox_totalDegree_le' subsets hD1 a)
        (Nat.pow_le_pow_right hD1 (Nat.le_succ _)))
  | .uor l => by
      rw [uArithApprox, UForm.depth]
      have hinp : ∀ q ∈ l.map (fun a => uArithApprox (p := p) subsets a),
          q.totalDegree ≤ (subsets.length * (p - 1)) ^ (l.map UForm.depth).foldr max 0 := by
        intro q hq
        rw [List.mem_map] at hq
        obtain ⟨a, ha, rfl⟩ := hq
        exact le_trans (uArithApprox_totalDegree_le' subsets hD1 a)
          (Nat.pow_le_pow_right hD1 (mem_le_foldr_max _ _ (List.mem_map_of_mem ha)))
      refine le_trans (orApproxN_totalDegree_le _ subsets _ hinp) (le_of_eq ?_)
      rw [pow_succ]; ring
  | .uand l => by
      rw [uArithApprox, UForm.depth]
      refine one_sub_totalDegree_le _ _ ?_
      have hinp : ∀ q ∈ l.map (fun a => (1 : MvPolynomial (Fin n) (ZMod p)) - uArithApprox subsets a),
          q.totalDegree ≤ (subsets.length * (p - 1)) ^ (l.map UForm.depth).foldr max 0 := by
        intro q hq
        rw [List.mem_map] at hq
        obtain ⟨a, ha, rfl⟩ := hq
        exact one_sub_totalDegree_le _ _ (le_trans (uArithApprox_totalDegree_le' subsets hD1 a)
          (Nat.pow_le_pow_right hD1 (mem_le_foldr_max _ _ (List.mem_map_of_mem ha))))
      refine le_trans (orApproxN_totalDegree_le _ subsets _ hinp) (le_of_eq ?_)
      rw [pow_succ]; ring

/-- **The degree win from `1 ≤ #subsets` (proved)**: derives the base bound `1 ≤ (#subsets)(p-1)` from a nonempty subset
list and `p` prime. -/
theorem uArithApprox_totalDegree_le (subsets : List (Finset ℕ)) (hlen : 1 ≤ subsets.length)
    (f : UForm n) :
    (uArithApprox (p := p) subsets f).totalDegree ≤ (subsets.length * (p - 1)) ^ f.depth := by
  have hp : 1 ≤ p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  exact uArithApprox_totalDegree_le' subsets (by simpa using Nat.mul_le_mul hlen hp) f

end PallLean.Paper93.DeepMath.PathB.RazborovSmolensky

#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.orApproxN_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.RazborovSmolensky.uArithApprox_totalDegree_le
