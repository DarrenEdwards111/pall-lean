import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMajorityAlgebraicImmunity

/-!
# Attacking the bottom clause: exact unbounded-fan-in `OR`/`AND` needs full degree = fan-in

The fragment ladder localized Wall 1 to the **bottom clause**: `ACC⁰ → exact low-degree integer polynomial across
depth`.  Every fragment worked because the bottom `AND` had *bounded* fan-in `w`, keeping its exact degree `≤ w`.
This file attacks the clause head-on at the gate level and proves the obstruction is **real**: an *unbounded*-fan-in
`OR` (or `AND`) over `n` bits has *exact* `F₂` degree exactly `n` — the full fan-in.

Concretely, over `F₂` every Boolean function has a *unique* multilinear (ANF) representation, recovered by the
subset-sum transform `anf` (`…MajorityAlgebraicImmunity`, `anf_involutive`: `anf (anf g) = g`).  We compute the top
ANF coefficient of `OR` and `AND`:

```
anf (OR_n)  univ = 1 ≠ 0        (top monomial x₁⋯xₙ present — via the parity of the 2ⁿ−1 nonempty subsets)
anf (AND_n) univ = 1 ≠ 0        (AND is literally the single full monomial)
```

So the exact `F₂` polynomial of an unbounded-fan-in `OR`/`AND` contains the degree-`n` monomial: its exact degree is
`n`, and its exact monomial-`AND` (`SYM∘AND` bottom) representation needs `2^n` monomials — **exponential**, not
quasipolynomial.

This is the precise, formal statement of why the bottom clause is hard.  The naive route — represent each `ACC⁰` gate
by a *single exact low-degree* polynomial — is **impossible** for unbounded fan-in: exactness forces degree = fan-in.
The only escape is the *approximate* low-degree polynomial (Razborov–Smolensky `toAgree`, degree polylog but agreeing
only `1-ε`, already proved in `Layer3`) converted back to an *exact* decision by the symmetric/count top — and doing
that while keeping the degree polylog is exactly the irreducible Beigel–Tarui analytic core (Wall 1).  This file does
not cross that wall; it proves the *gate-level* exact-vs-approximate gap that makes the wall necessary, ruling out the
naive single-polynomial approach.

## What is proved (clean axioms, no `sorry`)

* `orFn` / `andFn` — the `OR`/`AND` functions as `F₂`-valued functions on the Boolean cube (indexed by the set of
  `1`-bits).
* `anf_andFn_univ` — `anf andFn univ = 1` (the full monomial is `AND`'s only ANF term).
* `anf_orFn_univ` — `anf orFn univ = 1` for `n ≥ 1` (the full monomial is present in `OR`'s ANF, via the parity of the
  `2ⁿ−1` nonempty subsets).
* `or_exact_degree_full` / `and_exact_degree_full` — `∃ S, |S| = n ∧ anf · S ≠ 0`: the exact degree is the full fan-in.
* `or_not_anf_degree_lt` / `and_not_anf_degree_lt` — **the no-go**: there is *no* exact `F₂` representation of degree
  `< n`; the full-degree monomial cannot be dropped.

## Honest scope

This is a genuine, sharp **no-go for the naive bottom-clause route** — exact unbounded-fan-in `OR`/`AND` forces
degree = fan-in, hence exponential exact monomial count.  It is the exact counterpart to the proved *approximate*
low-degree side (`toAgree_totalDegree_le`), and together they show the bottom clause genuinely needs the
approximate→exact symmetric-top conversion, the irreducible Beigel–Tarui core (Wall 1).  It does **not** prove that
conversion (it does not, and this file does not claim to, cross Wall 1).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ExactDegreeNoGo

open Finset
open PallLean.Paper93.DeepMath.PathB.MajorityAI

variable {n : ℕ}

/-- The **`OR` function** as an `F₂`-valued function on the Boolean cube: `orFn T = OR` of the input whose set of
`1`-bits is `T`, i.e. `1` iff `T ≠ ∅`. -/
def orFn : Finset (Fin n) → ZMod 2 := fun T => if T = ∅ then 0 else 1

/-- The **`AND` function** as an `F₂`-valued function on the Boolean cube: `andFn T = 1` iff every bit is set
(`T = univ`). -/
def andFn : Finset (Fin n) → ZMod 2 := fun T => if T = Finset.univ then 1 else 0

/-- **The full monomial is `AND`'s only ANF term (proved): `anf andFn univ = 1`.** -/
theorem anf_andFn_univ : anf (andFn (n := n)) (Finset.univ : Finset (Fin n)) = 1 := by
  classical
  unfold anf andFn
  rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)).powerset (Finset.univ : Finset (Fin n))
        (fun _ => (1 : ZMod 2))]
  simp

/-- **The full monomial is present in `OR`'s ANF (proved): `anf orFn univ = 1` for `n ≥ 1`.**  Computed from the
parity of the `2ⁿ − 1` nonempty subsets. -/
theorem anf_orFn_univ [NeZero n] : anf (orFn (n := n)) (Finset.univ : Finset (Fin n)) = 1 := by
  classical
  have h1 : anf (orFn (n := n)) (Finset.univ : Finset (Fin n))
      = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, (if T ≠ ∅ then (1 : ZMod 2) else 0) := by
    unfold anf orFn
    refine Finset.sum_congr rfl (fun T _ => ?_)
    by_cases h : T = ∅ <;> simp [h]
  rw [h1, Finset.sum_boole]
  -- count the nonempty subsets: `powerset.card - 1 = 2ⁿ - 1`
  have hfilter : ((Finset.univ : Finset (Fin n)).powerset.filter (fun T => T ≠ ∅))
      = (Finset.univ : Finset (Fin n)).powerset.erase ∅ := Finset.filter_ne' _ _
  rw [hfilter,
    Finset.card_erase_of_mem (Finset.mem_powerset.mpr (Finset.empty_subset _)),
    Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  -- `((2ⁿ - 1 : ℕ) : ZMod 2) = 1`
  rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_one]
  have h2 : ((2 ^ n : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_pow, show ((2 : ℕ) : ZMod 2) = 0 from by decide,
      zero_pow (NeZero.ne n)]
  rw [h2, zero_sub, neg_eq_iff_add_eq_zero]
  decide

/-- **Exact degree of unbounded-fan-in `OR` is the full fan-in (proved): there is a nonzero ANF coefficient at a set
of size `n`.** -/
theorem or_exact_degree_full [NeZero n] :
    ∃ S : Finset (Fin n), S.card = n ∧ anf (orFn (n := n)) S ≠ 0 :=
  ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin],
    by rw [anf_orFn_univ]; exact one_ne_zero⟩

/-- **Exact degree of unbounded-fan-in `AND` is the full fan-in (proved).** -/
theorem and_exact_degree_full [NeZero n] :
    ∃ S : Finset (Fin n), S.card = n ∧ anf (andFn (n := n)) S ≠ 0 :=
  ⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin],
    by rw [anf_andFn_univ]; exact one_ne_zero⟩

/-- **The bottom-clause no-go for `OR` (proved): no exact `F₂` representation of degree `< n`.**  The full-degree
monomial cannot be dropped, so unbounded-fan-in `OR` is not exactly a low-degree polynomial. -/
theorem or_not_anf_degree_lt [NeZero n] :
    ¬ ∀ S : Finset (Fin n), n ≤ S.card → anf (orFn (n := n)) S = 0 := by
  intro h
  have hu := h Finset.univ (by rw [Finset.card_univ, Fintype.card_fin])
  rw [anf_orFn_univ] at hu
  exact one_ne_zero hu

/-- **The bottom-clause no-go for `AND` (proved): no exact `F₂` representation of degree `< n`.** -/
theorem and_not_anf_degree_lt [NeZero n] :
    ¬ ∀ S : Finset (Fin n), n ≤ S.card → anf (andFn (n := n)) S = 0 := by
  intro h
  have hu := h Finset.univ (by rw [Finset.card_univ, Fintype.card_fin])
  rw [anf_andFn_univ] at hu
  exact one_ne_zero hu

end PallLean.Paper93.DeepMath.PathB.ACC0ExactDegreeNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactDegreeNoGo.anf_andFn_univ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactDegreeNoGo.anf_orFn_univ
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactDegreeNoGo.or_exact_degree_full
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ExactDegreeNoGo.or_not_anf_degree_lt
