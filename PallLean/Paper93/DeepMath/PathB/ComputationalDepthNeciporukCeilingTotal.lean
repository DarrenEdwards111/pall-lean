import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukCeiling
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthFunctionResidualObserver

/-!
# The Nečiporuk ceiling, summed: the observer boundary is polynomially capped (the no-go)

`ComputationalDepthNeciporukCeiling` proved the sharp *per-block* caps — `log₂ #subfunctions ≤ min(2^b, n-b)` —
and explicitly deferred *"the cross-partition optimization to `n²/log n`... the standard convexity argument."*
This file discharges that deferred step in the form the observer no-go needs: it **sums** the per-block boundary
over a variable partition and proves the total is **polynomial** (`≤ n²`).

That polynomial cap is the whole point.  The frontier (`SCOPE_MACHINE_COMPLETENESS_BRIDGE.md`) requires a
*super-polynomial* observer boundary for SAT under some decomposition to contradict `boundary ≤ runtime`.  But
`neciporuk_ceiling` shows the total boundary is `≤ n²` for **every** function and **every** decomposition, so the
required super-polynomial value is unreachable: the observer boundary cannot, even in principle, witness a `P` vs
`NP` separation.

We use the representation-free subfunction count `funResiduals S f` over `Fin n` (so blocks compose into a
partition).  The per-block bound here is the loose `≤ n` (which already gives a polynomial total); the sharp
`min(2^b, n-b)` per-block cap lives in `NeciporukCeiling.log_subfunctions_le_min` and yields the tighter
`Θ(n²/log n)` under the convexity optimization.  Either way the conclusion — *polynomial, hence cannot separate* —
is the same.

## Honest scope

A proved *limitation*: the observer/Nečiporuk boundary is quadratically capped and cannot separate `P` from `NP`.
A no-go, not a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NeciporukCeilingTotal

open PallLean.Paper93.DeepMath.PathB.FunctionResidualObserver

variable {n : ℕ}

/-- The number of subfunctions of `f` on a block `S` is at most `2^n`: they are the image of the `2^n`
assignments under the residual map. -/
theorem funResiduals_card_le (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) :
    (funResiduals S f).card ≤ 2 ^ n := by
  classical
  have h : (funResiduals S f).card ≤ (Finset.univ : Finset (Fin n → Bool)).card := by
    rw [funResiduals]
    exact Finset.card_image_le
  rwa [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h

/-- **Per-block ceiling.**  The observer boundary on any block is at most `n`. -/
theorem funBoundary_le (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) :
    Nat.log 2 ((funResiduals S f).card) ≤ n := by
  calc Nat.log 2 ((funResiduals S f).card)
      ≤ Nat.log 2 (2 ^ n) := Nat.log_mono_right (funResiduals_card_le S f)
    _ = n := Nat.log_pow (by norm_num) _

/-- A partition into disjoint non-empty blocks has at most `n` blocks. -/
theorem partition_card_le (P : Finset (Finset (Fin n)))
    (hdisj : (↑P : Set (Finset (Fin n))).PairwiseDisjoint id) (hne : ∀ S ∈ P, S.Nonempty) :
    P.card ≤ n := by
  classical
  have hb : (P.biUnion id).card = ∑ S ∈ P, S.card :=
    Finset.card_biUnion (fun x hx y hy hxy => hdisj hx hy hxy)
  have h1 : P.card ≤ ∑ S ∈ P, S.card := by
    calc P.card = ∑ _S ∈ P, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ S ∈ P, S.card := Finset.sum_le_sum (fun S hS => Finset.card_pos.mpr (hne S hS))
  have h2 : ∑ S ∈ P, S.card ≤ n := by
    rw [← hb]
    calc (P.biUnion id).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  omega

/-- **The Nečiporuk ceiling (summed).**  For every function `f` on `n` variables and every partition of the
variables into disjoint non-empty blocks, the total observer boundary is at most `n²`.  Being polynomial, it can
never be super-polynomial — so the observer boundary cannot witness a `P` vs `NP` separation. -/
theorem neciporuk_ceiling (f : (Fin n → Bool) → Bool) (P : Finset (Finset (Fin n)))
    (hdisj : (↑P : Set (Finset (Fin n))).PairwiseDisjoint id) (hne : ∀ S ∈ P, S.Nonempty) :
    ∑ S ∈ P, Nat.log 2 ((funResiduals S f).card) ≤ n ^ 2 := by
  calc ∑ S ∈ P, Nat.log 2 ((funResiduals S f).card)
      ≤ ∑ _S ∈ P, n := Finset.sum_le_sum (fun S _ => funBoundary_le S f)
    _ = P.card * n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n := Nat.mul_le_mul_right _ (partition_card_le P hdisj hne)
    _ = n ^ 2 := (sq n).symm

/-- **The no-go, stated as an impossibility.**  No function's observer boundary can exceed `n²` on any partition;
in particular a super-polynomial boundary (needed to beat `boundary ≤ runtime` for a poly-time SAT machine) never
occurs.  Concretely: if a partition's total boundary were `> n²`, that is a contradiction. -/
theorem observer_boundary_not_superpoly (f : (Fin n → Bool) → Bool) (P : Finset (Finset (Fin n)))
    (hdisj : (↑P : Set (Finset (Fin n))).PairwiseDisjoint id) (hne : ∀ S ∈ P, S.Nonempty)
    (hbig : n ^ 2 < ∑ S ∈ P, Nat.log 2 ((funResiduals S f).card)) : False :=
  absurd (neciporuk_ceiling f P hdisj hne) (Nat.not_le.mpr hbig)

end PallLean.Paper93.DeepMath.PathB.NeciporukCeilingTotal

#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCeilingTotal.funBoundary_le
#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCeilingTotal.neciporuk_ceiling
#print axioms PallLean.Paper93.DeepMath.PathB.NeciporukCeilingTotal.observer_boundary_not_superpoly
