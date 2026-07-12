import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDimensionRestrictionObserver

/-!
# The honest capstone: residual-span rank ≤ 2^|S|, so the unrestricted min collapses

`DimensionFullRank` gave the *lower* side (equality has full rank `2^|S|` on a structured block).  This file
gives the matching *upper* side, closing the dimension-observer story honestly:

* `dimResiduals_empty_le` — the empty cut has rank `≤ 1` (its residuals are all constant).
* `dimResiduals_le_two_pow` — every cut `S` has rank `≤ 2^{|S|}` (iterate the halve calculus from the empty base).
* `dimResiduals_singleton_le` — a single-variable cut has rank `≤ 2`.

Together with `DimensionFullRank.eqFun_dim_ge` (rank `= 2^k` on a structured `k`-block) this makes the collapse
explicit: the **minimum over *all* decompositions is `≤ 1`** (achieved by the empty cut), while a structured cut
reaches `2^k`.  So — exactly as for the log observer (`BlockDecompositionMinGap`) — the super-log dimension bound
is a property of the *structured class*; the unrestricted min is trivial.  This is the dimension analogue of the
decomposition gap, and it is why the observer machinery cannot, on its own, force a bound over every real
polynomial-time SAT decider: the missing quantifier (machine-completeness) is not supplied by any single
observer, cut, or representation.

## Honest scope

The upper half of the residual-span dimension, closing the restricted-vs-unrestricted picture.  It proves the
*collapse* of the unrestricted min — a no-go, not a lower bound.  No separation.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DimensionUpperBound

open PallLean.Paper93.DeepMath.PathB.DimensionRestrictionObserver

variable {K : Type*} [Field K] {n : ℕ}

/-- **The empty cut has rank `≤ 1`.**  With no free variables, every residual is the constant `f α`, so the
residual span lies in the line spanned by the constant-`1` function. -/
theorem dimResiduals_empty_le (f : (Fin n → Bool) → K) : dimResiduals (∅ : Finset (Fin n)) f ≤ 1 := by
  classical
  haveI : FiniteDimensional K ((Fin n → Bool) → K) := inferInstance
  rw [dimResiduals_eq]
  have hsub : resSpan (∅ : Finset (Fin n)) f
      ≤ Submodule.span K {(fun _ => 1 : (Fin n → Bool) → K)} := by
    rw [resSpan, Submodule.span_le]
    rintro _ ⟨α, rfl⟩
    have hconst : resVec (∅ : Finset (Fin n)) f α = (f α) • (fun _ => (1 : K)) := by
      funext x
      simp [resVec]
    rw [hconst]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  calc Module.finrank K (resSpan (∅ : Finset (Fin n)) f)
      ≤ Module.finrank K (Submodule.span K {(fun _ => 1 : (Fin n → Bool) → K)}) :=
        Submodule.finrank_mono hsub
    _ ≤ ({(fun _ => 1 : (Fin n → Bool) → K)} : Finset _).card := by
        rw [← Set.toFinset_singleton]; exact finrank_span_le_card _
    _ = 1 := Finset.card_singleton _

/-- **Every cut has rank `≤ 2^{|S|}`.**  Iterate the linear halve from the empty base. -/
theorem dimResiduals_le_two_pow (S : Finset (Fin n)) (f : (Fin n → Bool) → K) :
    dimResiduals S f ≤ 2 ^ S.card := by
  have h := dimResiduals_union_le (∅ : Finset (Fin n)) S f
  rw [Finset.empty_union] at h
  calc dimResiduals S f ≤ 2 ^ S.card * dimResiduals (∅ : Finset (Fin n)) f := h
    _ ≤ 2 ^ S.card * 1 := by gcongr; exact dimResiduals_empty_le f
    _ = 2 ^ S.card := mul_one _

/-- **A single-variable cut has rank `≤ 2`.** -/
theorem dimResiduals_singleton_le (v : Fin n) (f : (Fin n → Bool) → K) :
    dimResiduals ({v} : Finset (Fin n)) f ≤ 2 := by
  have := dimResiduals_le_two_pow ({v} : Finset (Fin n)) f
  simpa using this

/-- **The unrestricted min collapses.**  For every function, some decomposition (the empty cut) has residual-span
rank `≤ 1` — so the minimum over *all* decompositions is trivial, no matter how hard the function.  The
super-log dimension bound (`DimensionFullRank.eqFun_dim_ge`) is a property of the structured class only. -/
theorem unrestricted_min_trivial (f : (Fin n → Bool) → K) :
    ∃ S : Finset (Fin n), dimResiduals S f ≤ 1 :=
  ⟨∅, dimResiduals_empty_le f⟩

end PallLean.Paper93.DeepMath.PathB.DimensionUpperBound

#print axioms PallLean.Paper93.DeepMath.PathB.DimensionUpperBound.dimResiduals_le_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.DimensionUpperBound.unrestricted_min_trivial
