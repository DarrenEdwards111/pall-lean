import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverBoundary

/-!
# Destructive vs admissible observer boundaries: the permanent, and the N-Frame refinement

## N-Frame Book 1 concept → Lean object

| Book 1 (observer-bounded actualization)                                   | Lean                                             |
|---------------------------------------------------------------------------|--------------------------------------------------|
| observer boundary `b` (finite attention/instrument selecting the context) | `ObserverBoundary` = visible vars + fixed context |
| boundary actualization / collapse (reality seen through the boundary)     | `restrictBoundary B p`                           |
| boundary robustness (structure that survives has real invariant content)  | `spdpRank_restrictBoundary_modqPoly_ge` (`MOD_q`) |
| boundary fragility (apparent structure collapses under the boundary)      | `fullProd_restrictBoundary_zero`, and this file   |

Observer-boundary SPDP formalizes N-Frame *boundary actualization*: the observer selects a computational/contextual
boundary, and SPDP rank measures what algebraic structure survives it.

## The hard-target test and why "admissible" is needed

`…ObserverBoundary` separated `MOD_q` (robust) from `∏Xᵢ` (fragile).  Does the invariant see *hardness*?  Take the
**permanent** `permPoly = ∑_{σ∈Sₙ} ∏ᵢ X_{i,σ(i)}` (`VNP`-complete).  Under an *arbitrary* boundary it is fragile:

  `permPoly_restrictRow_zero` — fixing one row to `0` kills it (every monomial covers that row).

So `BoundarySPDP` over *arbitrary* boundaries is **not** a hardness measure: it is a robustness invariant — it detects a
nonvanishing-product structure (`MOD_q`), not hardness, and a destructive boundary collapses even the hard permanent.

**The N-Frame refinement — admissible boundaries.**  A destructive boundary (zero a whole row) is *not* an admissible
observer context: it destroys the problem/witness (minor) structure.  Restrict to **admissible** boundaries — those
that preserve the minor structure.  Under an admissible (here diagonal/minor-preserving) boundary the permanent
*survives*, reducing to a smaller structured object:

  `permPoly_restrictDiagonal_eq` — fixing the *off-diagonal* to `0` (an admissible, diagonal-preserving boundary)
        reduces the permanent to `∏ᵢ X_{i,i}` — the diagonal product, a nonzero product of `n` distinct variables.
  `permPoly_restrictDiagonal_ne_zero` — hence it is `≠ 0`: the permanent is *robust* under this admissible boundary
        (and `∏ᵢ X_{i,i}` has SPDP rank `≥ C(n,κ)` by the full-product bound).

So the honest picture: `BoundarySPDP` over *arbitrary* boundaries measures robustness, not hardness (the permanent is
fragile); the correct N-Frame object is `BoundarySPDP` over *admissible* (minor-preserving) boundaries, under which the
permanent survives (`Permₙ ↦ scalar · Permₖ`, here the `k = n` diagonal reduction).  Formalising admissibility in
general and the `Permₙ ↦ Permₖ` reduction for `k < n` is the next step toward a hardness-aimed invariant; making a hard
target admissibly-robust *and* proving its rank stays high is the barriered `A3` hard-survival.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

open MvPolynomial

variable {n : ℕ} {F : Type*} [Field F]

/-- The **permanent** as a polynomial in `n²` variables `X_{i,j}` — genuinely hard (`VNP`-complete). -/
noncomputable def permPoly (n : ℕ) (F : Type*) [Field F] : MvPolynomial (Fin n × Fin n) F :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, X (i, σ i)

/-- **Fragile under a destructive boundary (proved).**  Fixing an entire row `a` to `0` kills the permanent, because
every monomial uses an entry from row `a`.  So over *arbitrary* boundaries `BoundarySPDP` is a robustness, not a
hardness, invariant. -/
theorem permPoly_restrictRow_zero (a : Fin n) :
    aeval (fun p : Fin n × Fin n => if p.1 = a then (C 0 : MvPolynomial (Fin n × Fin n) F) else X p)
      (permPoly n F) = 0 := by
  unfold permPoly
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro σ _
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp

/-- **Robust under an admissible boundary (proved).**  Fixing the *off-diagonal* entries to `0` — a diagonal /
minor-preserving observer boundary — reduces the permanent to the diagonal product `∏ᵢ X_{i,i}` (only `σ = id`
survives). -/
theorem permPoly_restrictDiagonal_eq :
    aeval (fun p : Fin n × Fin n => if p.1 = p.2 then X p else (C 0 : MvPolynomial (Fin n × Fin n) F))
      (permPoly n F) = ∏ i, X (i, i) := by
  unfold permPoly
  rw [map_sum, Finset.sum_eq_single (Equiv.refl (Fin n))]
  · rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => by simp)
  · intro σ _ hσ
    rw [map_prod]
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra h; push_neg at h; exact hσ (Equiv.ext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi])
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The permanent survives the admissible boundary (proved).**  Unlike the destructive row-zeroing, the diagonal
boundary leaves a nonzero structured object (`∏ᵢ X_{i,i}`, SPDP rank `≥ C(n,κ)` by the full-product bound). -/
theorem permPoly_restrictDiagonal_ne_zero [Nontrivial F] :
    aeval (fun p : Fin n × Fin n => if p.1 = p.2 then X p else (C 0 : MvPolynomial (Fin n × Fin n) F))
      (permPoly n F) ≠ 0 := by
  rw [permPoly_restrictDiagonal_eq]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => X_ne_zero _)

end PallLean.Paper93.DeepMath.PathB.SPDPLowerBound

#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.permPoly_restrictRow_zero
#print axioms PallLean.Paper93.DeepMath.PathB.SPDPLowerBound.permPoly_restrictDiagonal_ne_zero
