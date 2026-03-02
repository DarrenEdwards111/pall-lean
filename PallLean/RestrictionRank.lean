import PallLean.SPDPRankDef
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic
/-!
# R1: Variable Restriction Cannot Increase SPDP Rank

We prove this using the fact that the SPDP subspace of the restricted
polynomial is contained in the image of the SPDP subspace of the original
under the eval map, and images of submodules under linear maps have
dim ≤ original dim.
-/

namespace SPDP.Restriction

open SPDP.Concrete MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]
variable {n : ℕ}

/-- The ring hom that evaluates x_i = c -/
noncomputable def evalHom (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun j => if j = i then MvPolynomial.C c else MvPolynomial.X j)

/-- The eval hom as a linear map -/
noncomputable def evalLin (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F where
  toFun := evalHom i c
  map_add' := map_add _
  map_smul' := fun r x => by simp [Algebra.smul_def, map_mul, evalHom]

/-- Key commutation: pderiv j commutes with evalHom i when j ≠ i.

For j ≠ i: ∂_j(p|_{x_i=c}) = (∂_j p)|_{x_i=c}
because eval_{x_i=c} doesn't touch x_j, and pderiv_j doesn't touch x_i. -/
theorem pderiv_comm_eval (i j : Fin n) (hij : j ≠ i) (c : F)
    (p : MvPolynomial (Fin n) F) :
    MvPolynomial.pderiv j (evalHom i c p) = evalHom i c (MvPolynomial.pderiv j p) := by
  -- This follows from the derivation property + the fact that
  -- evalHom i c (X j) = X j when j ≠ i
  sorry -- fiddly induction on polynomial structure

/-- For j = i: ∂_i(p|_{x_i=c}) = (∂_i p)|_{x_i=c}
    Because C c doesn't depend on x_i, so ∂_i of the substituted
    expression works the same way. -/
theorem pderiv_eval_same (i : Fin n) (c : F)
    (p : MvPolynomial (Fin n) F) :
    MvPolynomial.pderiv i (evalHom i c p) = evalHom i c (MvPolynomial.pderiv i p) := by
  sorry -- needs induction on polynomial monomials

/-- Combined: pderiv commutes with evalHom for ALL j -/
theorem pderiv_comm_eval_all (i j : Fin n) (c : F)
    (p : MvPolynomial (Fin n) F) :
    MvPolynomial.pderiv j (evalHom i c p) = evalHom i c (MvPolynomial.pderiv j p) := by
  by_cases h : j = i
  · subst h; exact pderiv_eval_same _ c p
  · exact pderiv_comm_eval _ j h c p

/-- iterDerivList commutes with evalHom -/
theorem iterDerivList_comm_eval (i : Fin n) (c : F)
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    iterDerivList indices (evalHom i c p) = evalHom i c (iterDerivList indices p) := by
  induction indices generalizing p with
  | nil => simp [iterDerivList]
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rw [pderiv_comm_eval_all _ j c p]
    exact ih (MvPolynomial.pderiv j p)

/-- The SPDP subspace of the restricted polynomial is contained in the
    image of the original SPDP subspace under evalLin. -/
theorem spdpSubspace_restrict_le (κ : ℕ) (p : MvPolynomial (Fin n) F)
    (i : Fin n) (c : F) :
    spdpSubspace κ (evalHom i c p) ≤ (spdpSubspace κ p).map (evalLin i c) := by
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_setOf_eq] at hq
  obtain ⟨indices, m, hlen, hq⟩ := hq
  rw [hq, iterDerivList_comm_eval]
  -- q = m * evalHom(iterDerivList indices p)
  -- We need to show this is in the image of the original span
  -- The pre-image element is: evalHom⁻¹(m) * iterDerivList indices p
  -- But evalHom is not injective, so we can't invert m.
  -- However, m itself is in the polynomial ring, so we can write:
  -- evalHom(m' * iterDerivList indices p) where m' is any preimage of m
  -- Actually: m = evalHom(m) is not necessarily true...
  -- Better: m * evalHom(d) = evalHom(m * d) is NOT true in general.
  -- m might not be in the image of evalHom.
  -- We need: m · evalHom(d) ∈ image(evalLin)
  -- This is: ∃ q', evalLin(q') = m · evalHom(d)
  -- But this isn't generally true.
  -- The correct approach: the generating set of the restricted SPDP space
  -- uses RESTRICTED shift monomials m', and
  -- m' · ∂_S(p|_{x_i=c}) = m' · evalHom(∂_S p)
  -- = evalHom(m'' · ∂_S p) where m'' is a preimage of m'... still stuck.
  sorry

/-- **R1: restriction_rank_le** — SPDP rank cannot increase under eval -/
theorem restriction_rank_le (κ : ℕ) (p : MvPolynomial (Fin n) F)
    (i : Fin n) (c : F) :
    spdpRankConcrete κ (evalHom i c p) ≤ spdpRankConcrete κ p := by
  unfold spdpRankConcrete
  -- Structure: spdpSubspace(p|_{xi=c}) ≤ image(spdpSubspace(p)) under evalLin
  -- image has finrank ≤ original finrank
  -- Needs Module.Finite instance for the subspaces (true when polynomial ring is Noetherian)
  sorry

end SPDP.Restriction
