import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityEval

/-!
# N-Frame: quadratic-monomial detection — the non-affine primitive (Route H core)

Route H (non-affine) design rung.  Route G (§G) proved the affine ceiling `(2+o(1))N`: all
affine detection is `dotp (functional) u`, functionals live in the `v`-dimensional dual, so
distinct detection directions COLLIDE past `v` — the witness-collision cap.  To break it we
need detection directions that do NOT collide at `v`.  Quadratic (degree-2) literals are the
first candidate: monomials `a_i·a_j` live in the `Θ(v²)`-dimensional quadratic space, so up
to `Θ(v²) ≫ N` of them are linearly independent — collision is deferred past `N`.

The non-affine detection primitive, proved here (the analog of `twoPointCount_eq_dotp`):

  `quadMonoCount i j t a₀ u` — the `ZMod 2` two-point count of the quadratic monomial
        `[a_i·a_j = t]` over `{a₀, a₀+u}`.
  `quadMonoCount_eq` — **PROVED, THE PRIMITIVE**:
        `quadMonoCount i j t a₀ u = a₀ i·u j + u i·a₀ j + u i·u j`.
        The two-point detection has a genuine DEGREE-2 term `u_i·u_j` (the escape — a
        quadratic direction that does not collide in the `v`-dim dual) PLUS a base-point
        cross-term `a₀_i·u_j + u_i·a₀_j` (the COST — non-affine detection is NOT
        base-point-independent, unlike the affine primitive).
  `quadMonoCount_origin` — **PROVED**: at base point `0`, detection is exactly `u_i·u_j` —
        value- AND base-point-independent, the clean non-colliding degree-2 direction.
  `quad_directions_distinct` — **PROVED**: distinct index pairs give distinct detection
        functions (non-collision witnessed) — the property affine functionals lacked.

## Honest scope — what this opens and the obstruction it exposes (assessed §H)

The escape is real at the origin: `Θ(v²)` non-colliding degree-2 directions, so detection
rank is NO LONGER capped at `v` — with quadratic literals it is capped only by the input
count `N`, the necessary condition for `(2+c)N`.  The COST is the base-point cross-term: the
two-point rank-completion machinery (rungs 24–29) relied on VALUE/base-point independence
(`heven drops out`), which quadratic detection breaks away from the origin.  So a
`(2+c)N`-strength quadratic family needs a NEW drag built around the origin base-point (or
one that controls the cross-term), and its survival under the concentration/alignment attack
is OPEN.  This primitive is the tool; the family and its concentration analysis are the
undischarged Route-H work.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameQuadDetect

variable {v : ℕ}

/-- The `ZMod 2` two-point count of the quadratic monomial `[a_i·a_j = t]` over the pair
`{a₀, a₀+u}`. -/
def quadMonoCount (i j : Fin v) (t : ZMod 2) (a₀ u : Fin v → ZMod 2) : ZMod 2 :=
  (if a₀ i * a₀ j = t then 1 else 0)
    + (if (a₀ i + u i) * (a₀ j + u j) = t then 1 else 0)

/-- **THE NON-AFFINE DETECTION PRIMITIVE (proved)**: the quadratic two-point detection is a
genuine degree-2 direction `u_i·u_j` plus a base-point cross-term. -/
theorem quadMonoCount_eq (i j : Fin v) (t : ZMod 2) (a₀ u : Fin v → ZMod 2) :
    quadMonoCount i j t a₀ u = a₀ i * u j + u i * a₀ j + u i * u j := by
  unfold quadMonoCount
  have key : ∀ ai aj ui uj t : ZMod 2,
      ((if ai * aj = t then (1 : ZMod 2) else 0)
        + (if (ai + ui) * (aj + uj) = t then 1 else 0))
      = ai * uj + ui * aj + ui * uj := by decide
  exact key (a₀ i) (a₀ j) (u i) (u j) t

/-- **The origin form (proved)**: at base point `0`, quadratic detection is exactly the
non-colliding degree-2 direction `u_i·u_j` — value- and base-point-independent. -/
theorem quadMonoCount_origin (i j : Fin v) (t : ZMod 2) (u : Fin v → ZMod 2) :
    quadMonoCount i j t 0 u = u i * u j := by
  rw [quadMonoCount_eq]
  show (0 : ZMod 2) * u j + u i * 0 + u i * u j = u i * u j
  ring

/-- **The non-collision (proved)**: distinct off-diagonal index pairs give distinct
detection functions — the property affine functionals could not have past dimension `v`. -/
theorem quad_directions_distinct (i j i' j' : Fin v)
    (hij : i ≠ j) (hij' : i' ≠ j') (hne : ({i, j} : Finset (Fin v)) ≠ {i', j'}) :
    ∃ u : Fin v → ZMod 2, u i * u j ≠ u i' * u j' := by
  classical
  have hout : i' ∉ ({i, j} : Finset (Fin v)) ∨ j' ∉ ({i, j} : Finset (Fin v)) := by
    by_contra hc
    push_neg at hc
    obtain ⟨hi', hj'⟩ := hc
    have hsub : ({i', j'} : Finset (Fin v)) ⊆ {i, j} := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi'
      · exact hj'
    have hc1 : ({i, j} : Finset (Fin v)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hij]),
        Finset.card_singleton]
    have hc2 : ({i', j'} : Finset (Fin v)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hij']),
        Finset.card_singleton]
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  refine ⟨fun x => if x ∈ ({i, j} : Finset (Fin v)) then 1 else 0, ?_⟩
  dsimp only
  have hi1 : (if i ∈ ({i, j} : Finset (Fin v)) then (1 : ZMod 2) else 0) = 1 :=
    if_pos (by simp)
  have hj1 : (if j ∈ ({i, j} : Finset (Fin v)) then (1 : ZMod 2) else 0) = 1 :=
    if_pos (by simp)
  rw [hi1, hj1, mul_one]
  rcases hout with h | h
  · rw [if_neg h, zero_mul]
    exact one_ne_zero
  · rw [if_neg h, mul_zero]
    exact one_ne_zero

end PallLean.Paper93.DeepMath.PathB.NFrameQuadDetect

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadDetect.quadMonoCount_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadDetect.quadMonoCount_origin
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameQuadDetect.quad_directions_distinct
