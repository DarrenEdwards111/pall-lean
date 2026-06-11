import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Layer 4 (foundation) — polynomial base change `R → S`

Brick (1) of `SCOPE_LAYER4_MODq_GENERALIZATION.md`.  The Layer-3 degree/agreement side produces an
approximant over `F_p = ZMod p`; the `MOD_q` dimension argument lives over the extension
`F_{p^k} = GaloisField p k` (which contains the `q`-th roots of unity).  To carry the `F_p` approximant
into the extension we use `MvPolynomial.map φ` for a ring hom `φ : F_p → F_{p^k}` (the `algebraMap`), and
need exactly two facts, both **ring-hom-general** (proved here, sorry-free):

* `totalDegree_map_le` — base change does not increase total degree;
* `eval_map_comm` — base change commutes with evaluation along `φ`.

Together these say: if `g` over `F_p` has degree `≤ Δ` and `eval a g = v` on the cube, then `map φ g`
over `F_{p^k}` has degree `≤ Δ` and `eval (φ∘a) (map φ g) = φ v` — so the agreement and degree bounds
transfer to the extension unchanged.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open MvPolynomial

/-- **Base change does not raise total degree.**  For any ring hom `φ : R →+* S`,
`(map φ g).totalDegree ≤ g.totalDegree` (the support can only shrink). -/
theorem totalDegree_map_le {R S σ : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (g : MvPolynomial σ R) : (map φ g).totalDegree ≤ g.totalDegree := by
  simp only [MvPolynomial.totalDegree]
  exact Finset.sup_mono (support_map_subset φ g)

/-- **Base change commutes with evaluation.**  For `φ : R →+* S`, `a : σ → R`,
`eval (φ ∘ a) (map φ g) = φ (eval a g)`.  So an `F_p`-approximant evaluated on the cube transfers to
its `F_{p^k}`-base-change evaluated at the embedded point. -/
theorem eval_map_comm {R S σ : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (a : σ → R)
    (g : MvPolynomial σ R) :
    eval (fun i => φ (a i)) (map φ g) = φ (eval a g) := by
  rw [eval_map]; exact (eval₂_comp φ a g).symm

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.totalDegree_map_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.eval_map_comm
