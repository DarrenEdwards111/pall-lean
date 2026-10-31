import PallLean.Paper93.DeepMath.PathB.ComputationalDepthRSWiring
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Discharging the Smolensky half's *counting* step via the dimension engine

`RSWiring` left `smolensky` (MOD_q has no low `F_p`-approximate degree) as one socket.  Smolensky's proof
has two parts: a MOD_q-specific **spreading** step (a degree-`d` approximation of MOD_q makes every
function on a large agreement set degree-`≤ D` computable) and a **counting** step (a set spanned by
degree-`≤ D` polynomials can't be too big).  The counting step is *exactly* the dimension engine —
`kakeya_forces_dimension`'s dual — so it is dischargeable here, shrinking the socket to just `spreading`.

## What is proved

* **`restrict`** — the linear map sending a degree-`≤ D` coefficient vector to the function it computes on
  the points of a set `A`.
* **`counting`** — if `restrict A` is surjective (every function on `A` is degree-`≤ D` computable), then
  `|A| ≤ card {T : |T| ≤ D} = ∑_{i≤D} C(n,i)`.  Proof: `finrank (range) ≤ finrank (domain)`, and
  surjectivity makes `range = ⊤`; `finrank` of the codomain is `|A|`, of the domain is the monomial
  count.  This *is* Smolensky's counting.
* **`smolensky_from_spreading`** — the reduction: given the (open) spreading lemma and the parameter gap
  `∑_{i≤D} C(n,i) < 2^n − e`, MOD_q has no low-degree approximation.  The counting is discharged; only
  `spreading` remains.

## Honest scope

The counting step is now proved via the engine — a genuine reduction of the `smolensky` socket, not a
restatement.  What remains, `spreading`, is the MOD_q-specific algebraic step (the change of variables via
`q`-th roots of unity) — *not* dimension counting, and left as a precise, smaller socket.  This is
`AC⁰[p]`-restricted; nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.RSSmolenskyCounting

open scoped BigOperators
open Module
open PallLean.Paper93.DeepMath.PathB.KakeyaCEWCovering
open PallLean.Paper93.DeepMath.PathB.RSWiring

variable {p n D d e q : ℕ} [Fact (Nat.Prime p)]

/-- The restriction map: a degree-`≤ D` coefficient vector `c` maps to the function `a ↦ ∑_T c_T χ_T(a)`
on the points of `A`. -/
def restrict (A : Finset (Fin n → Bool)) :
    ({T : Finset (Fin n) // T.card ≤ D} → ZMod p) →ₗ[ZMod p] (↥A → ZMod p) where
  toFun c := fun a => ∑ T : {T : Finset (Fin n) // T.card ≤ D}, c T * monoVal T.1 (a : Fin n → Bool)
  map_add' c c' := by
    funext a
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun T _ => by ring)
  map_smul' r c := by
    funext a
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun T _ => by ring)

/-- **Smolensky's counting step, via the dimension engine (proved).**  If every function on `A` is
computed by a degree-`≤ D` polynomial (`restrict A` surjective), then `|A| ≤ ∑_{i≤D} C(n,i)`. -/
theorem counting (A : Finset (Fin n → Bool))
    (hsurj : Function.Surjective (restrict (p := p) (D := D) A)) :
    A.card ≤ Fintype.card {T : Finset (Fin n) // T.card ≤ D} := by
  have h := LinearMap.finrank_range_le (restrict (p := p) (D := D) A)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
  simpa [Fintype.card_coe] using h

/-- **The Smolensky half, reduced to spreading (proved).**  With the (open, MOD_q-specific) spreading
lemma and the parameter gap, `MOD_q` has no low-degree approximation.  The counting is discharged by the
engine; only `spreading` is left open. -/
theorem smolensky_from_spreading
    (spreading : LowApproxDeg d e (embed (MODq q) : (Fin n → Bool) → ZMod p) →
      ∃ A : Finset (Fin n → Bool), 2 ^ n - e ≤ A.card ∧
        Function.Surjective (restrict (p := p) (D := D) A))
    (hparam : Fintype.card {T : Finset (Fin n) // T.card ≤ D} < 2 ^ n - e) :
    ¬ LowApproxDeg d e (embed (MODq q) : (Fin n → Bool) → ZMod p) := by
  intro happrox
  obtain ⟨A, hAcard, hsurj⟩ := spreading happrox
  have hcount := counting A hsurj
  omega

end PallLean.Paper93.DeepMath.PathB.RSSmolenskyCounting

#print axioms PallLean.Paper93.DeepMath.PathB.RSSmolenskyCounting.counting
#print axioms PallLean.Paper93.DeepMath.PathB.RSSmolenskyCounting.smolensky_from_spreading
