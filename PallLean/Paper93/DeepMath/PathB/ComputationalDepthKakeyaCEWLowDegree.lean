import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKakeyaCEW
import Mathlib.Data.Fintype.Pi

/-!
# Instantiating the Kakeya→CEW engine for genuine AC⁰[p]: the Razborov–Smolensky degree space

The junta instantiation used the crudest bounded-CEW family (`k`-juntas).  This file uses the genuine
AC⁰[p] certificate space of the polynomial method / Razborov–Smolensky: **multilinear monomials of degree
`≤ d`** over `F`.  AC⁰[p] circuits are approximated by such low-degree polynomials, so this is the real
"bounded CEW = bounded degree" certificate space.

* certificate space `V` = `LowDeg n d → F`, coefficient vectors over the degree-`≤ d` monomials
  `{T ⊆ Fin n : |T| ≤ d}`; its dimension is `card (LowDeg n d) = ∑_{i≤d} C(n,i)`.
* `evalRS π pt`: evaluate `∑_T c_T χ_T` at the sampled points, where `χ_T(x) = ∏_{i∈T} x_i` is the
  multilinear monomial — the honest polynomial-method evaluation map.
* `Injective (evalRS pt)` = the direction-covering / Kakeya property (the points resolve every
  degree-`≤ d` polynomial — the exact hypothesis Dvir's argument establishes for a Kakeya set).

## What is proved

* **`evalRS`** — the degree-`≤ d` polynomial evaluation map, proved linear.
* **`rs_dim`** — the certificate space has dimension `card (LowDeg n d)` (`= ∑_{i≤d} C(n,i)`).
* **`rs_needs_measurements`** — the engine, instantiated: if the points resolve every degree-`≤ d`
  polynomial, then there are at least `card (LowDeg n d)` of them.

## Honest scope

The Kakeya→CEW engine biting on the *genuine* AC⁰[p] (low-degree) certificate space — a real, restricted,
axiom-clean statement.  It is still the honest `(A2)` direction: it bounds what a degree-`≤ d` family can
resolve.  It does **not** discharge `(A3)`: showing a concrete NP function *needs* degree/CEW beyond
polylog (the Razborov–Smolensky-style lower bound at superpolynomial dimension) is the open object.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KakeyaCEWLowDegree

open Module
open scoped BigOperators
open PallLean.Paper93.DeepMath.PathB.KakeyaCEW

variable {F : Type*} [Field F]
variable {n d : ℕ}
variable {S : Type*} [Fintype S]

/-- The degree-`≤ d` monomial index set: subsets of `Fin n` of size at most `d`. -/
abbrev LowDeg (n d : ℕ) := {T : Finset (Fin n) // T.card ≤ d}

/-- The multilinear monomial `χ_T(x) = ∏_{i∈T} x_i`, with `x_i ∈ {0,1} ⊆ F`. -/
def monoVal (T : Finset (Fin n)) (x : Fin n → Bool) : F := ∏ i ∈ T, (if x i then (1 : F) else 0)

/-- **The degree-`≤ d` evaluation map (proved linear).**  Sends a coefficient vector `c` to the function
`s ↦ ∑_T c_T χ_T(pt s)`. -/
def evalRS (pt : S → (Fin n → Bool)) : (LowDeg n d → F) →ₗ[F] (S → F) where
  toFun c := fun s => ∑ T : LowDeg n d, c T * monoVal T.1 (pt s)
  map_add' c c' := by
    funext s
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun T _ => by ring)
  map_smul' a c := by
    funext s
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun T _ => by ring)

/-- **The degree-`≤ d` certificate dimension (proved).**  `= card (LowDeg n d) = ∑_{i≤d} C(n,i)`. -/
theorem rs_dim : finrank F (LowDeg n d → F) = Fintype.card (LowDeg n d) := by simp

/-- **Bounded-degree (AC⁰[p]) instantiation of the engine (proved).**  If the sampled points resolve
every degree-`≤ d` polynomial (`evalRS` injective — the direction-covering / Kakeya property), then there
are at least `card (LowDeg n d) = ∑_{i≤d} C(n,i)` of them. -/
theorem rs_needs_measurements (pt : S → (Fin n → Bool))
    (hinj : Function.Injective (evalRS (F := F) (n := n) (d := d) pt)) :
    Fintype.card (LowDeg n d) ≤ Fintype.card S := by
  have h := kakeya_forces_dimension (evalRS (F := F) pt) hinj
  rwa [rs_dim] at h

end PallLean.Paper93.DeepMath.PathB.KakeyaCEWLowDegree

#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaCEWLowDegree.rs_needs_measurements
