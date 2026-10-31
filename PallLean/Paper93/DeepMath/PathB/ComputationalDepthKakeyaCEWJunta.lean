import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKakeyaCEW
import Mathlib.Data.Fintype.Pi

/-!
# Instantiating the Kakeya→CEW engine for a bounded-CEW AC⁰ family (k-juntas)

`ComputationalDepthKakeyaCEW` proved the schema `kakeya_forces_dimension : Injective E → finrank F V ≤
card S`.  This file turns it from a schema into a concrete restricted lower bound by instantiating the
certificate space `V` and the measurement map `E` for the **simplest bounded-CEW fragment of AC⁰**:
`k`-juntas — functions that depend on only `k` of the `n` inputs (contextual width `= k`).

The certificate space of a CEW-`k` family is `(Fin k → Bool) → F` — all functions of the `k` relevant
coordinates — and its dimension is exactly `2^k`.  The measurement map `evalJunta π pt` evaluates a
certificate at the sampled points `pt`, read through the `k` relevant coordinates `π`.  Injectivity of
`evalJunta` is the direction-covering / Kakeya property (the measurements resolve every certificate), and
the engine converts it into the concrete bound `2^k ≤ card S`.

## What is proved

* **`junta_dim`** — the CEW-`k` certificate space has dimension `2^k`.
* **`junta_needs_measurements`** — the engine, instantiated: if point-evaluation of a `k`-junta family is
  direction-covering, then at least `2^k` measurements are required.

## Honest scope

This is the engine *biting* on a concrete bounded-CEW family — a real, restricted, axiom-clean
measurement/covering lower bound (the honest `(A2)` direction: bounded CEW ⇒ bounded dimension ⇒ bounded
resolving power).  `k`-juntas are the simplest such fragment (a sub-family of AC⁰); the same engine with
the degree-`≤ d` Razborov–Smolensky certificate space gives the general AC⁰ picture, with `2^k` replaced
by `∑_{i≤d} C(n,i)`.  What none of this does is discharge `(A3)`: exhibiting a concrete function *outside*
the bounded-CEW family (a separation) is the open circuit lower bound.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KakeyaCEWJunta

open Module
open PallLean.Paper93.DeepMath.PathB.KakeyaCEW

variable {F : Type*} [Field F]
variable {n k : ℕ}
variable {S : Type*} [Fintype S]

/-- The CEW-`k` certificate space: all functions of the `k` relevant Boolean coordinates. -/
abbrev JuntaCert (F : Type*) (k : ℕ) := (Fin k → Bool) → F

/-- **The evaluation map of a `k`-junta family.**  A certificate `g` is measured at each sampled point
`pt s`, read through the `k` relevant coordinates chosen by `π`.  Linear in `g`. -/
def evalJunta (π : Fin k → Fin n) (pt : S → (Fin n → Bool)) :
    JuntaCert F k →ₗ[F] (S → F) where
  toFun g := fun s => g (fun i => pt s (π i))
  map_add' g h := by funext s; rfl
  map_smul' c g := by funext s; rfl

/-- **The CEW-`k` dimension is `2^k` (proved).** -/
theorem junta_dim : finrank F (JuntaCert F k) = 2 ^ k := by
  have h : finrank F (JuntaCert F k) = Fintype.card (Fin k → Bool) := by simp [JuntaCert]
  rw [h, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **Bounded-CEW (junta) instantiation of the engine (proved).**  If point-evaluation of a `k`-junta
family is direction-covering (`evalJunta` injective), then resolving it costs at least `2^k`
measurements.  A concrete restricted CEW lower bound, out of the Kakeya→CEW engine. -/
theorem junta_needs_measurements (π : Fin k → Fin n) (pt : S → (Fin n → Bool))
    (hinj : Function.Injective (evalJunta (F := F) π pt)) :
    2 ^ k ≤ Fintype.card S := by
  have h := kakeya_forces_dimension (evalJunta (F := F) π pt) hinj
  rwa [junta_dim] at h

end PallLean.Paper93.DeepMath.PathB.KakeyaCEWJunta

#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaCEWJunta.junta_needs_measurements
