import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKakeyaCEW

/-!
# The `(A3)` socket: instantiating the engine for an NP family at superpolynomial dimension

The junta and low-degree instantiations bit on *bounded*-CEW families, where the dimension is small.
This file states what instantiating the Kakeya→CEW engine for an **NP family** would require, and proves
the implication down to the one open object — exactly `book1`'s axiom `(A3)`.

The setup is a family `n ↦ (V n, Sf n, E n)`: `V n` the certificate space of the NP family at input
length `n`, `Sf n` the available measurements (the polynomial "width"), `E n` the evaluation map.  The
**direction-covering hypothesis** `covering : ∀ n, Injective (E n)` — that the NP family genuinely needs
all directions — is book1's `(A3)`, and it is left **open**: this file never discharges it.

## What is proved (everything *around* the socket)

* **`width_forced`** — from `covering`, the engine forces `finrank F (V n) ≤ card (Sf n)` for all `n`.
* **`superpoly_not_polyBounded`** — if `D` is superpolynomial and `D ≤ w` pointwise, then `w` is not
  polynomially bounded.
* **`separation_from_A3`** — the conditional separation: if the NP family is direction-covering
  (`covering`, the open `(A3)`) at **superpolynomial** certificate dimension, then **no polynomial width
  resolves it** — the measurements must be superpolynomial.

## Honest scope — the socket is open, on purpose

`separation_from_A3` takes `covering` as a hypothesis and never proves it.  Discharging it for a concrete
NP family (SAT/permanent) at superpolynomial `finrank F (V n)` is a **circuit lower bound** — book1's
`(A3)`, `cost_super`, SAT incompressible off `Π★`, the wall.  Everything *else* in the chain (the engine,
this reduction) is machine-checked and axiom-clean.  Nothing here is `P ≠ NP`; the open object is named
precisely and left standing.
-/

namespace PallLean.Paper93.DeepMath.PathB.KakeyaCEWA3

open Module
open PallLean.Paper93.DeepMath.PathB.KakeyaCEW

variable {F : Type*} [Field F]
variable (V : ℕ → Type*) [∀ n, AddCommGroup (V n)] [∀ n, Module F (V n)]
  [∀ n, FiniteDimensional F (V n)]
variable (Sf : ℕ → Type*) [∀ n, Fintype (Sf n)]
variable (E : ∀ n, V n →ₗ[F] (Sf n → F))

/-- Superpolynomial growth. -/
def Superpoly (D : ℕ → ℕ) : Prop := ∀ c k : ℕ, ∃ n, c * (n + 1) ^ k < D n

/-- Polynomial boundedness. -/
def PolyBounded (w : ℕ → ℕ) : Prop := ∃ c k : ℕ, ∀ n, w n ≤ c * (n + 1) ^ k

/-- **The engine, applied per input length (proved).**  Direction-covering forces the width to be at
least the certificate dimension at every `n`. -/
theorem width_forced (covering : ∀ n, Function.Injective (E n)) :
    ∀ n, finrank F (V n) ≤ Fintype.card (Sf n) :=
  fun n => kakeya_forces_dimension (E n) (covering n)

/-- **Superpolynomial dimension defeats any polynomial width (proved).** -/
theorem superpoly_not_polyBounded {D w : ℕ → ℕ} (hle : ∀ n, D n ≤ w n) (hD : Superpoly D) :
    ¬ PolyBounded w := by
  rintro ⟨c, k, hw⟩
  obtain ⟨n, hn⟩ := hD c k
  exact absurd (hn.trans_le ((hle n).trans (hw n))) (lt_irrefl _)

/-- **The conditional separation from `(A3)` (proved).**  If the NP family is direction-covering
(`covering` — the open `(A3)`) at superpolynomial certificate dimension, then no polynomial width
resolves it.  The `covering` hypothesis is exactly book1's `(A3)` and is **not** discharged here. -/
theorem separation_from_A3 (covering : ∀ n, Function.Injective (E n))
    (hD : Superpoly (fun n => finrank F (V n))) :
    ¬ PolyBounded (fun n => Fintype.card (Sf n)) :=
  superpoly_not_polyBounded (width_forced V Sf E covering) hD

end PallLean.Paper93.DeepMath.PathB.KakeyaCEWA3

#print axioms PallLean.Paper93.DeepMath.PathB.KakeyaCEWA3.separation_from_A3
