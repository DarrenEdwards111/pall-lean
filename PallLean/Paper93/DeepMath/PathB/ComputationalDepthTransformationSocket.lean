import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResistanceProof

/-!
# The transformation, as a socket to the resistance measure

The Flatland/relativity analysis left the missing piece named but not built: the **transformation** — the
Lorentz-analog / exact dictionary that reads `cbudget`'s value off the tower's structure.  This file
formalizes it as a **socket**, wired to the resistance measure, so the whole separation becomes one clean
conditional.

The separation splits into an easy half and a hard half:

* **the lens** — a measure `μ` with `μ ≤ cbudget`.  This is the *shadow reader*: a valid lower bound.
  Easy — many exist (formal complexity measures, KW communication complexity, …).
* **the transformation** — the certificate that `μ` **survives composition** on the SAT tower:
  `μ(T₍d+1₎) ≥ 2·μ(Tₐ)`, with nonzero base.  This is the *frame-transformation* — the hard half, the
  KRW-style step.  Named here as the socket.

## What is proved

* **`transformation_gives_resistance`** — lens + transformation assemble into a `ResistanceMeasure`.
* **`transformation_separates`** — hence `2^d ≤ cbudget(Tₐ)`: **discharging the transformation socket
  (given any lens) IS proving the separation.**

So the transformation is exactly the missing map: with it, the P-observer's shadow (`μ`) transforms into
the true value (`cbudget ≥ 2^d`); without it, the shadow stays lossy.  It plays the role Lorentz plays in
relativity — the transform that makes the frames agree — and it is the one thing not supplied.

## Honest scope

The socket `Transformation` is **unproven** — it is the open bound (the KRW conjecture / `cost_super`).
Naming it and wiring it does not discharge it; the file is a conditional, `Transformation ⟹ P ≠ NP` (given
a lens), in the shape of the Williams cash-out.  The known lenses for which the transformation is provable
cap polynomially (Khrapchenko `n²`, shrinkage `n³`).  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TransformationSocket

open PallLean.Paper93.DeepMath.PathB.ResistanceProof

/-- **The transformation socket.**  The missing frame-transformation: a certificate that the lens `μ`
**survives composition** on the SAT tower — `μ(T₍d+1₎) ≥ 2·μ(Tₐ)`, with nonzero base.  This is the
Lorentz-analog / exact dictionary that reads the doubling off the tower's structure; it is the KRW-style
step, named as a socket. -/
structure Transformation (Fn : Type) (mu : Fn → ℕ) (T : ℕ → Fn) where
  /-- `μ` survives composition: it doubles through the tower. -/
  survives_composition : ∀ d, 2 * mu (T d) ≤ mu (T (d + 1))
  /-- nonzero base. -/
  base : 1 ≤ mu (T 0)

/-- **The transformation gives the resistance measure (proved).**  A lens (`μ ≤ cbudget`, the shadow
reader — the easy half) together with the transformation socket assemble into a `ResistanceMeasure`. -/
def transformation_gives_resistance {Fn : Type} {cbudget : Fn → ℕ} {T : ℕ → Fn} {mu : Fn → ℕ}
    (lens : ∀ f, mu f ≤ cbudget f) (tr : Transformation Fn mu T) :
    ResistanceMeasure Fn cbudget T where
  mu := mu
  lower_bound := lens
  superadditive := tr.survives_composition
  base := tr.base

/-- **The transformation cashes out to the separation (proved).**  Given a lens and the transformation
socket, `2^d ≤ cbudget(Tₐ)` — SAT resists.  The shadow `μ` has been transformed into the true value.
Discharging the socket **is** proving `P ≠ NP` (given any lens). -/
theorem transformation_separates {Fn : Type} {cbudget : Fn → ℕ} {T : ℕ → Fn} {mu : Fn → ℕ}
    (lens : ∀ f, mu f ≤ cbudget f) (tr : Transformation Fn mu T) (d : ℕ) :
    2 ^ d ≤ cbudget (T d) :=
  resistance_measure_separates (transformation_gives_resistance lens tr) d

end PallLean.Paper93.DeepMath.PathB.TransformationSocket

#print axioms PallLean.Paper93.DeepMath.PathB.TransformationSocket.transformation_gives_resistance
#print axioms PallLean.Paper93.DeepMath.PathB.TransformationSocket.transformation_separates
