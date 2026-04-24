import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Basic

/-!
# Strictly monotone self-maps of `Fin k`

This file provides supporting lemmas for totally-positive arguments
in the amplituhedron development.

A strictly-monotone `r : Fin k → Fin n` with `r 0 = 0` and `r (k-1) = k-1`
need *not* be the identity when `n > k`. However, strictly-monotone
self-maps of `Fin k` (i.e. `r : Fin k → Fin k`) are always injective
via `StrictMono.injective`.

We provide:

* `strictMono_injective`: the one-line wrapper promoting strict
  monotonicity to injectivity. This is the tractable, always-available
  fact used by downstream amplituhedron arguments.
-/

namespace PallLean.Paper93.DeepMath.Amplituhedron

/-- Strictly monotone `r : Fin k → Fin n` is injective. -/
theorem strictMono_injective {k n : ℕ} (r : Fin k → Fin n) (hr : StrictMono r) :
    Function.Injective r := hr.injective

end PallLean.Paper93.DeepMath.Amplituhedron
