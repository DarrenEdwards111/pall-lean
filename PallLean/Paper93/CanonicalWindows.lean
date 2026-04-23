/-
# Paper §9.3.1 — Canonical κ-derivative windows

Paper reference: §9.3.1 "Canonicalization map and row-span preservation".

A κ-derivative *window* (paper's `Win_κ`) is a length-κ sequence of
block-admissible derivative/shift steps used in the Width⇒Rank analysis.
In the compiled/radius-1 regime each such step is determined by

  * a *block index* (which block of the fixed block partition B the step
    acts on), and
  * a *local operation* (the interface-local symbol τ ∈ Σ that this step
    applies — identified via the local action `A_τ` from Lemma 24).

Hence a window of size κ is precisely a vector of κ pairs
`(BlockIdx × LocalOp)`, which is exactly the finite combinatorial object
counted in the paper's §9.3.1 calculus.

This file defines the kernel-only type `Win κ BlockIdx LocalOp` and
records the `Fintype` instance inherited from `Fintype` on the index and
operation types, without depending on any other module under
`PallLean/Paper93/` (those are being introduced in parallel).
-/

import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Prod

namespace PallLean
namespace Paper93

open List

/--
**Paper §9.3.1, Definition 20 (κ-derivative window).**

A window of size `κ` over a block alphabet `BlockIdx` and local-operation
alphabet `LocalOp` is a length-`κ` sequence of `(block index, local
operation)` pairs. This is the block-admissible, compiled/radius-1
presentation used by the paper's Width⇒Rank analysis and the
canonicalization map `can : Winκ → Winκ`.

We implement it as `List.Vector (BlockIdx × LocalOp) κ` — a length-indexed
list — which is the standard finite-combinatorial model of a fixed-length
sequence in mathlib and inherits a `Fintype` instance whenever
`BlockIdx` and `LocalOp` are finite.
-/
abbrev Win (κ : ℕ) (BlockIdx LocalOp : Type) : Type :=
  List.Vector (BlockIdx × LocalOp) κ

/--
**Paper §9.3.1 corollary.** `Win κ BlockIdx LocalOp` is finite whenever
the block index set and the local-operation alphabet are finite. This
is the finiteness property used to make the histogram/profile count in
Definition 21 well-defined.

The instance unfolds `Win` and defers to the `Fintype` instance on
`List.Vector (BlockIdx × LocalOp) κ`, itself obtained from
`Mathlib.Data.Fintype.Vector` via `Fintype.ofEquiv` and
`Equiv.vectorEquivFin`.
-/
instance instFintypeWin
    {κ : ℕ} {BlockIdx LocalOp : Type}
    [Fintype BlockIdx] [Fintype LocalOp] :
    Fintype (Win κ BlockIdx LocalOp) :=
  inferInstanceAs (Fintype (List.Vector (BlockIdx × LocalOp) κ))

/--
Convenience constructor: the empty (length-0) window. Mirrors the
paper's boundary case `κ = 0`.
-/
def Win.nil {BlockIdx LocalOp : Type} : Win 0 BlockIdx LocalOp :=
  List.Vector.nil

/--
Convenience destructor: extract the length-`κ` list of
`(block, local-op)` pairs underlying a window. This is the
representation used in the paper's canonicalization algorithm
(steps P6 and P7 operate on this list).
-/
def Win.steps {κ : ℕ} {BlockIdx LocalOp : Type}
    (w : Win κ BlockIdx LocalOp) : List (BlockIdx × LocalOp) :=
  List.Vector.toList w

@[simp]
theorem Win.steps_length {κ : ℕ} {BlockIdx LocalOp : Type}
    (w : Win κ BlockIdx LocalOp) : (Win.steps w).length = κ := by
  unfold Win.steps
  exact w.toList_length

end Paper93
end PallLean
