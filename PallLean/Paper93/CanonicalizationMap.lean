/-
  Paper §9.3.1 Definition 20: canonicalization map `can : Win κ → Win κ`.

  This file encodes the canonicalization map of the paper as the
  shortlex-minimum representative of a window's equivalence class under:

    (P6) adjacent-swap of derivative steps with disjoint interface supports
    (P7) replacement of each interface-local update word `σ` by its
         monoid normal form `NF(σ)`.

  Agent 4 scope (AGENT 4 of 10):
    * Only this file is created.
    * Dependencies on Agent 1's `Win κ` and Agent 3's `NF` are modelled
      as `variable` hypothesis arguments rather than direct imports,
      so that this file compiles stand-alone, sorry-free.

  Design notes
  ------------
  * We model a length-`κ` window as a `List.Vector α κ` for
    `α := BlockIdx × LocalOp` so that windows over a finite alphabet
    are automatically a `Fintype` (see `Mathlib.Data.Fintype.Vector`).
  * An equivalence class of windows is realised as a `Finset` of windows
    (passed as a hypothesis). The canonical representative is then
    taken to be the shortlex-minimum element of that `Finset`, via
    `Finset.min'`.
  * To linearly order windows we take a `LinearOrder (BlockIdx × LocalOp)`
    as a hypothesis instance and lift it to `List.Vector _ κ` via
    `LinearOrder.lift'` on the underlying `List _` lex order.

  The whole development is kernel-only (no `sorry`, no new axioms):
  all proofs are by elementary `Finset` lemmas and definitional unfolding.
-/
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Max
import Mathlib.Order.Lattice
import Mathlib.Tactic

namespace PallLean
namespace Paper93

open List (Vector)

/-! ### Lex linear order on `List.Vector` -/

/-- The lex order on `List.Vector α n`, lifted from `List.instLinearOrder`. -/
instance listVectorLinearOrder {α : Type*} [LinearOrder α] {n : ℕ} :
    LinearOrder (List.Vector α n) :=
  LinearOrder.lift' (fun v => v.toList) (fun _ _ h => Subtype.ext h)

/-! ### The canonicalization map -/

variable {BlockIdx LocalOp : Type}
variable [Fintype BlockIdx] [DecidableEq BlockIdx]
variable [Fintype LocalOp] [DecidableEq LocalOp]
variable [LinearOrder (BlockIdx × LocalOp)]

/--
A `Window κ` is a `List.Vector (BlockIdx × LocalOp) κ`, i.e. a length-`κ`
sequence of (block index, local operation) pairs.

This is an alias chosen to match the paper's `Win κ`. When Agent 1's
`Win κ` is available, it can be definitionally identified with this
alias (both are `List.Vector (BlockIdx × LocalOp) κ`).
-/
abbrev Window (BlockIdx LocalOp : Type) (κ : ℕ) :=
  List.Vector (BlockIdx × LocalOp) κ

/--
Equivalence-class data for a window under rules (P6) and (P7).

The abstract data required to canonicalise a window `w` consists of a
`Finset` of windows `cls` (the equivalence class of `w`) together with a
proof `w ∈ cls` (nonemptiness witness). This is stated as a `structure`
so that different implementations of (P6)/(P7) can plug in without
touching this file.
-/
structure EquivClassData (κ : ℕ) (w : Window BlockIdx LocalOp κ) where
  /-- The finite equivalence class of `w` under (P6) ∪ (P7). -/
  cls : Finset (Window BlockIdx LocalOp κ)
  /-- `w` itself is in its equivalence class. -/
  self_mem : w ∈ cls

/--
A *canonicalisation scheme* packages a way to compute the equivalence
class of every window. This abstracts both (P6) (adjacent-swap with
disjoint support) and (P7) (NF replacement) via Agent 3's `NF`.
-/
structure CanonScheme (κ : ℕ) where
  /-- Equivalence-class data for every window. -/
  eqv : (w : Window BlockIdx LocalOp κ) → EquivClassData (κ := κ) w
  /-- The class is a genuine equivalence: if `w' ∈ eqv(w).cls` then
      `eqv(w').cls = eqv(w).cls`. -/
  sym : ∀ (w w' : Window BlockIdx LocalOp κ),
          w' ∈ (eqv w).cls → (eqv w').cls = (eqv w).cls

/-! ### The canonicalization map itself -/

variable (κ : ℕ)

-- Silence the `automatically included section variable(s) unused` linter
-- for the purely combinatorial Finset helpers that do not themselves need
-- the full algebraic instance package.
set_option linter.unusedSectionVars false in
/-- Nonemptiness of the equivalence class, derived from `self_mem`. -/
private lemma eqClass_nonempty
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    (w : Window BlockIdx LocalOp κ) :
    (S.eqv w).cls.Nonempty :=
  ⟨w, (S.eqv w).self_mem⟩

/--
Paper §9.3.1 Definition 20: the canonicalization map `can : Win κ → Win κ`.

`canWindow S w` returns the shortlex-minimum representative of `w`'s
equivalence class under (P6) ∪ (P7), where the equivalence class is
supplied by the canonicalisation scheme `S`.
-/
def canWindow (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    (w : Window BlockIdx LocalOp κ) : Window BlockIdx LocalOp κ :=
  (S.eqv w).cls.min' (eqClass_nonempty (κ := κ) S w)

/-- `canWindow S w` always lies in `w`'s equivalence class. -/
theorem canWindow_mem_class
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    (w : Window BlockIdx LocalOp κ) :
    canWindow (κ := κ) S w ∈ (S.eqv w).cls := by
  unfold canWindow
  exact Finset.min'_mem _ _

/-- `canWindow S w` is ≤ every element of `w`'s equivalence class. -/
theorem canWindow_le
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    (w : Window BlockIdx LocalOp κ) :
    ∀ w' ∈ (S.eqv w).cls, canWindow (κ := κ) S w ≤ w' := by
  intro w' hw'
  unfold canWindow
  exact Finset.min'_le _ _ hw'

/--
The key structural fact: if two windows share an equivalence class
(i.e. `w' ∈ (S.eqv w).cls`), then `canWindow S w' = canWindow S w`.

This uses the `sym` field of the canonicalisation scheme: equivalence
classes of windows in the same class coincide as `Finset`s, so their
`min'` coincides.
-/
theorem canWindow_congr
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    {w w' : Window BlockIdx LocalOp κ}
    (hw' : w' ∈ (S.eqv w).cls) :
    canWindow (κ := κ) S w' = canWindow (κ := κ) S w := by
  unfold canWindow
  -- Both classes are the same Finset by `S.sym`:
  have hEq : (S.eqv w').cls = (S.eqv w).cls := S.sym w w' hw'
  -- Rewrite the class on the LHS.
  simp [hEq]

/-- **Idempotence** of `canWindow` (Paper §9.3.1 Definition 20).

Applying the canonicalisation map twice gives the same result as applying
it once: `canWindow κ (canWindow κ w) = canWindow κ w`. -/
theorem canWindow_idempotent
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    (w : Window BlockIdx LocalOp κ) :
    canWindow (κ := κ) S (canWindow (κ := κ) S w) = canWindow (κ := κ) S w :=
  canWindow_congr (κ := κ) S (canWindow_mem_class (κ := κ) S w)

/-! ### Canonical-window subtype -/

/-- Paper §9.3.1 Definition 20: `IsCanonical w` says `w` is a fixed point
of the canonicalization map, i.e. it is already in canonical form. -/
def IsCanonical
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    (w : Window BlockIdx LocalOp κ) : Prop :=
  canWindow (κ := κ) S w = w

/-- The image of `canWindow` consists entirely of canonical windows. -/
theorem isCanonical_canWindow
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    (w : Window BlockIdx LocalOp κ) :
    IsCanonical (κ := κ) S (canWindow (κ := κ) S w) :=
  canWindow_idempotent (κ := κ) S w

/-- A canonical window is, tautologically, its own canonicalisation. -/
theorem canWindow_of_isCanonical
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    {w : Window BlockIdx LocalOp κ}
    (hw : IsCanonical (κ := κ) S w) :
    canWindow (κ := κ) S w = w := hw

/-- Canonical windows form a subtype of windows. -/
def CanonicalWindow
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ) :=
  { w : Window BlockIdx LocalOp κ // IsCanonical (κ := κ) S w }

/-- Paper §9.3.1: `Winκᶜᵃⁿ := can(Winκ)` is the set of canonical windows.
We realise it as the `Finset` image of `canWindow`. -/
noncomputable def canonicalWindows
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ) :
    Finset (Window BlockIdx LocalOp κ) :=
  (Finset.univ : Finset (Window BlockIdx LocalOp κ)).image (canWindow (κ := κ) S)

/-- Every canonical window is a member of the `canonicalWindows` Finset. -/
theorem mem_canonicalWindows_of_isCanonical
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    {w : Window BlockIdx LocalOp κ} (hw : IsCanonical (κ := κ) S w) :
    w ∈ canonicalWindows (κ := κ) S := by
  classical
  refine Finset.mem_image.mpr ⟨w, Finset.mem_univ _, ?_⟩
  exact hw

/-- Every element of `canonicalWindows` is canonical. -/
theorem isCanonical_of_mem_canonicalWindows
    (S : CanonScheme (BlockIdx := BlockIdx) (LocalOp := LocalOp) κ)
    {w : Window BlockIdx LocalOp κ}
    (hw : w ∈ canonicalWindows (κ := κ) S) :
    IsCanonical (κ := κ) S w := by
  classical
  rcases Finset.mem_image.mp hw with ⟨u, _, hu⟩
  -- `hu : canWindow κ S u = w` and `canWindow` applied to anything is canonical.
  have hCan : IsCanonical (κ := κ) S (canWindow (κ := κ) S u) :=
    isCanonical_canWindow (κ := κ) S u
  exact hu ▸ hCan

end Paper93
end PallLean
