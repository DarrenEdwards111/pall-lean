import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Concrete N-Frame invariant: definitions + the semantic-invariance kill test

Per the roadmap, this is the first concrete step past the abstract separating-invariant interface: give an
**exact combinatorial** definition of a representation-based rank, and run the **semantic-invariance kill test**
before anything else.  No SAT lower bound is attempted.

* `SPDPComputation n` — a computation presented as a decision function together with its `sheet`: an explicit
  Boolean representation matrix (rows = length-`n` inputs, columns = probes).
* `spdpRank` — the exact rank proxy: the number of *distinct rows* of the sheet.
* `trivialSheet` / `identitySheet` — two computations of the **same** decision function: one with a one-column
  constant sheet (rank `1`), one whose sheet is the identity matrix (rank `2^n`).

The decisive result `rank_gap_unbounded_same_decision`: two computations of the *same* decision can have rank
ratio exceeding any bound.  So `spdpRank` measures the **representation**, not the decision function — it is
**not** semantically invariant, and (by the interface's `polyR_decider_breaks_SATLower`) cannot be a separating
invariant as stated.  The identity sheet is the SPDP form of the appended-sheet countermodel.

## Consequence and honest scope

Representation-`SPDP` rank is **rejected** at the decisive gate.  The only repairs are an intrinsic definition
of rank from the Boolean decision function, a fixed canonical encoding, or minimisation over all computations
of a function.  Under any of those, `PUpper` (rank polynomial for every `P` function — threatened by parity /
Θ(n)-bit combination) becomes the next major obligation, and the NP-side lower bound is only reached after
that.  This file attempts **none** of those; it is exactly step 1–2 of the audit.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameConcreteInvariant

/-! ## Exact definitions -/

/-- A computation presented with its representation: the decided function plus a `sheet` — the explicit Boolean
representation matrix, rows indexed by length-`n` inputs, columns by a finite probe set. -/
structure SPDPComputation (n : Nat) where
  decision : (Fin n → Bool) → Bool
  Probe : Type
  probeFintype : Fintype Probe
  sheet : (Fin n → Bool) → Probe → Bool

/-- The exact rank proxy: the number of distinct rows of the representation matrix.  Formulated with
`Nat.card` of the range to stay free of any `DecidableEq` instance choice. -/
noncomputable def spdpRank {n : Nat} (C : SPDPComputation n) : Nat :=
  Nat.card (Set.range C.sheet)

/-! ## Two computations of the same decision with wildly different rank -/

/-- A one-column, constant representation of `f`: every row is identical, so rank `1`. -/
def trivialSheet {n : Nat} (f : (Fin n → Bool) → Bool) : SPDPComputation n where
  decision := f
  Probe := Unit
  probeFintype := inferInstance
  sheet := fun _ _ => false

/-- The identity representation of `f`: row `x` is the indicator of `x`, so all `2^n` rows are distinct. -/
def identitySheet {n : Nat} (f : (Fin n → Bool) → Bool) : SPDPComputation n where
  decision := f
  Probe := Fin n → Bool
  probeFintype := inferInstance
  sheet := fun x y => decide (x = y)

/-- Both present the **same** decision function. -/
theorem sameDecision {n : Nat} (f : (Fin n → Bool) → Bool) :
    (trivialSheet f).decision = (identitySheet f).decision := rfl

theorem trivialSheet_rank {n : Nat} (f : (Fin n → Bool) → Bool) :
    spdpRank (trivialSheet f) = 1 := by
  rw [spdpRank]
  have : Set.range (trivialSheet f).sheet = {fun _ => false} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨fun _ => default, rfl⟩, ?_⟩
    rintro y ⟨x, rfl⟩
    rfl
  rw [this, Nat.card_eq_fintype_card, Fintype.card_unique]

theorem identitySheet_rank {n : Nat} (f : (Fin n → Bool) → Bool) :
    spdpRank (identitySheet f) = 2 ^ n := by
  rw [spdpRank]
  have hinj : Function.Injective (identitySheet f).sheet := by
    intro a b h
    by_contra hne
    have hc := congrFun h a
    simp only [identitySheet] at hc
    rw [decide_eq_false (fun hba : b = a => hne hba.symm)] at hc
    simp at hc
  rw [Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-! ## The decisive semantic-invariance kill test

`spdpRank` is not a function of the decision: two computations of the *same* decision can have unboundedly
different rank.  Hence it is not semantically invariant, and cannot separate `P` from `NP` as defined. -/

/-- `n < 2^n`, elementary. -/
theorem lt_two_pow (n : Nat) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ m ih =>
    have h1 : 0 < 2 ^ m := by positivity
    have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
    omega

/-- **The semantic-invariance kill test (failed).**  For every bound `B` there are two computations of the
same decision function whose ranks differ by more than a factor `B`.  So `spdpRank` measures the
representation, not the decision. -/
theorem rank_gap_unbounded_same_decision :
    ∀ B : Nat, ∃ (n : Nat) (C₁ C₂ : SPDPComputation n),
      C₁.decision = C₂.decision ∧ B * spdpRank C₁ < spdpRank C₂ := by
  intro B
  refine ⟨B + 1, trivialSheet (fun _ => false), identitySheet (fun _ => false), rfl, ?_⟩
  rw [trivialSheet_rank, identitySheet_rank, mul_one]
  calc B < B + 1 := Nat.lt_succ_self B
    _ < 2 ^ (B + 1) := lt_two_pow (B + 1)

/-- Restated as an explicit witness pair for readability. -/
theorem spdpRank_representation_dependent (n : Nat) :
    (trivialSheet (fun _ => false : (Fin n → Bool) → Bool)).decision =
      (identitySheet (fun _ => false : (Fin n → Bool) → Bool)).decision ∧
    spdpRank (trivialSheet (fun _ => false : (Fin n → Bool) → Bool)) = 1 ∧
    spdpRank (identitySheet (fun _ => false : (Fin n → Bool) → Bool)) = 2 ^ n :=
  ⟨rfl, trivialSheet_rank _, identitySheet_rank _⟩

end PallLean.Paper93.DeepMath.PathB.NFrameConcreteInvariant

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConcreteInvariant.trivialSheet_rank
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConcreteInvariant.identitySheet_rank
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameConcreteInvariant.rank_gap_unbounded_same_decision
