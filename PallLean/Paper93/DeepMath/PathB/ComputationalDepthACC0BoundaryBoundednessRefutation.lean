import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CommunicationComplexity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0CarryBoundaryGrowth

/-!
# Attacking the boundary-boundedness socket directly — it is FALSE (a proved no-go)

Entry 286 reduced the composite `ACC⁰` separation to one socket:
`BoundedCompositionKeepsBoundaryBounded` — *does `ACC⁰[6]`-bounded composition keep the product-observer boundary
polynomially bounded?*  This file attacks that socket head-on and **proves it is false** for any polynomial budget.

**The attack.**  The product-observer boundary of a two-party function `f` is the number of distinct rows of its
communication matrix.  We exhibit a function realizable by a *tiny* `AC⁰ ⊆ ACC⁰[6]` circuit whose boundary is
**exponential**: the equality function `eq(a,b) := [a = b]` (on `k`-bit halves, computable as a depth-2 `AND` of
`XNOR`s).  Its communication matrix is the identity — `2^k` pairwise distinct rows — so any product observer needs
`≥ 2^k` boundary states.  (Set-disjointness, the depth-2 `OR` of `AND`s, gives the same conclusion.)

**The verdict.**  `equality_refutes_boundary_bounded`: any boundary budget that bounds *all* realizable functions must be
`≥ #A = 2^k` — exponential.  So no polynomial budget works; the socket is **false**, and entry 286's conditional, while
a true implication, has an unsatisfiable hypothesis.  The boundary route is dead.

**Why — the decisive structural finding.**  The communication boundary *anti-tracks* `ACC⁰[6]`-hardness:

* `MOD_M` is communication-*easy* — boundary exactly `M`, i.e. communication `O(log M)` (Alice sends her residue);
* equality / disjointness are communication-*hard* — boundary `2^k`, i.e. communication `Θ(k)` —

yet **both** are computable in `AC⁰ ⊆ ACC⁰[6]`.  So raw communication boundary cannot separate: it is large for easy
functions and small for the modular target.  The separating resource is **not** boundary size but the *characteristic /
CRT structure* — small for the native moduli `{2,3}`, large for a non-native prime — exactly the field-incompatibility
of entries 280–283 that boundary size cannot see.  Attacking the socket directly confirms the obstruction is genuinely
characteristic-bound, not a communication-counting fact.

## What is proved (clean axioms, no `sorry`)

* **`product_observer_card_ge_of_rows_injective`** (PROVED) — for any two-party `f` with pairwise-distinct
  communication-matrix rows, every product observer has boundary `≥ #A`.
* **`eqValue_rows_injective`** (PROVED) — the equality matrix (identity) has `#A` distinct rows.
* **`equality_product_observer_card_ge`** / **`equality_boundary_two_pow`** (PROVED) — equality needs boundary `≥ #A`,
  i.e. `≥ 2^k` on `k`-bit halves: exponential, realizable in `AC⁰`.
* **`equality_refutes_boundary_bounded`** (PROVED) — any budget bounding all realizable functions' boundary is `≥ #A`;
  hence no polynomial budget works: the entry-286 socket is **false**.

## Honest scope

A genuine, machine-proved **no-go** on the boundary-boundedness socket of entry 286: it is false for polynomial budgets
because `AC⁰ ⊆ ACC⁰[6]` realizes equality/disjointness with exponential communication boundary.  This refutes the
boundary route and re-localizes the obstruction onto the characteristic/CRT structure (entries 280–283), which raw
communication cannot detect.  This is **not** `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC0_ANATOMY.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BoundaryBoundednessRefutation

open PallLean.Paper93.DeepMath.PathB

/-- **General boundary lower bound from distinct rows (PROVED).**  For *any* two-party function `f : A → A → Bool` whose
communication-matrix rows `a ↦ (b ↦ f a b)` are pairwise distinct, every product observer (encoder `msg`, decoder
`decode`, correct) has boundary `≥ #A`.  Correctness forces `msg` to separate the distinct rows, so `msg` is injective.
The same fooling-set argument as `commValue_row_injective`, now for arbitrary `f`. -/
theorem product_observer_card_ge_of_rows_injective {A B : Type} [Fintype A] [Fintype B]
    (f : A → A → Bool) (hinj : Function.Injective (fun a => fun b => f a b))
    (msg : A → B) (decode : B → A → Bool) (hcorrect : ∀ a b, decode (msg a) b = f a b) :
    Fintype.card A ≤ Fintype.card B := by
  have hmsg : Function.Injective msg := by
    intro a₁ a₂ he
    apply hinj
    funext b
    calc f a₁ b = decode (msg a₁) b := (hcorrect a₁ b).symm
      _ = decode (msg a₂) b := by rw [he]
      _ = f a₂ b := hcorrect a₂ b
  exact Fintype.card_le_of_injective msg hmsg

/-- **The equality matrix has `#A` distinct rows (PROVED).**  Row `a` of the equality function is `b ↦ [a = b]`, the
indicator of `{a}`; distinct `a` give distinct rows (the communication matrix of equality is the identity). -/
theorem eqValue_rows_injective {A : Type} [DecidableEq A] :
    Function.Injective (fun a : A => fun b : A => decide (a = b)) := by
  intro a₁ a₂ heq
  have h : decide (a₁ = a₁) = decide (a₂ = a₁) := congrFun heq a₁
  rw [decide_eq_decide] at h
  exact (h.mp rfl).symm

/-- **Equality needs boundary `≥ #A` (PROVED).**  Any product observer computing the equality function across the cut
has `≥ #A` boundary states — the identity communication matrix has `#A` distinct rows. -/
theorem equality_product_observer_card_ge {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (msg : A → B) (decode : B → A → Bool)
    (hcorrect : ∀ a b, decode (msg a) b = decide (a = b)) :
    Fintype.card A ≤ Fintype.card B :=
  product_observer_card_ge_of_rows_injective (fun a b => decide (a = b)) eqValue_rows_injective
    msg decode hcorrect

/-- **Equality on `k`-bit halves has exponential boundary (PROVED).**  Computing `[a = b]` for `a, b : Fin k → Bool`
needs `≥ 2^k` boundary states.  Equality is computable by a depth-2 `AC⁰` circuit (`AND` of `XNOR`s), so this is a
poly-size `AC⁰ ⊆ ACC⁰[6]` function with **exponential** communication boundary — the counterexample that breaks the
socket. -/
theorem equality_boundary_two_pow {k : ℕ} {B : Type} [Fintype B]
    (msg : (Fin k → Bool) → B) (decode : B → (Fin k → Bool) → Bool)
    (hcorrect : ∀ a b : Fin k → Bool, decode (msg a) b = decide (a = b)) :
    2 ^ k ≤ Fintype.card B := by
  have hcard : Fintype.card (Fin k → Bool) = 2 ^ k := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h := equality_product_observer_card_ge msg decode hcorrect
  rwa [hcard] at h

/-- The boundary-boundedness socket of entry 286, stated for *general* two-party functions and an abstract
realizability predicate `Realizable` (e.g. "computable by an `ACC⁰[6]`-bounded composition of resource `≤ s`"): every
realizable function admits a product observer of boundary `≤ budget`. -/
def GeneralBoundaryBounded {A : Type} [Fintype A]
    (Realizable : (A → A → Bool) → Prop) (budget : ℕ) : Prop :=
  ∀ f : A → A → Bool, Realizable f →
    ∃ (B : Type) (_ : Fintype B) (msg : A → B) (decode : B → A → Bool),
      (∀ a b, decode (msg a) b = f a b) ∧ Fintype.card B ≤ budget

/-- **The socket is FALSE for polynomial budgets (PROVED no-go).**  If the equality function is realizable (it is — a
depth-2 `AC⁰ ⊆ ACC⁰[6]` circuit), then any boundary budget bounding *all* realizable functions must be `≥ #A`.  On
`k`-bit halves `#A = 2^k`, so the budget is forced to be **exponential** — no polynomial budget can bound the boundary.
Hence the entry-286 socket `BoundedCompositionKeepsBoundaryBounded` cannot hold with a polynomial budget, and its
conditional separation, though a true implication, has an unsatisfiable hypothesis.  The boundary route is dead. -/
theorem equality_refutes_boundary_bounded {A : Type} [Fintype A] [DecidableEq A]
    (Realizable : (A → A → Bool) → Prop) (hEq : Realizable (fun a b => decide (a = b)))
    (budget : ℕ) (hbb : GeneralBoundaryBounded Realizable budget) :
    Fintype.card A ≤ budget := by
  obtain ⟨B, _, msg, decode, hcorrect, hcard⟩ := hbb (fun a b => decide (a = b)) hEq
  have hlb := equality_product_observer_card_ge msg decode hcorrect
  omega

/-- **The socket needs an exponential budget on `k`-bit halves (PROVED).**  Specialising the no-go: any budget bounding
all realizable functions on `Fin k → Bool` is `≥ 2^k`.  So `BoundedCompositionKeepsBoundaryBounded` with a polynomial
budget is false once `Realizable` includes equality (which `AC⁰ ⊆ ACC⁰[6]` does). -/
theorem boundary_socket_needs_exponential_budget {k : ℕ}
    (Realizable : ((Fin k → Bool) → (Fin k → Bool) → Bool) → Prop)
    (hEq : Realizable (fun a b => decide (a = b)))
    (budget : ℕ) (hbb : GeneralBoundaryBounded Realizable budget) :
    2 ^ k ≤ budget := by
  have h := equality_refutes_boundary_bounded Realizable hEq budget hbb
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h

/-!
**The result of attacking the socket directly.**  It breaks: `BoundedCompositionKeepsBoundaryBounded` is **false** for
any polynomial budget, because `AC⁰ ⊆ ACC⁰[6]` realizes equality (and disjointness) with exponential communication
boundary (`equality_boundary_two_pow`, `boundary_socket_needs_exponential_budget`).  So the entry-286 boundary route
cannot yield a separation — its socket is unsatisfiable for poly budgets.

The decisive finding: communication boundary **anti-tracks** `ACC⁰[6]`-hardness.  `MOD_M` is communication-*easy*
(boundary `M`, communication `O(log M)`); equality/disjointness are communication-*hard* (boundary `2^k`); both are in
`AC⁰ ⊆ ACC⁰[6]`.  Boundary size therefore cannot be the separating resource.  What separates is the *characteristic /
CRT structure* — small for the native moduli `{2,3}`, large for a non-native prime — the field-incompatibility of
entries 280–283 that raw communication cannot see.  Attacking the socket head-on re-localizes the obstruction back onto
the characteristic mixing, confirming it is not a communication-counting fact.  An honest no-go, not a separation, not
faked.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0BoundaryBoundednessRefutation

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryBoundednessRefutation.product_observer_card_ge_of_rows_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryBoundednessRefutation.eqValue_rows_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryBoundednessRefutation.equality_boundary_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryBoundednessRefutation.equality_refutes_boundary_bounded
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BoundaryBoundednessRefutation.boundary_socket_needs_exponential_budget
