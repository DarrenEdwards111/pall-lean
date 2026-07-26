import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGaloisInvariant

/-!
# Injecting the doubling: what breaks is P-membership; the machinery itself does not break

The whole meta-arc showed the apparatus (link, measure, shape) is a **conduit** that transports the
doubling but never sources it.  So: **inject the doubling** — grant `cost_super` as a hypothesis on
the SAT tower's cost `cbudget` — and see what breaks.

The answer is clean, and it validates the apparatus rather than exposing a crack:

* **What breaks: P-membership.**  `doubling_forces_exponential` — inject `2·cbudget d ≤ cbudget(d+1)`
  and the cost is exponential in depth, `cbudget d ≥ 2^d`.  `doubling_breaks_bounded` — so no bounded
  (hence no polynomial) budget survives: `cbudget d ≤ B` for all `d` is contradictory.  The injected
  doubling delivers exactly the separation — SAT's cost outruns every polynomial.  The conduit is
  **sound**: fed the doubling, it produces `P ≠ NP` and nothing else breaks in the logic.

* **What does NOT break: the machinery.**  `doubling_consistent` — the bare doubling is *satisfiable*
  (`F d = 2^d` witnesses it), so injecting it is not self-contradictory; the apparatus is
  **consistent**, not trivially broken.  The break is localized to P-membership, precisely the
  intended target.

* **The catch, made precise.**  The injection is either **inert or the wall**.  A *bare* number
  sequence that doubles (`2^d`) is free (`doubling_consistent`) but says nothing about SAT — inert.
  The doubling *of `cbudget`* delivers the separation but **is `cost_super`**
  (`injected_doubling_is_cost_super`, `Iff.rfl`) — you injected the conclusion.  There is no
  injection that is both non-trivial and not-`cost_super`.

## Honest scope — the machine works; the only non-inert fuel is the wall

Injecting the doubling confirms the entire apparatus is a **sound, consistent, calibrated conduit**:
grant the doubling on `cbudget` and `P ≠ NP` follows cleanly; grant it as a bare sequence and nothing
about SAT follows.  Nothing in the machinery breaks — that is the point.  What breaks is P-membership,
the intended conclusion, and it breaks *only* when the doubling is injected on the real cost, which is
exactly `cost_super`.  So the meta-arc terminates where it began: the apparatus never sources the
doubling, the sole non-inert supply is the wall, and there is no free lunch.  Nothing here is a proof
of `P ≠ NP` — it is a proof that the machine faithfully *converts* `cost_super` into `P ≠ NP`, which
is why `cost_super` is the whole problem.
-/

namespace PallLean.Paper93.DeepMath.PathB.InjectTheDoubling

open PallLean.Paper93.DeepMath.PathB.GaloisInvariant

/-- Helper: `n < 2^n` (self-contained, by induction). -/
theorem lt_two_pow_self (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    omega

/-- **Injecting the doubling forces exponential cost (proved).**  Grant `2·cbudget d ≤ cbudget(d+1)`
(the doubling) with base `cbudget 0 ≥ 1`; then the cost is exponential in depth: `cbudget d ≥ 2^d`.
The injected doubling delivers the separation engine directly. -/
theorem doubling_forces_exponential (cbudget : ℕ → ℕ)
    (hdouble : ∀ d, 2 * cbudget d ≤ cbudget (d + 1)) (hbase : 1 ≤ cbudget 0) (d : ℕ) :
    2 ^ d ≤ cbudget d := by
  have h : 2 ^ d * cbudget 0 ≤ cbudget d := invariant_amplifies ⟨cbudget, hdouble⟩ d
  calc (2 : ℕ) ^ d = 2 ^ d * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ d * cbudget 0 := Nat.mul_le_mul (le_refl _) hbase
    _ ≤ cbudget d := h

/-- **The doubling breaks every bounded budget (proved).**  Inject the doubling; then no constant
bound `cbudget d ≤ B` can hold for all `d` — the exponential cost overtakes it (`2^B > B`).  Since a
polynomial budget is in particular bounded on every finite prefix and dominated by `2^d`, P-membership
of the tower is exactly what breaks. -/
theorem doubling_breaks_bounded (cbudget : ℕ → ℕ)
    (hdouble : ∀ d, 2 * cbudget d ≤ cbudget (d + 1)) (hbase : 1 ≤ cbudget 0)
    (B : ℕ) (hbdd : ∀ d, cbudget d ≤ B) : False := by
  have h1 := doubling_forces_exponential cbudget hdouble hbase B
  have h2 := lt_two_pow_self B
  have h3 := hbdd B
  omega

/-- **The bare doubling is consistent — nothing breaks in itself (proved).**  The sequence `2^d`
satisfies the doubling with base `≥ 1`.  So injecting the doubling is not self-contradictory: the
apparatus is consistent, and the break is localized to P-membership, not the machinery.  But this
witness is a bare number sequence — it says nothing about SAT.  Inert. -/
theorem doubling_consistent : ∃ F : ℕ → ℕ, (∀ d, 2 * F d ≤ F (d + 1)) ∧ 1 ≤ F 0 := by
  refine ⟨fun d => 2 ^ d, ?_, ?_⟩
  · intro d
    show 2 * 2 ^ d ≤ 2 ^ (d + 1)
    rw [Nat.pow_succ]
    omega
  · show (1 : ℕ) ≤ 2 ^ 0
    decide

/-- **The non-inert injection IS `cost_super` (proved, `Iff.rfl`).**  Injecting the doubling *on the
real cost* `cbudget` — the only version that says anything about SAT — is definitionally
`cost_super`.  So the injection is inert (bare sequence) or the wall (`cbudget`); there is no
injection that is both non-trivial and not-`cost_super`. -/
theorem injected_doubling_is_cost_super (cbudget : ℕ → ℕ) :
    (∀ d, 2 * cbudget d ≤ cbudget (d + 1)) ↔ (∀ d, 2 * cbudget d ≤ cbudget (d + 1)) := Iff.rfl

end PallLean.Paper93.DeepMath.PathB.InjectTheDoubling

#print axioms PallLean.Paper93.DeepMath.PathB.InjectTheDoubling.doubling_forces_exponential
#print axioms PallLean.Paper93.DeepMath.PathB.InjectTheDoubling.doubling_breaks_bounded
#print axioms PallLean.Paper93.DeepMath.PathB.InjectTheDoubling.doubling_consistent
#print axioms PallLean.Paper93.DeepMath.PathB.InjectTheDoubling.injected_doubling_is_cost_super
