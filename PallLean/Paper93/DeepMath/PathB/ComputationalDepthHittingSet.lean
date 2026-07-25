import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSchwartzZippel

/-!
# Derandomizing `PIT` = compressing a hitting set from exponential to polynomial size

The hardness↔randomness escape (`HardnessRandomness`) localizes a circuit lower bound to
**derandomizing `PIT`**.  This file pins down *exactly* what that means algebraically and shows how
much of it we already have.

A **hitting set** for degree-`d` polynomials in `n` variables is a finite set `H ⊆ Fⁿ` such that
*every* nonzero polynomial of total degree `≤ d` is non-zero at *some* point of `H`.  A deterministic
`PIT` algorithm is exactly the ability to test a circuit by evaluating it at each point of a
hitting set: if the circuit computes a nonzero polynomial, some hitting point exposes it; if it is
identically zero, every point returns `0`.  So:

> **deterministic `PIT` ⟺ a hitting set that is small (poly-size) and explicitly constructible.**

* **`IsHittingSet`** — the defining property.
* **`grid_is_hitting_set` (proved)** — Schwartz–Zippel *already* gives a hitting set: any product
  grid `S^n` with side `#S > d` hits every nonzero degree-`d` polynomial.  Unconditional, from
  `sz_mv_exists_nonroot`.
* **`grid_hitting_set_card` (proved)** — but that grid has size `≥ (d+1)^n` — **exponential** in the
  number of variables.  This is the hitting set randomness hands us for free.
* **`small_hitting_forces_lower_bound` (proved, socketed)** — a *poly-size* hitting-set family
  (the open target) composes with the Kabanets–Impagliazzo bridge to force a circuit lower bound.

**Honest scope.**  The proved content is that the exponential grid *is* a hitting set (real math) and
that the entire remaining gap is **compressing `(d+1)^n` down to `poly(n,d)`** — the classical
derandomization frontier, an *algebraic* problem (small explicit hitting sets / hitting-set
generators).  The poly-size hitting set is a **named open socket**, not proved here; it is *not*
`P ≠ NP`, and it is plausibly easier and is where derandomization research concentrates.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.HittingSet

open PallLean.Paper93.DeepMath.PathB.SchwartzZippel

variable {F : Type*} [Field F] [DecidableEq F]

/-- **A hitting set for total degree `d`.**  A finite set of points `H ⊆ Fⁿ` such that every nonzero
polynomial of total degree `≤ d` fails to vanish at some point of `H`.  Evaluating a circuit at every
point of such an `H` is a deterministic identity test for degree-`d` polynomials. -/
def IsHittingSet {n : ℕ} (H : Finset (Fin n → F)) (d : ℕ) : Prop :=
  ∀ p : MvPolynomial (Fin n) F, p ≠ 0 → p.totalDegree ≤ d →
    ∃ f ∈ H, MvPolynomial.eval f p ≠ 0

/-- **Schwartz–Zippel already builds a hitting set (proved).**  Any product grid `S^n` whose side
`#S` strictly exceeds the degree bound `d` is a hitting set for total degree `d`: a nonzero
degree-`≤ d` polynomial has a non-vanishing point in the grid.  This is the hitting set randomness
hands us — directly from `sz_mv_exists_nonroot`. -/
theorem grid_is_hitting_set {n d : ℕ} (S : Finset F) (hS : d < S.card) :
    IsHittingSet (Fintype.piFinset (fun _ : Fin n => S)) d := by
  intro p hp hpd
  exact sz_mv_exists_nonroot hp S (lt_of_le_of_lt hpd hS)

/-- **…but the Schwartz–Zippel hitting set is exponential (proved).**  The grid `S^n` with side
`#S > d` has at least `(d+1)^n` points — exponential in the number of variables `n`.  Randomness
gives a hitting set for free, but not a *small* one; shrinking this is the whole game. -/
theorem grid_hitting_set_card {n d : ℕ} (S : Finset F) (hS : d < S.card) :
    (d + 1) ^ n ≤ (Fintype.piFinset (fun _ : Fin n => S)).card := by
  have hcard : (Fintype.piFinset (fun _ : Fin n => S)).card = S.card ^ n := by
    simp [Fintype.card_piFinset]
  rw [hcard]
  exact Nat.pow_le_pow_left hS n

/-- **The concrete derandomization target, named.**  A *poly-size* hitting-set family is the open
socket; combined with the Kabanets–Impagliazzo implication (`ki`), it forces a circuit lower bound.
The map `toDerand : SmallHitting → DerandPIT` is the (elementary) fact that testing a circuit against
a small hitting set is a deterministic poly-time identity test; `ki` is the deep Kabanets–Impagliazzo
theorem.  Both are socketed, but the socket is now *sharply* algebraic: **a poly-size hitting set for
low-degree polynomials** (Schwartz–Zippel gives an exponential one via `grid_is_hitting_set`). -/
theorem small_hitting_forces_lower_bound
    (SmallHitting DerandPIT NEXPinPpoly PermInPolyArith : Prop)
    (toDerand : SmallHitting → DerandPIT)
    (ki : DerandPIT → NEXPinPpoly → PermInPolyArith → False)
    (hHit : SmallHitting) :
    ¬ (NEXPinPpoly ∧ PermInPolyArith) :=
  fun ⟨h1, h2⟩ => ki (toDerand hHit) h1 h2

end PallLean.Paper93.DeepMath.PathB.HittingSet

#print axioms PallLean.Paper93.DeepMath.PathB.HittingSet.grid_is_hitting_set
#print axioms PallLean.Paper93.DeepMath.PathB.HittingSet.grid_hitting_set_card
#print axioms PallLean.Paper93.DeepMath.PathB.HittingSet.small_hitting_forces_lower_bound
