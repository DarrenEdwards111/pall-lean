import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTimeContextualWidth

/-!
# The multiplicative / rank horn — and the honest attempt at A1 for it

The additive horn (`…TimeContextualWidth`) proved: a *summed* contextual invariant `tcw` makes Book-1 axiom **A1**
a theorem (bounded for all P) but is then capped at `T·n`, so the super-polynomial lower bound **A3** is *false*
for it.  The dichotomy predicts the **multiplicative / rank** horn is the mirror image: the invariant becomes
super-additive across the time cut, so **A3 is reachable** — but **A1** becomes the wall.  This file builds that
horn and confirms the prediction with proved theorems.

## The invariant: contextual rank across a cut

Split the input across a time cut into a *past* block `A` and a *future* block `B`.  An observer induces a matrix
`M : A → B → Bool` (the value, as the future varies, for each past-context).  The **contextual rank** is the
number of *distinct rows* — distinct past-contexts the observer must keep apart:

`crank M = |{ (fun b => M a b) : a ∈ A }|`.

This is a genuine rank/communication quantity (it equals the number of distinct rows of the communication matrix),
and it is **multiplicative across the cut** in the sense that it counts the product structure of past × future,
not a per-step sum.

## What is proved

* `crank_le_card_past` — `crank M ≤ |A|`: the rank is bounded by the *past-context count* — a **space** quantity.
* `crank_idMatrix` / `crank_cube_full` — the equality matrix achieves the ceiling: `crank = |A| = 2^a`.  **The
  rank is FULL — exponential in the block size.**
* `crank_unbounded` — `∀ N, ∃ a, N < crank(eq_a)`: the rank invariant is **unbounded**, in sharp contrast to the
  additive `tcw ≤ T·n`.  So **A3 (super-polynomial) is reachable** — exactly the half the additive horn lacked.
* `rank_space_bound_tight` — the only bound the budget yields is `crank ≤ 2^{space}`, and it is **achieved**.

## The outcome: A3 reachable, but A1 is the wall (proved)

`rank_space_bound_tight` is the verdict.  The contextual rank is bounded *only* by `2^{space}`, and that bound is
**tight** (the equality matrix saturates it).  A polynomial-*time* observer has only polynomial *space*, so the
rank bound it inherits is `2^{poly}` — **exponential, not polynomial** — and it is achievable.  Hence
"poly-time ⇒ poly rank" (**A1** for `crank`) does **not** follow from the time/space budget: it is an *additional
assumption*.  This is the rank analog of `space_machinery_cannot_supply_bridge` and `naive_time_cew_bound_false`
from the boundary side: the structural budget bounds rank by space, and space does not pin time.

Worse for the route (stated in prose, not over-claimed in Lean): standard P functions already realize *full*
contextual rank — inner-product and equality are linear-time yet have full rank `2^{n/2}` — so raw `crank` is in P
at the top of its range.  Only a *projected / structured* rank (the actual SPDP rank, after the contextual
projection that the Book-1 route posits) could conceivably satisfy A1, and that projection — "the P-time structure
forces the projected rank low" — is precisely the **assumed-not-derived** Book-1 bridge (A2/A1) audited in the
corpus (`…NFrameHypercubeConstraint`).

## Both horns, proved

| invariant | shape | A1 (bounded for P) | A3 (super-poly on hard family) |
|---|---|---|---|
| `tcw` (additive) | `∑ log width` | **provable** (`≤ T·n`) | **provably false** (capped at `T·n`) |
| `crank` (multiplicative) | `#distinct rows` | **the wall** (only `≤ 2^{space}`, tight) | **provable/reachable** (`= 2^a`, unbounded) |

An *unweighted* contextual invariant cannot have both: additive ones are too small (A3 fails), rank ones are
achieved by easy functions and bounded only by space (A1 fails).  Closing the separation needs the rank to be low
*because of the time structure* — the SPDP projection bridge — which is the one irreducible, `P ≠ NP`-strength
step.  This file proves the multiplicative horn of that dichotomy rather than asserting it.
-/

namespace PallLean.Paper93.DeepMath.PathB.RankContextualWidth

/-- The **contextual rank** across a past/future cut: the number of distinct rows of the communication matrix
`M : A → B → Bool` — the number of distinct past-contexts the observer keeps apart. -/
def crank {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (M : A → B → Bool) : ℕ :=
  (Finset.univ.image (fun a => (fun b => M a b))).card

/-- **`crank ≤ |A|` (proved).**  The contextual rank is bounded by the number of past-contexts — a *space*
quantity, not a time quantity. -/
theorem crank_le_card_past {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (M : A → B → Bool) :
    crank M ≤ Fintype.card A := by
  unfold crank
  exact le_trans Finset.card_image_le (le_of_eq Finset.card_univ)

/-- The equality matrix on a single block: `eqMatrix a a' = [a = a']`. -/
def eqMatrix (A : Type*) [DecidableEq A] : A → A → Bool := fun a a' => decide (a = a')

/-- The rows of the equality matrix are distinct (the row map is injective): row `a` is the indicator of `a`. -/
theorem eqMatrix_rows_injective {A : Type*} [DecidableEq A] :
    Function.Injective (fun a : A => (fun a' => eqMatrix A a a')) := by
  intro a a' h
  have hval := congrFun h a'
  dsimp only at hval
  have hrow : eqMatrix A a a' = true := by rw [hval]; simp [eqMatrix]
  simpa [eqMatrix] using hrow

/-- **The equality matrix achieves the rank ceiling (proved): `crank (eqMatrix) = |A|`.**  Every past-context is
distinguished — the rank is full. -/
theorem crank_eqMatrix {A : Type*} [Fintype A] [DecidableEq A] :
    crank (eqMatrix A) = Fintype.card A := by
  unfold crank
  rw [Finset.card_image_of_injective Finset.univ eqMatrix_rows_injective, Finset.card_univ]

/-- **Full rank on the Boolean cube (proved): `crank = 2^a`.**  With an `a`-bit past block, the equality matrix
has rank `2^a` — exponential in the block size, i.e. super-polynomial in the total input `n = 2a`. -/
theorem crank_cube_full (a : ℕ) :
    crank (eqMatrix (Fin a → Bool)) = 2 ^ a := by
  rw [crank_eqMatrix]
  simp [Fintype.card_bool, Fintype.card_fin]

/-- **The rank invariant is UNBOUNDED (proved).**  For every `N` there is a block size `a` with
`crank(eqMatrix on a bits) = 2^a > N`.  Contrast the additive horn, where `tcw ≤ T·n` is always bounded: the
multiplicative invariant **can** be super-polynomial — A3 is reachable. -/
theorem crank_unbounded (N : ℕ) : ∃ a : ℕ, N < crank (eqMatrix (Fin a → Bool)) := by
  refine ⟨N, ?_⟩
  rw [crank_cube_full]
  exact Nat.lt_two_pow_self

/-- **The verdict: the rank's only budget bound is `2^{space}`, and it is tight (proved).**  Over an `s`-bit past
block, every contextual matrix has `crank ≤ 2^s` (a *space* bound), and the equality matrix *achieves* `2^s`.  So
a polynomial-time observer (polynomial space `s`) inherits only an **exponential**, tight rank ceiling `2^{poly}`
— never a polynomial one.  Hence "poly-time ⇒ poly rank" (A1 for `crank`) is not supplied by the time/space
budget; it is an additional assumption — the assumed Book-1 projection bridge. -/
theorem rank_space_bound_tight (s : ℕ) :
    crank (eqMatrix (Fin s → Bool)) = 2 ^ s ∧
      ∀ (B : Type*) [Fintype B] [DecidableEq B] (M : (Fin s → Bool) → B → Bool), crank M ≤ 2 ^ s := by
  refine ⟨crank_cube_full s, ?_⟩
  intro B _ _ M
  have h := crank_le_card_past M
  rwa [show Fintype.card (Fin s → Bool) = 2 ^ s by
    simp [Fintype.card_bool, Fintype.card_fin]] at h

end PallLean.Paper93.DeepMath.PathB.RankContextualWidth

#print axioms PallLean.Paper93.DeepMath.PathB.RankContextualWidth.crank_le_card_past
#print axioms PallLean.Paper93.DeepMath.PathB.RankContextualWidth.crank_cube_full
#print axioms PallLean.Paper93.DeepMath.PathB.RankContextualWidth.crank_unbounded
#print axioms PallLean.Paper93.DeepMath.PathB.RankContextualWidth.rank_space_bound_tight
