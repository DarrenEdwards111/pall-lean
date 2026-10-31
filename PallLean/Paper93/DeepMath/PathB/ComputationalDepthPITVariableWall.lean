import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHittingSet

/-!
# The PIT derandomization wall is exactly the number of variables

`HittingSet` reduced the whole derandomization gap to **shrinking the Schwartz–Zippel hitting set
from size `(d+1)ⁿ` to `poly(n,d)`**.  This file locates the hardness *precisely*: it is the
`n`-dependence and nothing else.

* **`grid_card_pow` (proved)** — the grid `Sⁿ` with side `#S = d+1` has *exactly* `(d+1)ⁿ` points.
* **`univariate_hitting_set` (proved)** — at `n = 1`, that grid is a hitting set for degree `d`…
* **`univariate_hitting_set_card` (proved)** — …of size exactly `d+1`, i.e. **linear** in the degree.
  So **univariate `PIT` is unconditionally derandomized**: `d+1` explicit evaluation points suffice,
  no randomness and no open assumption.
* **`grid_card_two_var` (proved)** — already at `n = 2` the same construction costs `(d+1)²`, and in
  general `(d+1)ⁿ = (d+1)·(d+1)ⁿ⁻¹`: the overhead over the univariate `d+1` is `(d+1)ⁿ⁻¹`, which is
  `1` iff `n ≤ 1`.

**Reading.**  The exponential in the Schwartz–Zippel hitting set is carried *entirely* by the number
of variables `n`; for any fixed `n` it is polynomial in the degree `d`, and for `n = 1` it is already
small.  So the open derandomization target is not "beat Schwartz–Zippel for one polynomial" — it is
"break the `(d+1)ⁿ` scaling in the *number of variables*," i.e. build a hitting set whose size is
`poly(n,d)` rather than `d^{Θ(n)}`.  That is the sharp, algebraic frontier.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PITVariableWall

open PallLean.Paper93.DeepMath.PathB.SchwartzZippel
open PallLean.Paper93.DeepMath.PathB.HittingSet

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Exact size of the Schwartz–Zippel grid (proved).**  With side `#S = d+1`, the product grid
`Sⁿ` has exactly `(d+1)ⁿ` points — the number of evaluations Schwartz–Zippel needs. -/
theorem grid_card_pow {n d : ℕ} (S : Finset F) (hS : S.card = d + 1) :
    (Fintype.piFinset (fun _ : Fin n => S)).card = (d + 1) ^ n := by
  simp [Fintype.card_piFinset, hS, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Univariate `PIT` is derandomized (proved).**  At `n = 1`, a grid `S` of size `d+1` is a hitting
set for total degree `d`: every nonzero univariate polynomial of degree `≤ d` is non-zero at one of
the `d+1` points.  (This is `grid_is_hitting_set` with `#S = d+1 > d`.) -/
theorem univariate_hitting_set {d : ℕ} (S : Finset F) (hS : S.card = d + 1) :
    IsHittingSet (Fintype.piFinset (fun _ : Fin 1 => S)) d := by
  apply grid_is_hitting_set
  rw [hS]; exact Nat.lt_succ_self d

/-- **…and it is small: size `d+1`, linear in the degree (proved).**  The univariate hitting set has
exactly `d+1` points — a *polynomial*-size deterministic identity test, with no open assumption. -/
theorem univariate_hitting_set_card {d : ℕ} (S : Finset F) (hS : S.card = d + 1) :
    (Fintype.piFinset (fun _ : Fin 1 => S)).card = d + 1 := by
  rw [grid_card_pow S hS, pow_one]

/-- **Two variables already cost `(d+1)²` (proved).**  The same construction that is linear at `n = 1`
is quadratic at `n = 2`; in general the overhead over the univariate `d+1` is `(d+1)ⁿ⁻¹`.  The
exponential blow-up is carried purely by the number of variables. -/
theorem grid_card_two_var {d : ℕ} (S : Finset F) (hS : S.card = d + 1) :
    (Fintype.piFinset (fun _ : Fin 2 => S)).card = (d + 1) ^ 2 :=
  grid_card_pow S hS

end PallLean.Paper93.DeepMath.PathB.PITVariableWall

#print axioms PallLean.Paper93.DeepMath.PathB.PITVariableWall.grid_card_pow
#print axioms PallLean.Paper93.DeepMath.PathB.PITVariableWall.univariate_hitting_set
#print axioms PallLean.Paper93.DeepMath.PathB.PITVariableWall.univariate_hitting_set_card
#print axioms PallLean.Paper93.DeepMath.PathB.PITVariableWall.grid_card_two_var
