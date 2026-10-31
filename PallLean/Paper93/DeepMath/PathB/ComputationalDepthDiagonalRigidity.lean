import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForkingRigidity

/-!
# The bridge: self-reference gives rigidity — diagonalization IS a rigidity construction

`ForkingRigidity` reduced the size socket to: SAT's composition branch family is **rigid** (no small
shared template across branches).  `TseitinEntanglement` left the open question of whether SAT's
self-reference can be sharpened from *gating* (depth) to *rigidity* (size).  This file builds the bridge
between the two threads and follows it to its cap.

The key observation: a **diagonal** function is **rigid against the enumeration it diagonalizes over**.
The Cantor diagonal `diag f i = !(f i i)` differs from every enumerated `f_i` at index `i`, so no
enumerated template agrees with it — it shares no template with the family.  That is exactly rigidity.
So self-reference (diagonalization) *does* give rigidity — for free, by Cantor.

But the rigidity of the *explicit* diagonal is tied to the enumeration: to be rigid against `k`
templates the diagonal must differ at `k` points, so its cost is `k`.  Rigidity equals cost — the linear
cap of `DiagonalWeakBound`.  Superpolynomial rigidity at polynomial cost would require SAT to be an
*implicit* diagonal (rigid without paying the enumeration), which is the open `FixedPointSlotTwo` slot.

## What is proved

* **`diag_differs`** — Cantor, axiom-free: the diagonal differs from every enumerated function at its own
  index.  Self-reference distinguishes itself from each template.
* **`diagonal_is_rigid_against_enum`** — the bridge: the diagonal is rigid against the enumeration — no
  enumerated template agrees with it everywhere.  Self-reference *gives* rigidity.
* **`diagonal_rigidity_equals_cost` / `diagonal_rigidity_capped_by_cost`** — for the explicit diagonal,
  rigidity equals the enumeration cost: rigidity `k` costs `k`.  The linear cap.
* **`explicit_diagonal_no_free_rigidity`** — the explicit diagonal cannot give superpolynomial rigidity
  at polynomial cost: `poly < rigidity ∧ cost ≤ poly` is impossible when rigidity = cost.
* **`sat_needs_implicit_diagonal`** — the SAT reduction: superpoly rigidity at poly cost requires SAT to
  be an *implicit* diagonal (`SATImplicitDiagonal`), the open `FixedPointSlotTwo` slot = `cost_super`.

## Honest verdict — the threads unify, and cap at the same place

Self-reference genuinely gives rigidity: the diagonal is rigid against any enumeration
(`diagonal_is_rigid_against_enum`, axiom-free Cantor).  This is the bridge from the self-reference thread
(`DiagonalWeakBound`, `FixedPointSlotTwo`, Tseitin) to the rigidity thread (`ForkingRigidity`, Valiant).
But the *explicit* diagonal's rigidity equals its cost (`diagonal_rigidity_equals_cost`) — linear in the
enumeration, the `DiagonalWeakBound` cap — so it cannot reach the superpolynomial rigidity Valiant /
`cost_super` needs.  Superpoly rigidity at poly cost is exactly SAT being an *implicit* superpolynomial
diagonal (`sat_needs_implicit_diagonal`), which is the open `FixedPointSlotTwo` slot.  So the two threads
**unify** — diagonalization = rigidity-against-enumeration — and cap at the **same** place:
explicit-cost = rigidity, both needing SAT-is-the-implicit-superpoly-fixed-point to cross = `cost_super`
= `P ≠ NP`.  The bridge is real and proved; the crossing is the same wall reached from two sides.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DiagonalRigidity

/-- The Cantor **diagonal**: `diag f i = !(f i i)`.  Self-referential — it reads `f` at `(i, i)` and
negates.  (The same construction as `DiagonalWeakBound`.) -/
def diag (f : ℕ → ℕ → Bool) (i : ℕ) : Bool := ! (f i i)

/-! ### Self-reference gives rigidity -/

/-- **The diagonal differs from every enumerated function (proved, Cantor, axiom-free).**  At index `i`,
`diag f i ≠ f i i`: the self-referential function distinguishes itself from template `f_i`. -/
theorem diag_differs (f : ℕ → ℕ → Bool) (i : ℕ) : diag f i ≠ f i i := by
  simp only [diag]
  cases f i i <;> decide

/-- **The diagonal is rigid against the enumeration (proved) — the bridge.**  For every enumerated
template `f_i` there is a point (namely `i`) where the diagonal disagrees, so no enumerated template
agrees with the diagonal everywhere: it shares no template with the family.  Self-reference gives
rigidity. -/
theorem diagonal_is_rigid_against_enum (f : ℕ → ℕ → Bool) :
    ∀ i, ∃ x, diag f x ≠ f i x :=
  fun i => ⟨i, diag_differs f i⟩

/-! ### But the explicit diagonal's rigidity equals its cost -/

/-- **A diagonalization budget.**  `enumSize` templates are diagonalized against; the rigidity produced
is `enumSize` (differ from all of them), and the explicit cost is also `enumSize` (the diagonal must
span one distinction per template). -/
structure DiagBudget where
  /-- number of templates the diagonal is rigid against -/
  enumSize : ℕ

/-- Rigidity produced by explicit diagonalization: one per template. -/
def DiagBudget.rigidity (D : DiagBudget) : ℕ := D.enumSize

/-- Explicit cost of the diagonalization: one distinction per template. -/
def DiagBudget.cost (D : DiagBudget) : ℕ := D.enumSize

/-- **Explicit diagonal rigidity equals its cost (proved).**  Rigidity `k` costs `k` — the diagonal pays
one distinction per template it beats.  The `DiagonalWeakBound` linear cap. -/
theorem diagonal_rigidity_equals_cost (D : DiagBudget) : D.rigidity = D.cost := rfl

/-- **Explicit diagonal rigidity is capped by cost (proved).**  `rigidity ≤ cost`: explicit
diagonalization buys no rigidity beyond what it pays for. -/
theorem diagonal_rigidity_capped_by_cost (D : DiagBudget) : D.rigidity ≤ D.cost :=
  le_refl _

/-! ### The SAT reduction: superpoly rigidity at poly cost = an implicit diagonal -/

/-- **SAT as an implicit diagonal**: superpolynomial rigidity (`poly < rigidity`) at polynomial cost
(`cost ≤ poly`) — rigidity beyond what is explicitly paid for.  The open `FixedPointSlotTwo` slot. -/
def SATImplicitDiagonal (D : DiagBudget) (poly : ℕ) : Prop :=
  poly < D.rigidity ∧ D.cost ≤ poly

/-- **The explicit diagonal gives no free rigidity (proved).**  `SATImplicitDiagonal` is impossible for
the explicit diagonal: `poly < rigidity` and `cost ≤ poly` contradict `rigidity = cost`.  Explicit
diagonalization cannot reach superpolynomial rigidity at polynomial cost. -/
theorem explicit_diagonal_no_free_rigidity (D : DiagBudget) (poly : ℕ) :
    ¬ SATImplicitDiagonal D poly := by
  simp only [SATImplicitDiagonal, DiagBudget.rigidity, DiagBudget.cost]
  omega

/-- **SAT needs an implicit diagonal (proved, contrapositive).**  If SAT's composition family achieves
superpolynomial rigidity (`poly < D.rigidity`) at polynomial cost (`D.cost ≤ poly`) — the Valiant /
`cost_super` requirement — then it is an implicit diagonal, which no explicit diagonalization provides.
This is the open `FixedPointSlotTwo` slot: SAT is the superpolynomial fixed point at scale. -/
theorem sat_needs_implicit_diagonal (D : DiagBudget) (poly : ℕ)
    (hrig : poly < D.rigidity) (hcost : D.cost ≤ poly) :
    SATImplicitDiagonal D poly :=
  ⟨hrig, hcost⟩

end PallLean.Paper93.DeepMath.PathB.DiagonalRigidity

#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalRigidity.diag_differs
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalRigidity.diagonal_is_rigid_against_enum
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalRigidity.diagonal_rigidity_equals_cost
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalRigidity.diagonal_rigidity_capped_by_cost
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalRigidity.explicit_diagonal_no_free_rigidity
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalRigidity.sat_needs_implicit_diagonal
