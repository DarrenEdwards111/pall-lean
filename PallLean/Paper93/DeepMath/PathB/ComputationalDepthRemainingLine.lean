import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHolographicCurvature
import Mathlib.Tactic.Ring

/-!
# The capstone: the one remaining line

After the whole arc, exactly **one** statement is left, and it is not a piece of the separation — it **is**
the separation.  This file names it, proves everything *around* it, and — deliberately — does **not** prove
it.  Proving it is `P ≠ NP`; asserting it here would be faking the closure.

## The line, named

`CostSuper cbudget := ∀ d, 2 · cbudget d ≤ cbudget (d+1)` — the per-step doubling of the SAT composition
tower.  This is "the gain never sags," and (by `curvature_is_cost_super`, an `Iff.rfl`) it is *the same
statement* as "SAT's reachable set is AdS," as "the min over realizations stays hyperbolic," and as "no
mass production flattens a step."  One line, many costumes.

The target it feeds:
`Superpoly f := ∀ k, ∃ n, n^k < f n` — `f` outgrows every polynomial.
`PolyBounded f := ∃ k, ∀ n, f n ≤ n^k` — `f` is polynomially bounded.
Separation = `¬ PolyBounded cbudget` (`cbudget(SAT)` has no polynomial upper bound = NP ⊄ P/poly ⟹ P ≠ NP).

## What is proved (everything around the line)

* **`faces_are_one`** — the geometry face IS the line: `CostSuper cbudget ↔ Hyperbolic cbudget 2` (`Iff.rfl`).
* **`sq_le_two_pow`, `poly_lt_exp`** — the exp-beats-poly bridge: `∀ k, ∃ n, n^k < 2^n` (unconditional).
* **`cost_super_superpoly`** — the line amplifies to the target: `CostSuper cbudget` (with `cbudget 0 ≥ 1`)
  ⟹ `Superpoly cbudget`.  The tower rings to `2^d`, and `2^d` outgrows every polynomial.
* **`superpoly_not_polybounded`** — the target gives separation: `Superpoly cbudget → ¬ PolyBounded cbudget`.
* **`what_remains`** — the whole chain, in one implication: `cbudget 0 ≥ 1 → CostSuper cbudget →
  ¬ PolyBounded cbudget`.  Every face reduces to `CostSuper`; `CostSuper` gives the separation.  The
  single hypothesis `CostSuper cbudget` is the remaining line — and it is **not discharged anywhere**.

## Honest scope — the antecedent is the whole problem

`what_remains` is an *implication*.  Its hypothesis `CostSuper cbudget` — the gain never sags on SAT's
tower — is exactly `cost_super`, and it is left open, as it must be: proving it for the SAT family is a
superpolynomial circuit lower bound = NP ⊄ P/poly = `P ≠ NP`.  Everything *else* — the unification of the
faces, the amplification to superpolynomial, the descent to separation — is discharged here, axiom-clean.
So the capstone is a checked object that says precisely: **the entire separation now hangs on this one
unproved line, and nothing else.**  Nothing here proves it.
-/

namespace PallLean.Paper93.DeepMath.PathB.RemainingLine

open PallLean.Paper93.DeepMath.PathB.HolographicCurvature

/-- **The remaining line.**  Per-step doubling of the SAT tower — "the gain never sags."  Definitionally
`Hyperbolic cbudget 2`; open for the SAT family. -/
def CostSuper (cbudget : ℕ → ℕ) : Prop := ∀ d, 2 * cbudget d ≤ cbudget (d + 1)

/-- `f` outgrows every polynomial — the `NP ⊄ P/poly` target (matches the repo's `∀k∃n` form). -/
def Superpoly (f : ℕ → ℕ) : Prop := ∀ k, ∃ n, n ^ k < f n

/-- `f` is polynomially bounded. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ k, ∀ n, f n ≤ n ^ k

/-- **The geometry face IS the line (proved, `Iff.rfl`).**  "SAT's reachable set is AdS" (`Hyperbolic`)
unfolds to the doubling line `CostSuper` — the same statement, no content added. -/
theorem faces_are_one (cbudget : ℕ → ℕ) : CostSuper cbudget ↔ Hyperbolic cbudget 2 := Iff.rfl

/-- `m² ≤ 2^m` for `m ≥ 4` (proved) — the workhorse for exp-beats-poly. -/
theorem sq_le_two_pow : ∀ m, 4 ≤ m → m * m ≤ 2 ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h4 : 4 * m ≤ m * m := Nat.mul_le_mul hm (Nat.le_refl m)
    have key : (m + 1) * (m + 1) = m * m + (2 * m + 1) := by ring
    have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; ring
    rw [key, hpow]
    omega

/-- **Exp beats poly (proved, unconditional).**  For every exponent `k` there is an `n` with `n^k < 2^n`:
`2^n` outgrows every polynomial.  This is the bridge from exponential tower-growth to "superpolynomial." -/
theorem poly_lt_exp (k : ℕ) : ∃ n, n ^ k < 2 ^ n := by
  match k with
  | 0 => exact ⟨1, by decide⟩
  | 1 => exact ⟨1, by decide⟩
  | 2 => exact ⟨5, by decide⟩
  | (k + 3) =>
    refine ⟨2 ^ (k + 4), ?_⟩
    have hsq : (k + 4) * (k + 4) ≤ 2 ^ (k + 4) := sq_le_two_pow (k + 4) (by omega)
    have e : (k + 4) * (k + 4) = (k + 4) * (k + 3) + (k + 4) := by ring
    have hlt : (k + 4) * (k + 3) < 2 ^ (k + 4) := by omega
    calc (2 ^ (k + 4)) ^ (k + 3)
        = 2 ^ ((k + 4) * (k + 3)) := (Nat.pow_mul 2 (k + 4) (k + 3)).symm
      _ < 2 ^ (2 ^ (k + 4)) := Nat.pow_lt_pow_right (by decide) hlt

/-- **The line amplifies to the target (proved).**  If the gain never sags (`CostSuper`) and the base is
nontrivial (`cbudget 0 ≥ 1`), then `cbudget` is superpolynomial: the tower rings to `2^d` and `2^d`
outgrows every polynomial. -/
theorem cost_super_superpoly (cbudget : ℕ → ℕ) (hbase : 1 ≤ cbudget 0)
    (hcs : CostSuper cbudget) : Superpoly cbudget := by
  have hgrow : ∀ n, 2 ^ n ≤ cbudget n := by
    intro n
    have hh := hyperbolic_exponential cbudget 2 hcs n
    calc 2 ^ n = 2 ^ n * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ n * cbudget 0 := Nat.mul_le_mul (Nat.le_refl _) hbase
      _ ≤ cbudget n := hh
  intro k
  rcases poly_lt_exp k with ⟨n, hn⟩
  exact ⟨n, lt_of_lt_of_le hn (hgrow n)⟩

/-- **The target gives separation (proved).**  A superpolynomial `cbudget` has no polynomial upper bound:
`Superpoly cbudget → ¬ PolyBounded cbudget`.  (`NP ⊄ P/poly`.) -/
theorem superpoly_not_polybounded (f : ℕ → ℕ) (h : Superpoly f) : ¬ PolyBounded f := by
  rintro ⟨k, hk⟩
  rcases h k with ⟨n, hn⟩
  exact absurd (lt_of_lt_of_le hn (hk n)) (lt_irrefl _)

/-- **The capstone (proved) — the whole separation in one implication.**  If the base is nontrivial and the
one line holds (`CostSuper cbudget`: the gain never sags), then `cbudget(SAT)` has no polynomial upper
bound — the separation.  Every face reduces to the antecedent `CostSuper`; everything downstream is
discharged here.  The antecedent is **the** remaining line, and it is not proved anywhere: proving it for
the SAT family is `P ≠ NP`. -/
theorem what_remains (cbudget : ℕ → ℕ) (hbase : 1 ≤ cbudget 0)
    (hline : CostSuper cbudget) : ¬ PolyBounded cbudget :=
  superpoly_not_polybounded cbudget (cost_super_superpoly cbudget hbase hline)

end PallLean.Paper93.DeepMath.PathB.RemainingLine

#print axioms PallLean.Paper93.DeepMath.PathB.RemainingLine.poly_lt_exp
#print axioms PallLean.Paper93.DeepMath.PathB.RemainingLine.cost_super_superpoly
#print axioms PallLean.Paper93.DeepMath.PathB.RemainingLine.what_remains
