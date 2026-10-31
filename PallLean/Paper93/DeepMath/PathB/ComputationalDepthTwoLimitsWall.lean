import Mathlib.Data.Nat.Basic

/-!
# The wall is the interval between the two observers' limits — that interval is the separation

Darren's framing, formalized: the inside (P) observer certifies an **upper** limit `U` on cost — the
reach of `P`; the outside observer certifies a **lower** limit `L` on the target — the floor `SAT`
requires.  The **wall is the open interval `(U, L)`**, and the separation is exactly the assertion that
this interval is nonempty: the lower limit clears the upper.

This unifies the God-Move rank picture with the NP-ceiling `cbudget` route: `U k n = n^k + k` is the
poly ceiling the inside observer can certify at degree `k`; `L n` is the floor the outside observer
certifies on `SAT` at size `n`; and the separation is `∀ k, ∃ n, U k n < L n` — the floor eventually
clears every poly ceiling.

## What is proved

* **`gap_separates` (proved)** — the wall as a gap: if the outside limit `L` strictly exceeds the inside
  limit `U`, the target is not a P-compilation (`L ≤ cost sat` and `PComp sat ⟹ cost sat ≤ U ⟹ L ≤ U`,
  contradicting `U < L`).  This is Darren's sentence: *the gap between the limits is the separation.*
* **`limits_apart_separates` (proved)** — the scale-indexed form: at any scale `n` where the poly
  ceiling `U k n` sits below the floor `L n`, that scale is separated.
* **`overlap_no_separation` (proved)** — the honest converse: when the limits *overlap* (`L ≤ U`), no
  separation follows — a concrete model with `L ≤ U` and `PComp sat` both holding.
* **`certified_linear_below_quadratic` (proved)** — the honest status: the *best certified* lower limit
  is only linear (`c₀·n`, the circuit floor), and it sits **below** even a quadratic slice of the P
  ceiling once `n ≥ c₀`.  So the certified interval is **empty**: the two observers' *proved* limits do
  not yet separate.  The wall is exactly the distance from the certified `L` up to a superpoly `L`.

## Honest scope

The structure is proved: *if* the limits are apart, that is the separation.  What is **not** proved — and
is exactly `P ≠ NP` — is that the limits are apart: that the certified lower limit `L` can be pushed
above every poly ceiling `U`.  The best proved `L` is linear and sits under the ceiling
(`certified_linear_below_quadratic`).  So this file states Darren's characterization exactly and marks,
quantitatively, how far the certified limits still are from meeting the requirement.  Nothing here is
`P ≠ NP`; it is the wall, drawn as an interval.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoLimitsWall

/-- **The wall is the gap between the limits (proved).**  Inside observer: every P-compilation costs
`≤ U` (P's reach — the upper limit).  Outside observer: `L ≤ cost sat` (SAT's floor — the lower limit).
If the lower limit strictly clears the upper (`U < L`), the target is not a P-compilation.  The open
interval `(U, L)` is the wall, and its non-emptiness *is* the separation. -/
theorem gap_separates {Obj : Type} (cost : Obj → ℕ) (PComp : Obj → Prop) (sat : Obj)
    (U L : ℕ)
    (inside_upper : ∀ o, PComp o → cost o ≤ U)
    (outside_lower : L ≤ cost sat)
    (gap : U < L) :
    ¬ PComp sat := by
  intro h
  have hup := inside_upper sat h
  omega

/-- **Scale-indexed form (proved).**  With a poly-ceiling family `U k n` (degree `k`, size `n`) and a
floor `L n`: at any scale `n` where the floor clears the ceiling (`U k n < L n`), that scale is separated
— the size-`n` instance is not P-bounded at degree `k`. -/
theorem limits_apart_separates
    (cost : ℕ → ℕ) (PBounded : ℕ → ℕ → Prop) (U : ℕ → ℕ → ℕ) (L : ℕ → ℕ)
    (inside : ∀ k n, PBounded k n → cost n ≤ U k n)
    (outside : ∀ n, L n ≤ cost n)
    (k n : ℕ) (gap : U k n < L n) :
    ¬ PBounded k n := by
  intro h
  have h1 := inside k n h
  have h2 := outside n
  omega

/-- **The separation, as limits eventually apart.**  Darren's characterization as the exact open target
of the NP-ceiling route: the outside observer's floor `L` eventually clears *every* poly ceiling `U k`
the inside observer can certify. -/
def LimitsEventuallyApart (U : ℕ → ℕ → ℕ) (L : ℕ → ℕ) : Prop :=
  ∀ k, ∃ n, U k n < L n

/-- **Honest converse (proved).**  When the certified limits overlap (`L ≤ U`), no separation follows:
here is a concrete world where `L ≤ U` holds together with `PComp sat`.  A gap is necessary — overlap is
consistent with membership. -/
theorem overlap_no_separation :
    ∃ (Obj : Type) (cost : Obj → ℕ) (PComp : Obj → Prop) (sat : Obj) (U L : ℕ),
      (∀ o, PComp o → cost o ≤ U) ∧ L ≤ cost sat ∧ L ≤ U ∧ PComp sat :=
  ⟨Unit, (fun _ => 0), (fun _ => True), (), 0, 0,
    (fun _ _ => Nat.le_refl 0), Nat.le_refl 0, Nat.le_refl 0, trivial⟩

/-- **The honest status (proved).**  The best *certified* lower limit is only linear, `c₀ · n` (the
circuit floor `~5n`), and once `n ≥ c₀` it sits below even a quadratic slice of the P ceiling.  So with
`U = n·n` and `L = c₀·n`, the certified interval `(U, L)` is empty — the two observers' *proved* limits
do not separate.  The wall is precisely the gap from this certified `L` up to a superpoly one. -/
theorem certified_linear_below_quadratic (c₀ n : ℕ) (h : c₀ ≤ n) :
    c₀ * n ≤ n * n :=
  Nat.mul_le_mul h (Nat.le_refl n)

end PallLean.Paper93.DeepMath.PathB.TwoLimitsWall

#print axioms PallLean.Paper93.DeepMath.PathB.TwoLimitsWall.gap_separates
#print axioms PallLean.Paper93.DeepMath.PathB.TwoLimitsWall.limits_apart_separates
#print axioms PallLean.Paper93.DeepMath.PathB.TwoLimitsWall.overlap_no_separation
#print axioms PallLean.Paper93.DeepMath.PathB.TwoLimitsWall.certified_linear_below_quadratic
