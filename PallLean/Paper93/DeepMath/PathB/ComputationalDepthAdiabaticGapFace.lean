import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Basic

/-!
# A face of the wall: the adiabatic spectral gap ties thermodynamic cost to `cost_super` — by theorem

The nearest *honest* physical handle on SAT hardness is not a collider but an adiabatic device forced to
solve worst-case SAT: encode SAT in a Hamiltonian whose ground state is the satisfying assignment, and
interpolate slowly.  The **adiabatic theorem** — an actual theorem, not a fit — says the annealing time
needed to stay in the ground state scales like the inverse *square* of the minimum spectral gap along
the path (`T ~ 1/g²`).  So "thermodynamic cost" (annealing time) is bound to the spectral gap by proof.

This file abstracts that bridge and proves the honest consequence:

* annealing time is polynomially bounded **iff** the inverse gap is (the gap is not superpolynomially
  small) — because squaring preserves polynomial growth;
* hence the solver is defeated by worst-case SAT **iff** its minimum gap closes superpolynomially.

That is `cost_super` drawn in physical coordinates: the physical shadow of "SAT is hard" is "the
adiabatic gap for worst-case SAT closes faster than any polynomial."

## Honest scope — two ceilings

Like the other wall faces, this **re-labels** the wall; it does not cross it.  Two ceilings are made
explicit and one is machine-checked:

1. **Open on both sides.**  The bridge is a proved *equivalence* between two solver-relative properties;
   `easySolver_not_hard` exhibits a solver whose gap stays open.  Whether the *SAT* solver's gap closes
   is exactly `cost_super`, undischarged.
2. **Doubly restricted.**  It bounds ONE physical model — an algorithm can bypass physical relaxation,
   so a gap lower bound is a restricted lower bound, not `SAT ∉ P`.  And adiabatic computation equals
   BQP, so even a full gap lower bound lands at `NP ⊄ BQP`, a quantum ceiling, not `P ≠ NP`.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AdiabaticGapFace

/-- Polynomial boundedness (mirrors the corpus `PolyBounded`): `∃ c d, ∀ n, T n ≤ c·(n+1)^d`. -/
def PolyBounded (T : ℕ → ℕ) : Prop := ∃ c d : ℕ, ∀ n, T n ≤ c * (n + 1) ^ d

/-- **Poly bounds are closed under squaring (proved).**  If `f` is polynomially bounded, so is
`fun n => f n * f n`.  This is the algebraic content of the adiabatic `T ~ 1/g²`: squaring the inverse
gap keeps it polynomial, so a poly gap gives a poly time and vice versa. -/
theorem PolyBounded.sq {f : ℕ → ℕ} (h : PolyBounded f) : PolyBounded (fun n => f n * f n) := by
  obtain ⟨c, d, hf⟩ := h
  refine ⟨c * c, d + d, fun n => ?_⟩
  calc f n * f n ≤ (c * (n + 1) ^ d) * (c * (n + 1) ^ d) := Nat.mul_le_mul (hf n) (hf n)
    _ = c * c * (n + 1) ^ (d + d) := by ring

/-- An abstract adiabatic/annealing solver for a problem family: its minimum **inverse** spectral gap
as a function of instance size (`gapInv n = 1/g(n)`, so large `gapInv` = small gap = hard), and its
annealing time.  The two fields are the adiabatic theorem, both directions. -/
structure AnnealingSolver where
  /-- Inverse minimum spectral gap along the interpolation, as a function of instance size. -/
  gapInv : ℕ → ℕ
  /-- The annealing time actually paid. -/
  annealTime : ℕ → ℕ
  /-- Adiabatic **necessity**: a small gap forces slow annealing — time is at least the inverse gap. -/
  time_ge_gap : ∀ n, gapInv n ≤ annealTime n
  /-- Adiabatic **sufficiency** (`T ~ 1/g²`, constant absorbed): the squared inverse gap suffices. -/
  time_le_gap_sq : ∀ n, annealTime n ≤ gapInv n * gapInv n

/-- **The bridge (proved): annealing time is polynomial ⟺ the gap is not superpolynomially small.**
By the adiabatic theorem (necessity + sufficiency), physical cost and the inverse gap are polynomially
tied.  This binds "thermodynamic cost" to the spectral gap BY THEOREM, not by fit. -/
theorem annealTime_poly_iff_gap_poly (S : AnnealingSolver) :
    PolyBounded S.annealTime ↔ PolyBounded S.gapInv := by
  constructor
  · rintro ⟨c, d, hb⟩
    exact ⟨c, d, fun n => le_trans (S.time_ge_gap n) (hb n)⟩
  · intro h
    obtain ⟨c, d, hb⟩ := PolyBounded.sq h
    exact ⟨c, d, fun n => le_trans (S.time_le_gap_sq n) (hb n)⟩

/-- The solver is defeated by worst-case SAT: its annealing time is not polynomially bounded. -/
def HardForSolver (S : AnnealingSolver) : Prop := ¬ PolyBounded S.annealTime

/-- The minimum gap closes superpolynomially: the inverse gap is not polynomially bounded. -/
def GapClosesSuperpoly (S : AnnealingSolver) : Prop := ¬ PolyBounded S.gapInv

/-- **The face (proved): the solver is defeated by SAT ⟺ its gap closes superpolynomially.**  The
physical hardness (superpolynomial annealing time) is EXACTLY the minimum spectral gap closing faster
than any polynomial.  This is `cost_super`'s physical shadow. -/
theorem hard_iff_gap_closes (S : AnnealingSolver) :
    HardForSolver S ↔ GapClosesSuperpoly S :=
  not_iff_not.mpr (annealTime_poly_iff_gap_poly S)

/-- A solver whose gap stays open (constant inverse gap): the adiabatic device runs in `O(1)` — SAT is
trivially easy for it.  A witness that the bridge does not, by itself, force hardness. -/
def easySolver : AnnealingSolver where
  gapInv := fun _ => 1
  annealTime := fun _ => 1
  time_ge_gap := fun _ => le_refl 1
  time_le_gap_sq := fun _ => by decide

/-- **Ceiling 1 (proved): the bridge does not force hardness.**  `easySolver`'s gap stays open, so it
is not hard — `hard_iff_gap_closes` genuinely relates two *solver-relative* properties, and deciding
whether the SAT solver's gap closes is the open content (`cost_super` in physical coordinates). -/
theorem easySolver_not_hard : ¬ HardForSolver easySolver := by
  unfold HardForSolver
  rw [not_not]
  exact ⟨1, 0, fun n => by simp [easySolver]⟩

/-- **Capstone (proved): the adiabatic gap re-labels `cost_super`, it does not decide it.**

For any annealing solver, physical cost (annealing time) is polynomially tied to the spectral gap
(`annealTime_poly_iff_gap_poly`), so the solver is defeated by SAT exactly when its gap closes
superpolynomially (`hard_iff_gap_closes`) — thermodynamic cost bound to the gap BY THEOREM.  But the
equivalence is solver-relative and open on both sides (`easySolver_not_hard`): whether the SAT solver's
gap closes is `cost_super` in physical coordinates, undischarged.  And the ceiling is doubly restricted:
it bounds ONE physical model (an algorithm can bypass annealing), and adiabatic computation equals BQP,
so even a full gap lower bound lands at `NP ⊄ BQP`, not `P ≠ NP`.  A face, not a crossing. -/
theorem adiabatic_gap_relabels (S : AnnealingSolver) :
    (HardForSolver S ↔ GapClosesSuperpoly S) ∧ ¬ HardForSolver easySolver :=
  ⟨hard_iff_gap_closes S, easySolver_not_hard⟩

end PallLean.Paper93.DeepMath.PathB.AdiabaticGapFace

#print axioms PallLean.Paper93.DeepMath.PathB.AdiabaticGapFace.annealTime_poly_iff_gap_poly
#print axioms PallLean.Paper93.DeepMath.PathB.AdiabaticGapFace.hard_iff_gap_closes
#print axioms PallLean.Paper93.DeepMath.PathB.AdiabaticGapFace.adiabatic_gap_relabels
