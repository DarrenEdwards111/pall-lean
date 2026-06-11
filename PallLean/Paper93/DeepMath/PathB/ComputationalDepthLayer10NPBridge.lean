import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer9KarpLipton

/-!
# Layer 10B — the circuit route to `P ≠ NP`, made precise (conditional bridges)

We are at the cliff: no further *separation* is honest.  This file builds **frontier infrastructure** that
makes any future circuit-based attack on `P` vs `NP` precise and falsifiable — clean complexity-class
definitions (separate from the TM-based `Step4Compiler`) and the two conditional bridges that connect a
general-circuit lower bound to `P ≠ NP`, with the genuinely-hard inputs kept as **explicit hypotheses**.

## Classes (sets of length-indexed boolean languages)

* `PpolyClass` — `P/poly` (poly-size general-circuit families, from Layer 9 `Ppoly`).
* `VerifierFamily` / `NPpoly` / `NPpolyClass` — a **clean nonuniform NP** ("NP/poly"): a poly-bounded
  witness length and a poly-size verifier circuit family.  Fully concrete, independent of `Step4Compiler`.
* `Ppoly_subset_NPpoly` — `P/poly ⊆ NP/poly` (a circuit is a verifier that ignores the witness).

## The bridges

* `np_not_subset_ppoly_of_hard` (**Bridge 1**) — an `NP` language with a super-polynomial circuit lower
  bound (`∉ P/poly`) witnesses `NP ⊄ P/poly`.
* `p_ne_np_of_np_not_subset_ppoly` (**Bridge 2**) — `NP ⊄ P/poly ⇒ P ≠ NP`, given `P ⊆ P/poly`.
* `p_ne_np_of_np_hard` — the composed target: **if `P ⊆ P/poly` and some `NP` language has a
  super-polynomial general-circuit lower bound, then `P ≠ NP`.**

## Honest status

These are *conditional* theorems.  The two hard inputs are explicit hypotheses, **never asserted**:
* `hhard : ¬ Ppoly L` for an `NP` language `L` — an **explicit super-polynomial general-circuit lower
  bound**.  This is the open, barrier-blocked frontier (`SCOPE_LAYER8_EXPLICIT_LOWER_BOUND_FRONTIER.md`);
  Layer 8 gives it only for a *nonexplicit* (Shannon) language and only an explicit *linear* bound.
* `hPsub : P ⊆ P/poly` — the standard inclusion `P ⊆ P/poly`.  True and classical, but its proof needs the
  uniform TM→circuit construction (off-limits here); it is fenced as a hypothesis.

Nothing here claims `NP ⊄ P/poly` or `P ≠ NP`.  The value is precision: it pins down *exactly* what an
honest circuit-route proof would have to supply.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer10

open PallLean.Paper93.DeepMath.PathB

/-- A complexity class as a set of length-indexed boolean languages. -/
abbrev ComplexityClass := Set Layer7.BoolLang

/-- **`P/poly`** as a class. -/
def PpolyClass : ComplexityClass := {L | Layer9.Ppoly L}

/-- A **nonuniform NP verifier** for `L`: a poly-bounded witness length `wit` and a poly-size verifier
circuit family `ver n : Circuit (n + wit n)` such that `L n x` holds iff some witness is accepted.
Concrete, and entirely separate from the TM-based `Step4Compiler`. -/
structure VerifierFamily (L : Layer7.BoolLang) where
  wit : ℕ → ℕ
  witPoly : Layer7.IsPolyBounded wit
  ver : (n : ℕ) → Layer8.Circuit (n + wit n)
  verSize : ℕ → ℕ
  verSizePoly : Layer7.IsPolyBounded verSize
  verSizeBound : ∀ n, (ver n).size ≤ verSize n
  correct : ∀ (n : ℕ) (x : Fin n → Bool),
    L n x = true ↔ ∃ w : Fin (wit n) → Bool, (ver n).eval (Fin.append x w) = true

/-- **NP/poly**: `L` has a nonuniform NP verifier. -/
def NPpoly (L : Layer7.BoolLang) : Prop := Nonempty (VerifierFamily L)

/-- **`NP/poly`** as a class. -/
def NPpolyClass : ComplexityClass := {L | NPpoly L}

/-- **`P/poly ⊆ NP/poly`.**  A circuit family for `L` is a verifier that ignores a zero-length witness. -/
theorem Ppoly_subset_NPpoly : PpolyClass ⊆ NPpolyClass := by
  rintro L ⟨p, hpoly, hsize⟩
  classical
  refine ⟨{
    wit := fun _ => 0
    witPoly := ⟨0, 0, 0, fun _ => by simp⟩
    ver := fun n => Classical.choose (hsize n)
    verSize := p
    verSizePoly := hpoly
    verSizeBound := fun n => (Classical.choose_spec (hsize n)).1
    correct := fun n x => ?_ }⟩
  have hcomp : (Classical.choose (hsize n)).eval = (fun x => L n x) := by
    funext y; exact (Classical.choose_spec (hsize n)).2 y
  have hax : Fin.append x (fun i : Fin 0 => Fin.elim0 i) = x := by
    funext i
    rw [Fin.append, Fin.addCases, dif_pos (show (i : ℕ) < n from i.is_lt)]
    rfl
  constructor
  · intro h; exact ⟨fun i => Fin.elim0 i, by rw [hax, hcomp]; exact h⟩
  · rintro ⟨w, hw⟩
    rw [show w = (fun i : Fin 0 => Fin.elim0 i) from by funext i; exact Fin.elim0 i, hax, hcomp] at hw
    exact hw

/-- **Bridge 1.**  An `NP` language with a super-polynomial circuit lower bound (`∉ P/poly`) witnesses
`NP ⊄ P/poly`.  The lower bound `hhard` is the open, explicitly-fenced hypothesis. -/
theorem np_not_subset_ppoly_of_hard {NP : ComplexityClass} {L : Layer7.BoolLang}
    (hLNP : L ∈ NP) (hhard : ¬ Layer9.Ppoly L) : ¬ (NP ⊆ PpolyClass) :=
  fun hsub => hhard (hsub hLNP)

/-- **Bridge 2.**  `NP ⊄ P/poly ⇒ P ≠ NP`, given the standard inclusion `P ⊆ P/poly` (true, but its proof
needs the uniform model; here it is the explicitly-fenced hypothesis `hPsub`). -/
theorem p_ne_np_of_np_not_subset_ppoly {P NP : ComplexityClass}
    (hPsub : P ⊆ PpolyClass) (hsep : ¬ (NP ⊆ PpolyClass)) : P ≠ NP :=
  fun hPeqNP => hsep (hPeqNP ▸ hPsub)

/-- **The circuit route to `P ≠ NP`, made precise.**  If `P ⊆ P/poly` (standard) and some `NP` language has
a super-polynomial general-circuit lower bound (`∉ P/poly`, open), then `P ≠ NP`.  Both hard inputs are
explicit hypotheses; neither is asserted. -/
theorem p_ne_np_of_np_hard {P NP : ComplexityClass} (hPsub : P ⊆ PpolyClass)
    {L : Layer7.BoolLang} (hLNP : L ∈ NP) (hhard : ¬ Layer9.Ppoly L) : P ≠ NP :=
  p_ne_np_of_np_not_subset_ppoly hPsub (np_not_subset_ppoly_of_hard hLNP hhard)

/-- The concrete `NP/poly` class plugs straight into Bridge 1: an `NP/poly` language outside `P/poly`
witnesses `NP/poly ⊄ P/poly`. -/
theorem npPoly_not_subset_ppoly_of_hard {L : Layer7.BoolLang}
    (hL : NPpoly L) (hhard : ¬ Layer9.Ppoly L) : ¬ (NPpolyClass ⊆ PpolyClass) :=
  np_not_subset_ppoly_of_hard hL hhard

end PallLean.Paper93.DeepMath.PathB.Layer10

#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.p_ne_np_of_np_hard
#print axioms PallLean.Paper93.DeepMath.PathB.Layer10.Ppoly_subset_NPpoly
