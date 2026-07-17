import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCodec

/-!
# THE SEPARATION TARGET: `SAT ∉ P`, stated minimally and honestly

E6 closed the observer-class Cook–Levin engineering: the reduction is emitted by a
proven machine in proven polynomial time.  That machinery is TRUE REGARDLESS of whether
`P = NP`.  What separation requires — and what NOTHING in this repository proves — is
the statement in this file: a lower bound showing every polynomial-time machine fails
to decide satisfiability.

This file contains NO theorem claiming the target.  It states the target as a single
`Prop` built exclusively from the repository's proven-semantics definitions — the
faithful `ComposableMachine` model (halt-flag semantics, closure under composition
proved), `Decides` (the machine halts within the clock and its output matches the
language on EVERY input), `PolyBounded` (an explicit `c·(n+1)^k` bound), and the
coordinate formula codec (round-trip faithfulness proved) — with no residual
propositions hidden behind names.  The one classical ingredient is stated in the open:
`SATLang` uses `Classical.propDecidable` to make the mathematical language a `Bool`
function; `Decides` requires only that the machine's outputs MATCH it.

Status (2026-07): open.  Every restricted lower bound in this repository (AC⁰[p],
switching, Nečiporuk, SPDP-rank, cross-model) falls short of this statement, and the
candidate bridges toward it are unproved conjectures of full `P ≠ NP` strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.SeparationTarget

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction (Satisfiable)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec

/-- **The SAT language** over the coordinate codec: a word is accepted iff it decodes
to a satisfiable formula.  Classical (`propDecidable`): this is the mathematical
language, not an algorithm — deciding it IS the problem. -/
noncomputable def SATLang (w : List Bool) : Bool :=
  if Satisfiable (decodeFormula' w) then true else false

/-- **Membership in P**, faithfully: some machine decides `L` on every input within
some polynomially bounded clock. -/
def InP (L : List Bool → Bool) : Prop :=
  ∃ (M : Machine) (T : ℕ → ℕ), PolyBounded T ∧ Decides M L T

/-- **THE TARGET.**  This proposition — nothing weaker — is the separation.  It is not
proved anywhere in this repository. -/
def SAT_not_in_P : Prop := ¬ InP SATLang

/-! ## Sanity: the target means what it says -/

/-- `SATLang` agrees with satisfiability on every encoded formula — the codec hides
nothing. -/
theorem SATLang_encode
    (φ : PallLean.Paper93.DeepMath.PathB.CookLevinReduction.Formula) :
    SATLang (encodeFormula' φ) = true ↔ Satisfiable φ := by
  rw [SATLang, decodeFormula'_encodeFormula']
  constructor
  · intro h
    by_contra hn
    rw [if_neg hn] at h
    exact Bool.false_ne_true h
  · intro h
    rw [if_pos h]

/-- Unfolded in full: the target quantifies over EVERY machine and EVERY polynomially
bounded clock — no machine model restrictions, no observer classes, no hidden
hypotheses. -/
theorem SAT_not_in_P_iff :
    SAT_not_in_P ↔ ∀ (M : Machine) (T : ℕ → ℕ), PolyBounded T →
      ¬ (∀ x, HaltsBy M x (T x.length) ∧ decideOut M x (T x.length) = SATLang x) := by
  constructor
  · intro h M T hT hd
    exact h ⟨M, T, hT, hd⟩
  · intro h ⟨M, T, hT, hd⟩
    exact h M T hT hd

end PallLean.Paper93.DeepMath.PathB.SeparationTarget
