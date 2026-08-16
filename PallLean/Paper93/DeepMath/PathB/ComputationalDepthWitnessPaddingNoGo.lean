import Mathlib

/-!
# Witness padding defeats trace-only circuit lifting

Occurrence-separated traces can contain a genuine Cartesian product before
existential projection.  This file proves that such trace structure alone
cannot lower-bound circuits for the projected Boolean answer.  Any verifier
may be conjoined with an input-independent, satisfiable padding relation.  The
new trace coordinates expose that relation exactly, while the projected
decision predicate is unchanged.

In particular, a verifier whose projected answer is constantly true can carry
an arbitrary nonempty Cartesian trace relation.  Thus a lifting theorem for
unrestricted decision circuits must establish hardness of the projected
Boolean function itself; counting or charging pre-erasure transcripts is not
representation invariant.
-/

namespace PallLean.Paper93.DeepMath.PathB.WitnessPaddingNoGo

/-- A proof-relevant verifier.  Its decision predicate existentially erases
both the witness and the exposed trace. -/
structure TraceVerifier (Input Witness Trace : Type*) where
  accept : Input → Witness → Trace → Prop

namespace TraceVerifier

variable {Input Witness Trace : Type*}

/-- The Boolean predicate seen by a decision circuit. -/
def projected (V : TraceVerifier Input Witness Trace) (x : Input) : Prop :=
  ∃ w t, V.accept x w t

/-- Conjoin an arbitrary input-independent padding component. -/
def pad {PadWitness PadTrace : Type*}
    (V : TraceVerifier Input Witness Trace)
    (padding : PadWitness → PadTrace → Prop) :
    TraceVerifier Input (Witness × PadWitness) (Trace × PadTrace) where
  accept x w t := V.accept x w.1 t.1 ∧ padding w.2 t.2

/-- Satisfiable inert padding leaves the projected Boolean function exactly
unchanged. -/
theorem pad_projected_iff {PadWitness PadTrace : Type*}
    (V : TraceVerifier Input Witness Trace)
    (padding : PadWitness → PadTrace → Prop)
    (hpadding : ∃ pw pt, padding pw pt) (x : Input) :
    (V.pad padding).projected x ↔ V.projected x := by
  constructor
  · rintro ⟨⟨w, pw⟩, ⟨t, pt⟩, hV, _⟩
    exact ⟨w, t, hV⟩
  · rintro ⟨w, t, hV⟩
    rcases hpadding with ⟨pw, pt, hp⟩
    exact ⟨⟨w, pw⟩, ⟨t, pt⟩, hV, hp⟩

/-- Padding exposes its chosen trace relation without affecting the old
acceptance condition. -/
theorem pad_accept_iff {PadWitness PadTrace : Type*}
    (V : TraceVerifier Input Witness Trace)
    (padding : PadWitness → PadTrace → Prop)
    (x : Input) (w : Witness) (pw : PadWitness)
    (t : Trace) (pt : PadTrace) :
    (V.pad padding).accept x (w, pw) (t, pt) ↔
      V.accept x w t ∧ padding pw pt := by
  rfl

end TraceVerifier

/-- A verifier carrying an arbitrary Cartesian trace relation and ignoring
its genuine input. -/
def cartesianTraceVerifier (Input Row Col : Type*)
    (rowSupport : Row → Prop) (colSupport : Col → Prop) :
    TraceVerifier Input Unit (Row × Col) where
  accept _ _ trace := rowSupport trace.1 ∧ colSupport trace.2

/-- The exposed trace relation is exactly the requested Cartesian product. -/
theorem cartesianTraceVerifier_accept_iff
    {Input Row Col : Type*} (rowSupport : Row → Prop)
    (colSupport : Col → Prop) (x : Input) (r : Row) (c : Col) :
    (cartesianTraceVerifier Input Row Col rowSupport colSupport).accept
        x () (r, c) ↔ rowSupport r ∧ colSupport c := by
  rfl

/-- If each factor is nonempty, existential projection erases the whole
Cartesian relation and yields the constant-true decision predicate. -/
theorem cartesianTraceVerifier_projected_true
    {Input Row Col : Type*} (rowSupport : Row → Prop)
    (colSupport : Col → Prop)
    (hr : ∃ r, rowSupport r) (hc : ∃ c, colSupport c) (x : Input) :
    (cartesianTraceVerifier Input Row Col rowSupport colSupport).projected x := by
  rcases hr with ⟨r, hr⟩
  rcases hc with ⟨c, hc⟩
  exact ⟨(), (r, c), hr, hc⟩

/-- All four crossed traces really occur when two supported values are chosen
on each side. -/
theorem cartesianTraceVerifier_all_four
    {Input Row Col : Type*} (rowSupport : Row → Prop)
    (colSupport : Col → Prop) (x : Input)
    {r₀ r₁ : Row} {c₀ c₁ : Col}
    (hr₀ : rowSupport r₀) (hr₁ : rowSupport r₁)
    (hc₀ : colSupport c₀) (hc₁ : colSupport c₁) :
    let V := cartesianTraceVerifier Input Row Col rowSupport colSupport
    V.accept x () (r₀, c₀) ∧ V.accept x () (r₀, c₁) ∧
      V.accept x () (r₁, c₀) ∧ V.accept x () (r₁, c₁) := by
  exact ⟨⟨hr₀, hc₀⟩, ⟨hr₀, hc₁⟩, ⟨hr₁, hc₀⟩, ⟨hr₁, hc₁⟩⟩

/-- Concrete two-by-two witness: a constant Boolean function coexists with a
full four-corner trace rectangle. -/
theorem bool_four_corner_constant_true (x : Bool) :
    let V := cartesianTraceVerifier Bool Bool Bool (fun _ => True) (fun _ => True)
    V.projected x ∧
      V.accept x () (false, false) ∧ V.accept x () (false, true) ∧
      V.accept x () (true, false) ∧ V.accept x () (true, true) := by
  simp [TraceVerifier.projected, cartesianTraceVerifier]

end PallLean.Paper93.DeepMath.PathB.WitnessPaddingNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.WitnessPaddingNoGo.TraceVerifier.pad_projected_iff
#print axioms PallLean.Paper93.DeepMath.PathB.WitnessPaddingNoGo.cartesianTraceVerifier_projected_true
#print axioms PallLean.Paper93.DeepMath.PathB.WitnessPaddingNoGo.cartesianTraceVerifier_all_four
#print axioms PallLean.Paper93.DeepMath.PathB.WitnessPaddingNoGo.bool_four_corner_constant_true
