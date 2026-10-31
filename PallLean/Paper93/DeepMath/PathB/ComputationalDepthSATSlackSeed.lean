import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATFamilyDenseFloor

/-!
# The SAT slack seed: an unsplittable triple inside the codec

Hunting the above-floor slack the rate-3 boundary demands.  Cone-floor attainers
(`cbudget = 2d − 1`) are forced — by the equality analysis of the parent-edge
counting — into read-once tree circuits: `d` fanout-one `var` gates, `d − 1` binary
gates, no reconvergence.  Read-once functions split at every variable:
`f = op (xᵢ, g(rest))` up to tree order.  This file plants the SAT-side obstruction:

* **`SAT_embeds_allEq3` (proved)**: the three sign bits of `(x₀^{s₁}) ∧ (x₀^{s₂}) ∧
  (x₀^{s₃})` realize **AllEqual₃** through the actual codec — satisfiable exactly
  when the signs agree;
* **`allEq3_no_split_a/b/c` (proved, by decide over all 256 candidate splits)**:
  AllEqual₃ admits NO decomposition `op (xᵢ, g(x_j, x_k))` at any of its three
  variables — it is not read-once, in the strongest per-variable sense.

**The remaining structure theorem, recorded**: floor-attainment ⟹ read-once
(equality analysis: cone = circuit, injection bijective, fanout one, no `un`/`cst`)
⟹ every triple-restriction splits somewhere.  With this seed, that theorem yields
`cbudget ≥ 2·deps` on the SAT slices — the first slack over the cone floor, opening
the rate-3 invariant's door.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATSlackSeed

open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec

/-- All-equal on three bits. -/
def allEq3 (a b c : Bool) : Bool := (a == b) && (b == c)

/-- The three-sign formula family: `(x₀^{s₁}) ∧ (x₀^{s₂}) ∧ (x₀^{s₃})`. -/
def se (s₁ s₂ s₃ : Bool) : Formula :=
  [[((0 : ℕ), s₁)], [((0 : ℕ), s₂)], [((0 : ℕ), s₃)]]

theorem unsat_of_conflict (φ : Formula) (h1 : [((0 : ℕ), true)] ∈ φ)
    (h0 : [((0 : ℕ), false)] ∈ φ) : ¬ Satisfiable φ := by
  rintro ⟨a, ha⟩
  rw [evalFormula, List.all_eq_true] at ha
  have ht := ha _ h1
  have hf := ha _ h0
  simp only [evalClause, List.any_cons, List.any_nil, evalLit, Bool.or_false,
    beq_iff_eq] at ht hf
  rw [ht] at hf
  simp at hf

/-- **The codec realizes AllEqual₃ (proved)**: the satisfiability of the three-sign
word is exactly agreement of the signs. -/
theorem SAT_embeds_allEq3 (t₁ t₂ t₃ : Bool) :
    SATLang (encodeFormula' (se t₁ t₂ t₃)) = allEq3 t₁ t₂ t₃ := by
  rw [SATLang, decodeFormula'_encodeFormula']
  cases t₁ <;> cases t₂ <;> cases t₃
  · rw [if_pos ⟨fun _ => false, by decide⟩]; rfl
  · rw [if_neg (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [if_neg (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [if_neg (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [if_neg (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [if_neg (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [if_neg (unsat_of_conflict _ (by decide) (by decide))]; rfl
  · rw [if_pos ⟨fun _ => true, by decide⟩]; rfl

/-- AllEqual₃ has no single-bit split at its first variable. -/
theorem allEq3_no_split_a :
    ¬ ∃ op g : Bool → Bool → Bool, ∀ a b c, allEq3 a b c = op a (g b c) := by decide

/-- AllEqual₃ has no single-bit split at its second variable. -/
theorem allEq3_no_split_b :
    ¬ ∃ op g : Bool → Bool → Bool, ∀ a b c, allEq3 a b c = op b (g a c) := by decide

/-- AllEqual₃ has no single-bit split at its third variable. -/
theorem allEq3_no_split_c :
    ¬ ∃ op g : Bool → Bool → Bool, ∀ a b c, allEq3 a b c = op c (g a b) := by decide

end PallLean.Paper93.DeepMath.PathB.SATSlackSeed

#print axioms PallLean.Paper93.DeepMath.PathB.SATSlackSeed.SAT_embeds_allEq3
#print axioms PallLean.Paper93.DeepMath.PathB.SATSlackSeed.allEq3_no_split_a
