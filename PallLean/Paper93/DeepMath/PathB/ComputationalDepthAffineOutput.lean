import PallLean.Paper93.DeepMath.PathB.ComputationalDepthAffineSemantics

/-!
# Closing the teeth: an affine-mixed circuit computes an affine function

`AffineSemantics` proved the per-gate closure of the GF(2)-affine class.  This file threads that
closure through the straight-line evaluation `runFrom`: **every wire of an affine-mixed circuit is an
affine function of the inputs**, hence so is its output.  This closes the rigidity teeth fully — an
`AffineMixed` circuit is not merely syntactically affine, it *computes* a GF(2)-affine function.

* **`runFrom_length` (proved)** — a run appends exactly one wire per gate (so wire indices are
  input-independent).
* **`wireAffine_of_affineMixed` (proved)** — for an affine-mixed circuit, every wire
  `x ↦ (runFrom x [] c).getD j false` is affine (reverse induction on the gate list: an inherited
  wire is affine by IH; the newly appended wire is `evalGate` of earlier affine wires through an
  affine gate, hence affine by the `AffineSemantics` closure lemmas; out-of-range indices default to
  the constant `false`).
* **`output_affine` (proved)** — the circuit's output is affine.

**Honest scope.**  This makes the linear horn's regime exact: affine-mixed circuits compute affine
functions, so the horn is genuinely the GF(2)-linear / matrix-rigidity (Valiant) regime.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AffineOutput

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.CostSuperDichotomy
open PallLean.Paper93.DeepMath.PathB.AffineSemantics

variable {n : ℕ}

/-- A run appends exactly one wire per gate: `|runFrom x vals gs| = |vals| + |gs|`. -/
theorem runFrom_length (x : Fin n → Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool),
      (runFrom x vals gs).length = vals.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro vals; simp [runFrom]
  | cons g gs ih =>
    intro vals
    rw [runFrom, ih (vals ++ [evalGate x vals g]), List.length_append, List.length_singleton,
      List.length_cons]
    omega

/-- Every wire of `c`, as a function of the inputs, is a GF(2)-affine function. -/
def WireAffine (c : List (CGate n)) : Prop :=
  ∀ j, IsAffineFn (fun x => (runFrom x [] c).getD j false)

/-- **Every wire of an affine-mixed circuit is affine (proved).** -/
theorem wireAffine_of_affineMixed :
    ∀ (c : List (CGate n)), AffineMixed c → WireAffine c := by
  intro c
  induction c using List.reverseRecOn with
  | nil =>
    intro _ j
    have h0 : (fun x : Fin n → Bool => (runFrom x [] ([] : List (CGate n))).getD j false)
            = fun _ => false := by funext x; rfl
    rw [h0]; exact isAffineFn_const false
  | append_singleton c' g ih =>
    intro hc j
    have hc' : AffineMixed c' := fun gg hgg => hc gg (List.mem_append_left _ hgg)
    have hg : IsAffineGate g := hc g (by simp)
    have ihc' : WireAffine c' := ih hc'
    have hrun : ∀ x : Fin n → Bool,
        runFrom x [] (c' ++ [g]) = runFrom x [] c' ++ [evalGate x (runFrom x [] c') g] := by
      intro x; rw [runFrom_append]; simp [runFrom]
    have hlen : ∀ x : Fin n → Bool, (runFrom x [] c').length = c'.length := by
      intro x; rw [runFrom_length x c' []]; simp
    rcases lt_trichotomy j c'.length with hj | hj | hj
    · -- inherited wire
      have heq : (fun x => (runFrom x [] (c' ++ [g])).getD j false)
               = fun x => (runFrom x [] c').getD j false := by
        funext x
        rw [hrun x, List.getD_append _ _ _ _ (by rw [hlen x]; exact hj)]
      rw [heq]; exact ihc' j
    · -- the newly appended gate's output
      subst hj
      have heq : (fun x => (runFrom x [] (c' ++ [g])).getD c'.length false)
               = fun x => evalGate x (runFrom x [] c') g := by
        funext x
        rw [hrun x, ← hlen x, getD_concat]
      rw [heq]
      cases g with
      | var i => simp only [evalGate]; exact isAffineFn_proj i
      | cst b => simp only [evalGate]; exact isAffineFn_const b
      | un op k => simp only [evalGate]; exact isAffineFn_unary op (ihc' k)
      | bin op k l => simp only [evalGate]; exact isAffineFn_bin hg (ihc' k) (ihc' l)
    · -- past the end: default false
      have heq : (fun x => (runFrom x [] (c' ++ [g])).getD j false)
               = fun _ : Fin n → Bool => false := by
        funext x
        rw [hrun x]
        apply List.getD_eq_default
        rw [List.length_append, hlen x, List.length_singleton]
        omega
      rw [heq]; exact isAffineFn_const false

/-- **An affine-mixed circuit computes a GF(2)-affine function (proved).**  The output is the last
wire, which is affine by `wireAffine_of_affineMixed`. -/
theorem output_affine (c : List (CGate n)) (hc : AffineMixed c) : IsAffineFn (output c) :=
  wireAffine_of_affineMixed c hc (c.length - 1)

end PallLean.Paper93.DeepMath.PathB.AffineOutput

#print axioms PallLean.Paper93.DeepMath.PathB.AffineOutput.runFrom_length
#print axioms PallLean.Paper93.DeepMath.PathB.AffineOutput.wireAffine_of_affineMixed
#print axioms PallLean.Paper93.DeepMath.PathB.AffineOutput.output_affine
