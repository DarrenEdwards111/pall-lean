import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Reconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReadOnceId

/-!
# Reconstruction for read-once: the reduction, and an honest scope note

This file proves the clean **reduction** of `ReconstructionCorrect` to a *label-free* decoder, and
documents precisely what read-once does and does not give for the deepest-branch reconstruction.

* `reconstruction_of_labelfree` — if the deepest branch's selected set is recoverable from the
  *end-state alone* (a label-free decoder `D₀`), then `ReconstructionCorrect` holds (use a constant
  label and `D = fun π _ => D₀ π`).  This is exactly how the **falsify path** is reconstructed:
  `decodedSel_eq_replaySel` is such a `D₀` (queried variables carry false literals, read off the
  end-state, no label needed).

* `readonce_clause_of_litVar` — the read-once enabling fact: a literal's variable determines its
  clause.  So once a selected variable is known, *which* clause it came from is free under read-once.

## Why read-once does **not** make the deepest branch label-free

Under read-once the canonical decision tree factors over (variable-disjoint) clauses, and the
**deepest** branch *satisfies* its final clause — setting that clause's literals to `true`.  Those
`true`-set variables carry **no false literal**, so in the end-state they are indistinguishable from
variables `ρ` itself fixed: a label-free decoder cannot tell which of the satisfied clause's
true-variables are path-selected.  Hence the `(2w)^s` label is genuinely needed for the satisfied
clause, *even under read-once*, and `reconstruction_of_labelfree` does not by itself close the
deepest-branch case.

So the honest status: the reduction and the read-once clause-identification are proved; full
read-once `ReconstructionCorrect` additionally needs the label to encode the satisfied clause's
path-variables (and the monotone step-to-clause matching, `termFalsified_fixVar_of_free`).  That
encoding is **not** discharged here and **not** faked.  (Width-1 read-once — every clause a single
literal — is the sub-case where the deepest branch *is* the falsify path, so `decodedSel` +
`reconstruction_of_labelfree` close it with no label.)
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Reduction: a label-free decoder gives `ReconstructionCorrect`.**  If `D₀` recovers the deepest
selected set from the end-state alone, then the reconstruction invariant holds with a constant label.
(The falsify path supplies such a `D₀` via `decodedSel_eq_replaySel`.) -/
theorem reconstruction_of_labelfree {w s F : ℕ} [NeZero w] {cs : List (Clause n)}
    {Bad : Finset (Restriction n)} (D₀ : Restriction n → Finset (Fin n))
    (hD₀ : ∀ ρ ∈ Bad, D₀ (deepestEnd cs F ρ) = deepestSel cs F ρ) :
    ReconstructionCorrect cs w s F Bad :=
  ⟨fun _ _ => ((0 : Fin w), false), fun π _ => D₀ π, hD₀⟩

/-- **Read-once clause identification.**  A literal's variable determines its clause: under
read-once, two clauses sharing a variable are equal.  So once a selected variable is recovered, its
clause is free. -/
theorem readonce_clause_of_litVar {cs : List (Clause n)} (hro : ReadOnce cs)
    {C D : Clause n} {ℓ ℓ' : Rung4Literal n} (hC : C ∈ cs) (hD : D ∈ cs)
    (hℓC : ℓ ∈ C.lits) (hℓD : ℓ' ∈ D.lits) (hv : litVar ℓ = litVar ℓ') : C = D :=
  hro (litVar ℓ) C D hC hD ⟨ℓ, hℓC, rfl⟩ ⟨ℓ', hℓD, hv.symm⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_of_labelfree
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.readonce_clause_of_litVar
