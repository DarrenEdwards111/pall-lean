import PallLean.Paper93.CompiledCoefficientBasis
import PallLean.Paper93.TensorDimBound
import PallLean.WithinProfileBound

/-!
# Paper §9 Lemma 31 — compiled-basis profile-subspace dimension bound

This file produces the **dimension-bound half** of Paper §9 Lemma 31 in
its `profileTemplateBound` / `withinProfileBound` form.

Paper Lemma 31 has two halves:

* **(Property 2 — dimension bound, this file.)** For each
  interface-anonymous profile `h`, the profile subspace
  `V_h = ⊗_σ Sym^{h(σ)}(W_σ)` (encoded in Lean as
  `profileSubspace h (fun σ => W_σ)`) has dimension at most
  `∏_σ C(h(σ) + 2, 2)`, which is `profileTemplateBound h`, and which is
  in turn dominated by the global `withinProfileBound κ` on admissible
  profiles.

* **(Property 1 — structural decomposition, NOT in this file.)** Every
  SPDP row corresponding to a mixed partial `∂^τ p` with local-type
  statistics matching `h` lies in `V_h`. The paper handles this in one
  sentence ("by construction"); in the Lean codebase it is the
  unresolved math content of the bounded-Leibniz / per-interface
  contribution machinery and is the subject of Codex's ongoing
  `…ProfileTemplateTermFamilyData` / `…SourceLeibnizLocalTypeCompressionData`
  attacks.

The bound here is mechanically composed from:

* `profileSubspace_finrank_bound` (`Paper93/TensorDimBound.lean:309`)
  — the per-profile dimension bound for an arbitrary family `W` of
  per-interface subspaces with `dim W_σ ≤ 3`.
* `interfaceSpace_compiledBasis_finrank_le_three`
  (`Paper93/CompiledCoefficientBasis.lean:264`) — instantiation of
  Lemma 31's `dim W_σ ≤ d₀ = 3` for the canonical compiled-basis
  interface space.
* `profileTemplateBound_le_withinProfileBound`
  (`WithinProfileBound.lean:1324`) — arithmetic dominance of the
  per-profile template count by the global `(κ+1)^8` budget on
  admissible profiles.

No new axiom is introduced; the `#print axioms` outputs at the bottom
must show only `[propext, Classical.choice, Quot.sound]`.
-/

namespace PallLean.Paper93

open MvPolynomial SPDP SymmetricPowerBound WithinProfileBound

/-- **Paper §9 Lemma 31 (compiled-basis profile-subspace dimension bound,
explicit template form).**

For any block partition `B`, parameters `κ ℓ`, and profile histogram `h`,
the profile subspace built from the canonical compiled-basis interface
spaces has finrank bounded by the explicit per-profile template count
`profileTemplateBound h = ∏_σ C(h(σ) + 2, 2)`.

This is the dimension-bound half of Lemma 31 in the codebase's
`profileTemplateBound` idiom. The structural-decomposition half
(showing concrete SPDP rows of profile `h` lie in this subspace) is
supplied separately by the per-interface-contribution machinery in the
Route-B / PathB closure chain. -/
theorem profileSubspace_compiledBasis_finrank_le_profileTemplateBound
    {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ) (h : ProfileHistogram) :
    Module.finrank ℚ
        (profileSubspace h
          (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)) ≤
      profileTemplateBound h := by
  classical
  unfold profileTemplateBound
  exact profileSubspace_finrank_bound h
    (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)
    (fun σ : ConstraintType => interfaceSpace_compiledBasis_finite B κ ℓ σ)
    (fun σ : ConstraintType => interfaceSpace_compiledBasis_finrank_le_three B κ ℓ σ)

/-- **Paper §9 Lemma 31 (compiled-basis profile-subspace dimension bound,
global form).**

Strengthened admissibility form: when `h` is admissible at parameter `κ`
(i.e. `profileMass h ≤ κ`), the compiled-basis profile subspace has
finrank dominated by the global `withinProfileBound κ = (κ+1)^8`.

This is the dimension input expected by the downstream Width⇒Rank
chain: once an SPDP row is shown to lie in the profile subspace, its
contribution to the SPDP rank at parameters `(κ, ℓ)` is bounded by
`withinProfileBound κ`, which is polylogarithmic in `n` when
`κ = Θ(log n)`. -/
theorem profileSubspace_compiledBasis_finrank_le_withinProfileBound
    {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ)
    (h : ProfileHistogram) (hadm : ProfileAdmissible κ h) :
    Module.finrank ℚ
        (profileSubspace h
          (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)) ≤
      withinProfileBound κ :=
  (profileSubspace_compiledBasis_finrank_le_profileTemplateBound B κ ℓ h).trans
    (profileTemplateBound_le_withinProfileBound κ h hadm)

/-! ### Axiom audit

Both theorems above should depend only on the kernel-only profile
`[propext, Classical.choice, Quot.sound]`. The `#print axioms`
directives below make this auditable. -/

#print axioms profileSubspace_compiledBasis_finrank_le_profileTemplateBound
#print axioms profileSubspace_compiledBasis_finrank_le_withinProfileBound

end PallLean.Paper93
