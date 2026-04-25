import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.PrincipalMinorAtUniv
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetMinorEmpty
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial

/-!
# Non-trivial gauge witness for `satFamily 3` at `n = 3`

This kernel-only file constructs a *non-identity* positive-definite gauge
witness for the SAT family `satFamily 3 = {∅, Finset.univ}` at `n = 3`.

The construction uses the Path B `compiledGadget α 3 = α • I + L_{K_3}`,
whose closed-form determinant is

```
  (compiledGadget α 3).det = α * (α + 3)^2.
```

To certify `det = 1` we must exhibit a positive real root of the cubic
`α (α + 3)^2 = 1`. We supply such a root via the **intermediate value
theorem** (inline, so we do not depend on a separate
`N3IVTExistence.lean`): the polynomial `f(α) = α (α + 3)^2` is continuous
on `[0, 1]`, satisfies `f(0) = 0 < 1 < 16 = f(1)`, hence attains the
value `1` at some `α ∈ (0, 1)`.

For that `α`:
* `compiledGadget α 3` is `PosDef` (by `compiledGadget_posDef`, since
  `α > 0` and `1 ≤ 3`),
* its determinant is `1` (by `compiledGadget_3x3_det`),
* it is *not* the identity matrix (by `compiledGadget_ne_identity`,
  since `2 ≤ 3`; the off-diagonal `(0, 1)` entry is `-1`, not `0`).

The final theorem packages these three facts as the existence of a
non-identity PosDef matrix on `Fin 3` of determinant `1`, which is the
non-trivial gauge witness requested at the truncated `n = 3` level.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open Set

/-- **Inline IVT existence: positive root of `α (α + 3)^2 = 1` in `(0, 1)`.**

The polynomial `f(α) = α * (α + 3)^2` is continuous on `ℝ`, satisfies
`f(0) = 0` and `f(1) = 1 * 16 = 16 > 1`, hence by the intermediate
value theorem on `Icc 0 1` it attains the value `1` at some
`α ∈ Ioo 0 1`. -/
private theorem exists_alpha_n3_det_one_local :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 3)^2 = 1 := by
  -- Define the cubic in question.
  let f : ℝ → ℝ := fun x => x * (x + 3)^2
  -- Continuity of `f` on `Icc (0:ℝ) 1`.
  have hf_cont : ContinuousOn f (Icc (0:ℝ) 1) := by
    have hcont : Continuous f :=
      (continuous_id).mul ((continuous_id.add continuous_const).pow 2)
    exact hcont.continuousOn
  -- Endpoint values.
  have hf0 : f 0 = 0 := by
    show (0 : ℝ) * (0 + 3)^2 = 0
    ring
  have hf1 : f 1 = 16 := by
    show (1 : ℝ) * (1 + 3)^2 = 16
    ring
  -- We have `1 ∈ Ioo (f 0) (f 1) = Ioo 0 16`.
  have h1_in : (1 : ℝ) ∈ Ioo (f 0) (f 1) := by
    rw [hf0, hf1]
    refine ⟨?_, ?_⟩
    · norm_num
    · norm_num
  -- IVT on `Ioo`: `Ioo (f 0) (f 1) ⊆ f '' Ioo 0 1`.
  have hIVT : Ioo (f 0) (f 1) ⊆ f '' Ioo (0:ℝ) 1 :=
    intermediate_value_Ioo (by norm_num : (0:ℝ) ≤ 1) hf_cont
  -- Extract a witness.
  obtain ⟨α, hα_mem, hα_eq⟩ := hIVT h1_in
  refine ⟨α, hα_mem.1, hα_mem.2, ?_⟩
  -- `hα_eq : f α = 1`, which unfolds to `α * (α + 3)^2 = 1`.
  show α * (α + 3)^2 = 1
  exact hα_eq

/-- For `n = 3` there exists `α > 0` with `(compiledGadget α 3).det = 1`.

By the inline IVT existence lemma `exists_alpha_n3_det_one_local`, there
is some `α ∈ (0, 1)` with `α (α + 3)^2 = 1`. The closed-form
`compiledGadget_3x3_det` then gives `(compiledGadget α 3).det = 1`. -/
theorem exists_alpha_compiledGadget_3x3_det_one :
    ∃ α : ℝ, 0 < α ∧ (compiledGadget α 3).det = 1 := by
  obtain ⟨α, hα_pos, _, hα_eq⟩ := exists_alpha_n3_det_one_local
  refine ⟨α, hα_pos, ?_⟩
  rw [compiledGadget_3x3_det]
  exact hα_eq

/-- For `n = 3`, there exists `α > 0` such that `compiledGadget α 3` is
`PosDef` *and* has `det = 1`.

Combines `exists_alpha_compiledGadget_3x3_det_one` with
`compiledGadget_posDef`, applied at `n = 3` (so `1 ≤ 3` is immediate). -/
theorem exists_compiledGadget_3x3_posDef_det_one :
    ∃ α : ℝ, 0 < α ∧ (compiledGadget α 3).PosDef ∧ (compiledGadget α 3).det = 1 := by
  obtain ⟨α, hα_pos, hα_det⟩ := exists_alpha_compiledGadget_3x3_det_one
  refine ⟨α, hα_pos, ?_, hα_det⟩
  exact compiledGadget_posDef α 3 hα_pos (by norm_num : 1 ≤ 3)

/-- **Existence of a NON-IDENTITY `PosDef` matrix with `det = 1` at `n = 3`.**

For some `α > 0` (a positive real root of the cubic `α (α + 3)^2 = 1`),
the compiled gadget `compiledGadget α 3` is simultaneously:

* positive definite (`compiledGadget_posDef`),
* of determinant `1` (`compiledGadget_3x3_det` together with the IVT
  witness),
* *not* equal to the identity matrix (`compiledGadget_ne_identity`,
  since `2 ≤ 3` — the `(0, 1)` off-diagonal entry equals `-1`).

This packages the three ingredients into the non-trivial gauge witness
for `satFamily 3` at `n = 3` requested by the user. -/
theorem exists_nonidentity_posDef_det_one_n3 :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
      A.PosDef ∧ A.det = 1 ∧ A ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨α, _hα_pos, hα_pd, hα_det⟩ := exists_compiledGadget_3x3_posDef_det_one
  refine ⟨compiledGadget α 3, hα_pd, hα_det, ?_⟩
  exact compiledGadget_ne_identity α 3 (by norm_num : 2 ≤ 3)

/-- **Existence of a non-trivial gauge witness for `satFamily 3`.**

Using the non-identity PosDef matrix with `det = 1` from
`exists_nonidentity_posDef_det_one_n3`, we obtain a gauge witness for
`satFamily 3 = {∅, Finset.univ}`:

* the principal minor at `∅` is the empty determinant `1` (vacuously),
* the principal minor at `Finset.univ` is `det A = 1` (by hypothesis),
* `A` is `PosDef` (by hypothesis),
* `A ≠ 1` (by hypothesis).

The principal-minor obligations are discharged via
`Matrix.det_isEmpty` for the empty subset and
`principalMinor_at_univ` for the full subset. -/
theorem exists_nontrivial_gauge_satFamily_n3 :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
      IsAmplituhedronGauge A (satFamily 3) ∧
      A ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  obtain ⟨A, hA_pd, hA_det, hA_ne⟩ := exists_nonidentity_posDef_det_one_n3
  refine ⟨A, ⟨hA_pd, ?_⟩, hA_ne⟩
  intros J hJ e
  -- `J ∈ satFamily 3` means `J = ∅ ∨ J = Finset.univ`.
  rw [satFamily_subset_iff] at hJ
  rcases hJ with h_empty | h_univ
  · -- Empty case: the submatrix is `0 × 0`, determinant is `1`.
    subst h_empty
    -- The index type `Fin (∅ : Finset (Fin 3)).card = Fin 0` is empty.
    have h_card : (∅ : Finset (Fin 3)).card = 0 := Finset.card_empty
    -- Use `Matrix.det_isEmpty` since `Fin 0` is empty.
    haveI : IsEmpty (Fin (∅ : Finset (Fin 3)).card) := by
      rw [h_card]; exact Fin.isEmpty'
    exact Matrix.det_isEmpty
  · -- Full case: the principal minor at `univ` equals `det A = 1`.
    subst h_univ
    -- The submatrix indexed by `Fin (univ.card)` along `e` is, up to a
    -- relabelling equivalence, equal to `A` itself, hence has determinant `det A`.
    -- We use `Matrix.det_submatrix_equiv_self` after composing the equivalence
    -- `e : Fin (univ.card) ≃ {i // i ∈ univ}` with the canonical
    -- `subtypeUnivEquiv : {i // i ∈ univ} ≃ Fin 3`.
    let φ : Fin (Finset.univ : Finset (Fin 3)).card ≃ Fin 3 :=
      e.trans (Equiv.subtypeUnivEquiv (fun i : Fin 3 => Finset.mem_univ i))
    -- The submatrix `A.submatrix (fun i => (e i).1) (fun i => (e i).1)`
    -- equals `A.submatrix φ φ` because `(e i).1 = φ i` by definition.
    have h_eq :
        A.submatrix (fun i => (e i).1) (fun i => (e i).1)
          = A.submatrix φ φ := by
      apply Matrix.ext
      intros i j
      rfl
    rw [h_eq, Matrix.det_submatrix_equiv_self φ A, hA_det]

end PallLean.Paper93.DeepMath.PathB.Positroid
