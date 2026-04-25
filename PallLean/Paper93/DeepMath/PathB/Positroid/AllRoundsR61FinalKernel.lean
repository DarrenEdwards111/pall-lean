import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerRelation2x4
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Identity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Path B + Positroid kernel-only progress, rounds 51–61 final bundle

This file bundles twelve concrete kernel-only facts spanning Path B
Positroid work across rounds 51–61 into a single substantive
conjunction `all_rounds_r61_final_kernel`.

Compared to `AllRoundsR60FinalKernel`, this round-61 bundle adds two
additional clauses:

11. **Round 61, n = 4:** there exists a `4 × 4` real matrix that is
    positive definite and not the identity (witness:
    `compiledGadget 1 4`).

12. **Round 61, n = 5:** there exists a `5 × 5` real matrix that is
    positive definite and not the identity (witness:
    `compiledGadget 1 5`).

Both new clauses follow from the closed-form `compiledGadget`
positive-definiteness lemma and the non-identity lemma at `n ≥ 2`.

The bundle records, for the §7.1 amplituhedron-gauge discharge program:

1. The identity matrix is **principal-TNN** at every dimension `n`.

2. The identity matrix is an **amplituhedron gauge** for *any* index
   family `𝒥` at any dimension.

3. The fundamental **Plücker relation** for 2×4 matrices holds as a
   polynomial identity in eight real entries.

4. **Round 59 generalisation:** for every `α : ℝ` and every `n ≥ 2`,
   `compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)`.

5. **Round 59 generalisation:** for every `α > 0` and every `n ≥ 1`,
   `compiledGadget α n` is positive definite.

6. **n = 1 collapse:** `compiledGadget 1 1` equals the identity matrix
   on `Fin 1`, and is therefore an amplituhedron gauge for
   `satFamily 1`.

7. **n = 2 non-triviality:** `compiledGadget (√2 − 1) 2` from §28.3
   gauges `satFamily 2` and is genuinely *not* the identity matrix.

8. For any SAT-decider tableau, the **extracted family** contains both
   `∅` and `Finset.univ` (the two extremal positroid index sets).

9. For every `n = 2` SAT-decider tableau there exists a non-trivial
   gauge witness (the §28.3 compiledGadget at `α = √2 − 1` gauges
   `satFamily 2` and is not the identity).

10. **Round 60 existence:** for every dimension `n`, there exists a
    matrix `A` that is an amplituhedron gauge for `satFamily n`.

11. **Round 61, n = 4:** existence of a positive-definite, non-identity
    `4 × 4` real matrix.

12. **Round 61, n = 5:** existence of a positive-definite, non-identity
    `5 × 5` real matrix.

None of the twelve clauses depends on the upstream
`exists_amplituhedron_gauge_for_sat_decider` axiom: each is discharged
purely from closed-form `compiledGadget` data, the `satFamily`
definition, the Path B positive-definiteness construction, the
`identity_isAmplituhedronGauge_any` existential witness, and the
polynomial identity from `ring`. The file is kernel-only: no `sorry`,
no custom `axiom`, only the kernel axioms `propext`, `Classical.choice`,
`Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **All Path B Positroid kernel-only progress, rounds 51–61.**

    A 12-fold conjunction. None depend on the upstream
    `exists_amplituhedron_gauge_for_sat_decider` axiom. -/
theorem all_rounds_r61_final_kernel :
    -- (1) Identity is principal-TNN
    (∀ n : ℕ, IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    -- (2) Identity gauges any family
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    -- (3) Plücker relation 2×4
    (∀ a b c d e f g h : ℝ,
       (a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f) + (a*h - d*e) * (b*g - c*f) = 0) ∧
    -- (4) For all α and n ≥ 2, compiledGadget α n ≠ identity
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    -- (5) For all α > 0 and n ≥ 1, compiledGadget α n is PosDef
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    -- (6) n=1 collapse
    (compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
     IsAmplituhedronGauge (compiledGadget 1 1) (satFamily 1)) ∧
    -- (7) n=2 NON-TRIVIAL gauge witness from §28.3
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (8) Tableau extracted family extremality
    (∀ (m n : ℕ) (T : SATDeciderTableau m n),
       ∅ ∈ T.extractedFamily ∧ (Finset.univ : Finset (Fin n)) ∈ T.extractedFamily) ∧
    -- (9) For every n=2 tableau, a NON-TRIVIAL gauge witness exists
    (∀ (m : ℕ) (T : SATDeciderTableau m 2),
       ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
         IsAmplituhedronGauge A (satFamily 2) ∧
         A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- (10) Existence at every n
    (∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n)) ∧
    -- (11) Round 61: n = 4 PosDef non-identity existence
    (∃ A : Matrix (Fin 4) (Fin 4) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    -- (12) Round 61: n = 5 PosDef non-identity existence
    (∃ A : Matrix (Fin 5) (Fin 5) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact identity_isPrincipalTNN
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · exact plucker_relation_2x4
  · intros α n hn; exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · exact ⟨compiledGadget_one_one_is_identity, compiledGadget_one_one_isGauge_satFamily⟩
  · exact ⟨compiledGadget_n2_isGauge_satFamily, compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · exact fun m n T => ⟨T.extractedFamily_mem_empty, T.extractedFamily_mem_univ⟩
  · exact fun m _T =>
      ⟨compiledGadget (Real.sqrt 2 - 1) 2,
       compiledGadget_n2_isGauge_satFamily,
       compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · exact fun n => ⟨1, identity_isAmplituhedronGauge_any (satFamily n)⟩
  · refine ⟨compiledGadget 1 4, ?_, ?_⟩
    · exact compiledGadget_posDef 1 4 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 4 (by norm_num)
  · refine ⟨compiledGadget 1 5, ?_, ?_⟩
    · exact compiledGadget_posDef 1 5 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 5 (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid
