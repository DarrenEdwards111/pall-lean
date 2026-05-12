import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugePosDef
import PallLean.Paper93.DeepMath.PathB.Positroid.ContentGaugeNotIdentityN2
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

/-!
# Non-triviality of the content-driven gauge at `n = 3`

This file packages the two structural facts about the **content-driven
gauge** `contentDrivenGauge T` for an `n = 3` SAT decider tableau:

* It is **positive definite** (`contentDrivenGauge_n3_posDef`), and
* It is **not the identity** matrix on `Fin 3`
  (`contentDrivenGauge_n3_ne_identity`).

Together these say that for every tableau `T : SATDeciderTableau m 3`,
the matrix `contentDrivenGauge T` is a genuinely **non-trivial** PosDef
witness: it lies in the (open) cone of positive definite matrices yet
is distinct from the identity, regardless of the tableau's content.

We additionally:

* Restate this as an existence statement
  (`exists_content_driven_nontrivial_n3`), and
* Combine it with the analogous `n = 2` statement
  (`contentDrivenGauge_n2_posDef`, `contentDrivenGauge_n2_ne_identity`)
  into a single packaged theorem
  (`content_driven_nontrivial_n2_and_n3`).

The proofs reduce directly to the lemmas already proven in
`ContentGaugePosDef.lean` and `ContentGaugeNotIdentityN2.lean`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- For any n=3 SAT tableau, the content-driven gauge is PosDef and not identity. -/
theorem contentDrivenGauge_n3_nontrivial {m : ℕ} (T : SATDeciderTableau m 3) :
    (contentDrivenGauge T).PosDef ∧
    contentDrivenGauge T ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
  ⟨contentDrivenGauge_n3_posDef T, contentDrivenGauge_n3_ne_identity T⟩

/-- For any n=3 SAT tableau, ∃ non-identity PosDef matrix from content. -/
theorem exists_content_driven_nontrivial_n3 :
    ∀ (m : ℕ) (T : SATDeciderTableau m 3),
      ∃ A : Matrix (Fin 3) (Fin 3) ℝ,
        A.PosDef ∧
        A ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) ∧
        A = contentDrivenGauge T := by
  intros m T
  refine ⟨contentDrivenGauge T, ?_, ?_, rfl⟩
  · exact contentDrivenGauge_n3_posDef T
  · exact contentDrivenGauge_n3_ne_identity T

/-- Combined statement: at n=2 AND n=3, there exist non-trivial content-driven gauges. -/
theorem content_driven_nontrivial_n2_and_n3 :
    (∀ (m : ℕ) (T : SATDeciderTableau m 2),
      (contentDrivenGauge T).PosDef ∧
      contentDrivenGauge T ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ (m : ℕ) (T : SATDeciderTableau m 3),
      (contentDrivenGauge T).PosDef ∧
      contentDrivenGauge T ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  refine ⟨?_, ?_⟩
  · intros m T
    refine ⟨contentDrivenGauge_n2_posDef T, contentDrivenGauge_n2_ne_identity T⟩
  · intros m T
    refine ⟨contentDrivenGauge_n3_posDef T, contentDrivenGauge_n3_ne_identity T⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
