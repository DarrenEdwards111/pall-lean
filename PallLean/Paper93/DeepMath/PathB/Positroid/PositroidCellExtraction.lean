import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy

/-!
# Toy positroid cell extraction from a SAT-decider tableau

This file defines a **toy extraction** of a positroid cell from a
SAT-decider tableau (in the sense of `SATDeciderTableauToy.lean`). The
"extraction" is just the placeholder family `{∅, Finset.univ}` that is
attached to every tableau by `SATDeciderTableau.extractedFamily`, but
re-exposed at the top level under the name `extractPositroidCell` so it
can be referenced by the §7.1 amplituhedron-gauge construction.

This file is **kernel-only**: no `sorry`, no custom `axiom`, only the
kernel axioms `propext`, `Classical.choice`, `Quot.sound`.

## Note on `TNNStratumDef`

The companion file `TNNStratumDef.lean` is in flight. We do not depend
on it here: the extraction we expose is purely at the level of the
combinatorial index family `Finset (Finset (Fin n))` — i.e. the
positroid *cell* combinatorial data — which is what the gauge family
construction consumes.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The "extracted positroid cell" from a SAT decider tableau: a placeholder map
    that just returns the identity-based amplituhedron gauge family. -/
def extractPositroidCell {m n : ℕ} (T : SATDeciderTableau m n) :
    Finset (Finset (Fin n)) :=
  T.extractedFamily

/-- The extracted positroid cell from the all-ones tableau is `{∅, univ}`. -/
theorem extractPositroidCell_allOnes (m n : ℕ) :
    extractPositroidCell (SATDeciderTableau.allOnes m n) = {∅, Finset.univ} := rfl

/-- The extracted positroid cell from the zero tableau is `{∅, univ}`. -/
theorem extractPositroidCell_zero (m n : ℕ) :
    extractPositroidCell (SATDeciderTableau.zero m n) = {∅, Finset.univ} := rfl

/-- For any tableau, the extracted cell is non-empty. -/
theorem extractPositroidCell_nonempty {m n : ℕ} (T : SATDeciderTableau m n) :
    (extractPositroidCell T).Nonempty := by
  refine ⟨∅, ?_⟩
  unfold extractPositroidCell
  exact T.extractedFamily_mem_empty

/-- For any tableau, ∅ is in the extracted cell. -/
theorem extractPositroidCell_mem_empty {m n : ℕ} (T : SATDeciderTableau m n) :
    ∅ ∈ extractPositroidCell T :=
  T.extractedFamily_mem_empty

/-- For any tableau, univ is in the extracted cell. -/
theorem extractPositroidCell_mem_univ {m n : ℕ} (T : SATDeciderTableau m n) :
    (Finset.univ : Finset (Fin n)) ∈ extractPositroidCell T :=
  T.extractedFamily_mem_univ

end PallLean.Paper93.DeepMath.PathB.Positroid
