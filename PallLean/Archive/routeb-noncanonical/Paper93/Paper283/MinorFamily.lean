import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

namespace PallLean.Paper93.Paper283

/-- The family J of principal-minor index sets.
    Paper §28.3 line 6876: "a fixed family J of principal minors (amplituhedron-type positivity)".
    For concreteness: all non-empty subsets of size ≤ 3. -/
def minorFamily (N : ℕ) : Finset (Finset (Fin N)) :=
  (Finset.univ.powerset).filter (fun J => 1 ≤ J.card ∧ J.card ≤ 3)

theorem minorFamily_nonempty {N : ℕ} (hN : 1 ≤ N) : (minorFamily N).Nonempty := by
  refine ⟨{⟨0, hN⟩}, ?_⟩
  unfold minorFamily
  simp [Finset.mem_filter, Finset.mem_powerset]

end PallLean.Paper93.Paper283
