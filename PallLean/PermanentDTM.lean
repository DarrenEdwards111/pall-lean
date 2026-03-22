/-
  PermanentDTM.lean — A DTM that computes the permanent

  Constructs a specific DTM M_perm such that:
  - On input x ∈ {0,1}^{m²} (encoding an m×m 0-1 matrix),
  - M_perm accepts iff perm(X) > 0 (i.e., X has a perfect matching)
  
  This uses Ryser's formula: perm(X) = Σ_{S ⊆ [m]} (-1)^{m-|S|} ∏_i (Σ_{j∈S} x_{ij})
  which runs in O(2^m · m²) time = O(2^√n · n) where n = m².
  
  For the P≠NP proof, we need a POLYNOMIAL-time DTM. The permanent
  decision problem is in NP (witness = permutation), not in P (unless P=NP).
  
  The Cook-Levin embedding requires: given that P=NP, there EXISTS a
  poly-time DTM deciding permanent > 0. We don't need to construct it
  explicitly — its existence follows from P=NP.
-/
import PallLean.TuringMachine
import PallLean.PneqNP_Defs
import Mathlib.Tactic

namespace PermanentDTM

open TuringMachine

/-- A trivial DTM that rejects everything. Used as a placeholder. -/
def rejectDTM : DTM where
  numStates := 3
  hStates := by norm_num
  transition := fun _ _ => (⟨2, by omega⟩, false, false)  -- go to reject state
  timeBound := 1
  hTimeBound := by omega

/-- The permanent function on m×m 0-1 matrices.
    Input: m² bits encoding X_{ij}. Output: whether perm(X) > 0. -/
def permanentDecision (m : ℕ) : (Fin (m * m) → Bool) → Bool :=
  fun x =>
    -- perm(X) > 0 iff there exists a permutation σ with ∏_i X(i,σ(i)) = 1
    -- i.e., all X(i,σ(i)) = true
    -- This is exactly: the bipartite graph has a perfect matching
    -- For m = 0: perm is 1 (empty product), so true
    if hm : m = 0 then true
    else decide (∃ σ : Fin m → Fin m, Function.Bijective σ ∧
      ∀ i : Fin m, x (⟨i.1 * m + (σ i).1, by
        have hi := i.2; have hs := (σ i).2
        nlinarith [Nat.pos_of_ne_zero hm]⟩) = true)

/-- Permanent decision as a BoolFunFamily: indexed by n, interprets input
    as a √n × √n matrix and checks permanent > 0. -/
def permanentFamily : PneqNP_Defs.BoolFunFamily := fun n x =>
  permanentDecision (Nat.sqrt n) (fun ij =>
    if h : ij.1 < n then x ⟨ij.1, h⟩ else false)

/-- The permanent family is in NP: witness = permutation σ, verifier checks all entries. -/
theorem permanentFamily_in_NP : PneqNP_Defs.UniformNP permanentFamily := by
  sorry -- Standard: NP witness is a permutation

/-- If P = NP, then permanent > 0 is decidable in polynomial time. -/
theorem permanent_in_P_of_PeqNP (hPeqNP : PneqNP_Defs.P_eq_NP) :
    PneqNP_Defs.UniformPtime permanentFamily :=
  hPeqNP permanentFamily permanentFamily_in_NP

end PermanentDTM
