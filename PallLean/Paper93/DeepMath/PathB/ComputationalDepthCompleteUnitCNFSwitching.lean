import PallLean.Paper93.DeepMath.PathB.ComputationalDepthXorCNFSwitchingCashout

/-!
# A constructive switching base case: complete unit CNF

This file constructs, rather than assumes, the switching certificate for the smallest named CNF class.  A complete
unit CNF contains one unit clause for every profile coordinate.  It accepts exactly one target profile, so no
restriction branching is needed: the whole formula is already a one-target XOR-DNF leaf.

This base case is deliberately narrow.  Its purpose is to connect actual CNF syntax and semantics to the numerical
certificate cash-out.  Extending the construction to non-unit bounded-width CNF is the remaining switching problem.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompleteUnitCNFSwitching

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.XorCNFIdentityEmbedding
open PallLean.Paper93.DeepMath.PathB.XorCNFSwitchingCashout

variable {n : ℕ}

/-- The CNF containing the required unit clause `xᵢ = targetᵢ` for every coordinate. -/
def completeUnitCNF (target : Fin n → Bool) : CNF n :=
  Finset.univ.image fun i => {(i, target i)}

/-- A complete unit CNF accepts exactly its designated target assignment. -/
theorem eval_completeUnitCNF_iff (x target : Fin n → Bool) :
    evalCNF x (completeUnitCNF target) ↔ x = target := by
  constructor
  · intro hx
    funext i
    have hclause : ({(i, target i)} : Finset (Literal n)) ∈ completeUnitCNF target := by
      simp [completeUnitCNF]
    obtain ⟨l, hl, heval⟩ := hx _ hclause
    have hli : l = (i, target i) := by simpa using hl
    subst l
    exact heval
  · intro hxt clause hclause
    subst x
    simp only [completeUnitCNF, Finset.mem_image] at hclause
    obtain ⟨i, -, rfl⟩ := hclause
    exact ⟨(i, target i), by simp, by simp [evalLiteral]⟩

/-- The explicit no-branch, one-target switching certificate for complete unit CNF. -/
def completeUnitCertificate (n : ℕ) (hn : 1 ≤ n) : SwitchingCertificate where
  n := n
  leafCount := 1
  targetsPerLeaf := 1
  saving := n
  npos := hn
  savingPos := hn
  savingLe := le_rfl
  leafBound := by simp
  targetBound := one_le_pow₀ (by norm_num)

/-- The constructed certificate already gives a strict sub-cube linear-test bound. -/
theorem completeUnitLinearTests_beats_bruteforce (n : ℕ) (hn : 1 ≤ n) :
    switchingLinearTests (completeUnitCertificate n hn) < 2 ^ n := by
  simpa [PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic.bruteForceTime] using
    switchingLinearTests_beats_bruteforce (completeUnitCertificate n hn)

end PallLean.Paper93.DeepMath.PathB.CompleteUnitCNFSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.CompleteUnitCNFSwitching.eval_completeUnitCNF_iff
#print axioms PallLean.Paper93.DeepMath.PathB.CompleteUnitCNFSwitching.completeUnitLinearTests_beats_bruteforce
