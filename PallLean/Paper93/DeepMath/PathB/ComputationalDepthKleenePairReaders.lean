import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleenePairSub
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKleeneDispatch

/-!
# Kleene interpreter project — pair handler sub-result reader Codes (PROVED)

`eaCode`/`ebCode` build the `lookupSubCode` input for sub-`a`/`b` (extracting `a.enc`/`b.enc` from `ec` via
`fstSubCode`/`sndSubCode`) and read it.  On the pair bundle (with `ec = (pair a b).enc` and the correct
table) they return `spec` at the sub-config ranks.

* `eaCode`, `ebCode`, `eval_eaCode`, `eval_ebCode`.

Honest scope: the pair handler's sub-result readers.  The multiplicative assembly, the other handlers, the
body, the interpreter, and the runtime remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneUCode

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.KleeneList (encodeList)
open PallLean.Paper93.DeepMath.PathB.KleeneRank (cfgRank)

/-- Reader for sub-`a`: build `lookupSubCode` input with `a.enc = fstSubCode ec`. -/
def eaCode : Code :=
  Code.comp lookupSubCode (Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
    (Code.pair (Code.comp fstSubCode (Code.comp Code.left (Code.comp Code.right Code.right)))
      (Code.comp Code.right (Code.comp Code.right Code.right)))))

/-- Reader for sub-`b`. -/
def ebCode : Code :=
  Code.comp lookupSubCode (Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
    (Code.pair (Code.comp sndSubCode (Code.comp Code.left (Code.comp Code.right Code.right)))
      (Code.comp Code.right (Code.comp Code.right Code.right)))))

theorem eval_eaCode (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.pair a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.pair a b).enc n) :
    eaCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair (UCode.pair a b).enc n))) = Part.some (spec (cfgRank E B k a.enc n)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
    (Nat.pair k (Nat.pair (UCode.pair a b).enc n)) with hX
  have hbi : (Code.left : Code).eval X
      = Part.some (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hec2 : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X
      = Part.some (UCode.pair a b).enc := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hfst : (Code.comp fstSubCode (Code.comp Code.left (Code.comp Code.right Code.right))).eval X
      = Part.some a.enc := by rw [comp_eval _ _ _ _ hec2]; exact eval_fstSub_pair a b
  have hinput : (Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp fstSubCode (Code.comp Code.left (Code.comp Code.right Code.right)))
        (Code.comp Code.right (Code.comp Code.right Code.right))))).eval X
      = Part.some (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
          (Nat.pair k (Nat.pair a.enc n))) :=
    pair_eval _ _ _ _ _ hbi (pair_eval _ _ _ _ _ hk (pair_eval _ _ _ _ _ hfst hn2))
  rw [show eaCode.eval X = ((Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp fstSubCode (Code.comp Code.left (Code.comp Code.right Code.right)))
        (Code.comp Code.right (Code.comp Code.right Code.right))))).eval X).bind lookupSubCode.eval from rfl,
    hinput, Part.bind_some]
  exact pair_ea E B N k n a b spec hec hn hN

theorem eval_ebCode (E B N k n : ℕ) (a b : UCode) (spec : ℕ → ℕ)
    (hec : (UCode.pair a b).enc ≤ E) (hn : n ≤ B) (hN : N = cfgRank E B k (UCode.pair a b).enc n) :
    ebCode.eval (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
        (Nat.pair k (Nat.pair (UCode.pair a b).enc n))) = Part.some (spec (cfgRank E B k b.enc n)) := by
  set X := Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
    (Nat.pair k (Nat.pair (UCode.pair a b).enc n)) with hX
  have hbi : (Code.left : Code).eval X
      = Part.some (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N)))) := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hk : (Code.comp Code.left Code.right).eval X = Part.some k := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hn2 : (Code.comp Code.right (Code.comp Code.right Code.right)).eval X = Part.some n := by
    rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hec2 : (Code.comp Code.left (Code.comp Code.right Code.right)).eval X
      = Part.some (UCode.pair a b).enc := by rw [hX]; simp [Code.eval, Nat.unpair_pair]
  have hsnd : (Code.comp sndSubCode (Code.comp Code.left (Code.comp Code.right Code.right))).eval X
      = Part.some b.enc := by rw [comp_eval _ _ _ _ hec2]; exact eval_sndSub_pair a b
  have hinput : (Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp sndSubCode (Code.comp Code.left (Code.comp Code.right Code.right)))
        (Code.comp Code.right (Code.comp Code.right Code.right))))).eval X
      = Part.some (Nat.pair (Nat.pair (Nat.pair E B) (Nat.pair N (encodeList (tableList spec N))))
          (Nat.pair k (Nat.pair b.enc n))) :=
    pair_eval _ _ _ _ _ hbi (pair_eval _ _ _ _ _ hk (pair_eval _ _ _ _ _ hsnd hn2))
  rw [show ebCode.eval X = ((Code.pair Code.left (Code.pair (Code.comp Code.left Code.right)
      (Code.pair (Code.comp sndSubCode (Code.comp Code.left (Code.comp Code.right Code.right)))
        (Code.comp Code.right (Code.comp Code.right Code.right))))).eval X).bind lookupSubCode.eval from rfl,
    hinput, Part.bind_some]
  exact pair_eb E B N k n a b spec hec hn hN

end PallLean.Paper93.DeepMath.PathB.KleeneUCode

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_eaCode
#print axioms PallLean.Paper93.DeepMath.PathB.KleeneUCode.eval_ebCode
