import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityHeadline

/-!
# N-Frame: the standard codebook — explicit enumeration

Work package 2 (… → parity headline → **standard codebook**).  The explicit singleton-core
codebook of `sat3X⊕`: index `0` is the tautology, index `1 + 2j + b` is the singleton literal
`(e_j, b)`.  The enumeration lemmas discharge the layout hypotheses of the headline chain
(`hcodeTaut`, `hcodeStar`-shaped facts, index disjointness and injectivity).

  `stdL` / `tautIdxStd` / `sIdx` / `stdCode` — the layout.
  `stdCode_taut` / `stdCode_sIdx` — **PROVED**: the enumeration reads.
  `sIdx_ne_taut` / `sIdx_inj` — **PROVED**: the index discipline.

## Honest scope

The singleton core only — the expander-edge indices extend `stdL` when the expander lands
(work package 1); the per-target assignments (`KF`, `pinIdxF`, scaffold sets) are the
counting round's Lean instantiation, built on these reads.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode

open PallLean.Paper93.DeepMath.PathB.NFrameParityEval
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook

/-- The standard codebook length: one tautology index plus two value-indices per
coordinate. -/
def stdL (v : ℕ) : ℕ := 2 * v + 1

/-- The tautology index. -/
def tautIdxStd (v : ℕ) : Fin (stdL v) := ⟨0, by unfold stdL; omega⟩

theorem sIdx_lt (v : ℕ) (j : Fin v) (b : ZMod 2) :
    1 + 2 * j.val + b.val < stdL v := by
  have hj := j.isLt
  have hb : b.val < 2 := ZMod.val_lt b
  unfold stdL
  omega

/-- The index of the singleton literal `(e_j, b)`. -/
def sIdx (v : ℕ) (j : Fin v) (b : ZMod 2) : Fin (stdL v) :=
  ⟨1 + 2 * j.val + b.val, sIdx_lt v j b⟩

theorem stdCode_div_lt (v : ℕ) (hv : 0 < v) (i : Fin (stdL v)) :
    (i.val - 1) / 2 < v := by
  have hi := i.isLt
  unfold stdL at hi
  omega

/-- The standard codebook. -/
def stdCode (v : ℕ) (hv : 0 < v) : Fin (stdL v) → Lit v := fun i =>
  if _h : i.val = 0 then tautLit v
  else (single v ⟨(i.val - 1) / 2, stdCode_div_lt v hv i⟩,
    (((i.val - 1) % 2 : ℕ) : ZMod 2))

/-- **The tautology read (proved)**. -/
theorem stdCode_taut (v : ℕ) (hv : 0 < v) :
    stdCode v hv (tautIdxStd v) = tautLit v := by
  unfold stdCode tautIdxStd
  rw [dif_pos rfl]

/-- **The singleton read (proved)**: index `1 + 2j + b` codes `(e_j, b)`. -/
theorem stdCode_sIdx (v : ℕ) (hv : 0 < v) (j : Fin v) (b : ZMod 2) :
    stdCode v hv (sIdx v j b) = (single v j, b) := by
  have hbv : b.val < 2 := ZMod.val_lt b
  unfold stdCode sIdx
  rw [dif_neg (by omega : ¬(1 + 2 * j.val + b.val = 0))]
  have h1 : (1 + 2 * j.val + b.val - 1) / 2 = j.val := by omega
  have h2 : (1 + 2 * j.val + b.val - 1) % 2 = b.val := by omega
  have hcast : ∀ x : ZMod 2, ((x.val : ℕ) : ZMod 2) = x := by decide
  congr 1
  · congr 1
    exact Fin.ext h1
  · rw [h2]
    exact hcast b

/-- **The index discipline (proved)**: singleton indices avoid the tautology index. -/
theorem sIdx_ne_taut (v : ℕ) (j : Fin v) (b : ZMod 2) :
    sIdx v j b ≠ tautIdxStd v := by
  intro h
  have h' : 1 + 2 * j.val + b.val = 0 := congrArg Fin.val h
  omega

/-- **The index injectivity (proved)**. -/
theorem sIdx_inj (v : ℕ) {j j' : Fin v} {b b' : ZMod 2}
    (h : sIdx v j b = sIdx v j' b') : j = j' ∧ b = b' := by
  have hval : 1 + 2 * j.val + b.val = 1 + 2 * j'.val + b'.val :=
    congrArg Fin.val h
  have hb : b.val < 2 := ZMod.val_lt b
  have hb' : b'.val < 2 := ZMod.val_lt b'
  have hj : j.val = j'.val := by omega
  have hbv : b.val = b'.val := by omega
  have hcast : ∀ x y : ZMod 2, x.val = y.val → x = y := by decide
  exact ⟨Fin.ext hj, hcast b b' hbv⟩

end PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode.stdCode_taut
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode.stdCode_sIdx
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode.sIdx_ne_taut
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode.sIdx_inj
