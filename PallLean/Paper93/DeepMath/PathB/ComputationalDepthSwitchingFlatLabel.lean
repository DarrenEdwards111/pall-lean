import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLabel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFlatten

/-!
# Packing the flat label into `PathLabel w s`

**STATUS: REAL.  THE LAST TYPE-LEVEL COERCION FOR THE `(2w)^s` LABEL.**

The flat `(index, isLast)` sequence (from `ungroupBlocks`) is a `List (ℕ × Bool)`; the count
scaffold wants the finite type `PathLabel w s = Fin s → (Fin w × Bool)` (cardinality
`(2w)^s`).  This file packs a length-`s`, indices-`< w` flat sequence into `PathLabel w s`
**injectively**, completing the type-level join.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

variable {w s : ℕ}

/-- Pack a flat `(Fin w × Bool)` sequence into `PathLabel w s` by indexing (default outside
range). -/
def flatToLabel [NeZero w] (l : List (Fin w × Bool)) : PathLabel w s :=
  fun i => (l[i.val]?).getD default

/-- On length-`s` sequences, the packing is injective. -/
theorem flatToLabel_inj [NeZero w] {l l' : List (Fin w × Bool)}
    (hl : l.length = s) (hl' : l'.length = s) (h : (flatToLabel l : PathLabel w s) = flatToLabel l') :
    l = l' := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < s
  · have hfun := congrFun h ⟨i, hi⟩
    simp only [flatToLabel] at hfun
    rw [List.getElem?_eq_getElem (show i < l.length by omega),
        List.getElem?_eq_getElem (show i < l'.length by omega)] at hfun ⊢
    simp only [Option.getD_some] at hfun
    rw [hfun]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.flatToLabel_inj
