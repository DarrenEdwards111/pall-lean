import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTreeToCNF

/-!
# Tight switching, step 53: clause-count bounds for the switched bottom gates (branch `razborov-recoverRho-wip`)

The size half of the width-aware invariant.  `dtreeToDNF_width` / `dtreeToCNF_width` (foundations 1/2) bound
each *term's width* by the tree depth; here we bound the *number of terms* by `2 ^ depth` (one accepting/
rejecting leaf per term, and a depth-`d` tree has `≤ 2^d` leaves).  Together they say: a depth-`d` decision
tree switches to a DNF (or CNF) of **width `≤ d` and clause-count `≤ 2^d`** — the full size control on a
switched bottom gate that a width/clause-count-aware alternation invariant will thread through the rounds, so
the terminal `DNF` meets the survivor budget `hterm` and the last oracle fires on the *actual* collapsed gate.

* `dtreeToDNF_length` / `dtreeToCNF_length` — `≤ 2 ^ depth t` clauses.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Clause-count bound (DNF).**  The accepting-path DNF of a depth-`d` tree has at most `2 ^ d` terms. -/
theorem dtreeToDNF_length (t : DTree n) : (dtreeToDNF t).length ≤ 2 ^ t.depth := by
  induction t with
  | leaf b => cases b <;> simp [dtreeToDNF, DTree.depth]
  | node v lo hi ihlo ihhi =>
    have hml := le_max_left lo.depth hi.depth
    have hmr := le_max_right lo.depth hi.depth
    rw [dtreeToDNF, List.length_append, List.length_map, List.length_map]
    show (dtreeToDNF hi).length + (dtreeToDNF lo).length ≤ 2 ^ (max lo.depth hi.depth + 1)
    calc (dtreeToDNF hi).length + (dtreeToDNF lo).length
        ≤ 2 ^ hi.depth + 2 ^ lo.depth := Nat.add_le_add ihhi ihlo
      _ ≤ 2 ^ (max lo.depth hi.depth) + 2 ^ (max lo.depth hi.depth) :=
          Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) hmr)
            (Nat.pow_le_pow_right (by norm_num) hml)
      _ = 2 ^ (max lo.depth hi.depth + 1) := by rw [pow_succ]; ring

/-- **Clause-count bound (CNF).**  The rejecting-path CNF of a depth-`d` tree has at most `2 ^ d` clauses. -/
theorem dtreeToCNF_length (t : DTree n) : (dtreeToCNF t).length ≤ 2 ^ t.depth := by
  induction t with
  | leaf b => cases b <;> simp [dtreeToCNF, DTree.depth]
  | node v lo hi ihlo ihhi =>
    have hml := le_max_left lo.depth hi.depth
    have hmr := le_max_right lo.depth hi.depth
    rw [dtreeToCNF, List.length_append, List.length_map, List.length_map]
    show (dtreeToCNF hi).length + (dtreeToCNF lo).length ≤ 2 ^ (max lo.depth hi.depth + 1)
    calc (dtreeToCNF hi).length + (dtreeToCNF lo).length
        ≤ 2 ^ hi.depth + 2 ^ lo.depth := Nat.add_le_add ihhi ihlo
      _ ≤ 2 ^ (max lo.depth hi.depth) + 2 ^ (max lo.depth hi.depth) :=
          Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) hmr)
            (Nat.pow_le_pow_right (by norm_num) hml)
      _ = 2 ^ (max lo.depth hi.depth + 1) := by rw [pow_succ]; ring

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToDNF_length
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.dtreeToCNF_length
