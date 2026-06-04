import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyLabel

/-!
# Per-step-clause decode: `deepestSatSel` from the (clause, position) sequence — unconditionally

The pure-satisfy decode (`deepestSatSel_eq_decode_pure_satisfy`) decoded all positions through *one*
constant clause.  Here is the **general, hypothesis-free** version: record each satisfy step's *own*
active clause together with its position, and decode each pair through its recorded clause.  This
recovers `deepestSatSel` for **any** branch (interleaved falsify steps included).

* `deepestSatSeq` — the per-satisfy-step `(active clause, position)` list (mirrors `deepestSatPos`,
  pairing each recorded position with its clause).
* `decodeSatSeq` — decode each `(clause, position)` pair to its variable.
* `deepestSatSel_eq_decodeSatSeq` — **the recovery**: `deepestSel`'s satisfy part equals the decoded
  `(clause, position)` sequence, with *no* regime hypothesis.

This isolates the remaining open core precisely: the decoder must recover the *clause* of each
satisfy step from the end-state.  The clause side is supplied by `deepestSel_mem_leaf_clause` (the
clauses are leaf-readable) and `deepest_falsified_clause_active` (read-once); what remains is
assigning consecutive positions to clauses in `cs`-order (the block delimiting).  Not faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The per-satisfy-step `(active clause, position)` list: at each satisfy step record the active
clause `T` and the canonical position `pivotPosOf cs σ`; skip falsify steps.  Mirrors `deepestSatPos`,
pairing each position with the clause it indexes into. -/
def deepestSatSeq (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → List (Clause n × ℕ)
  | 0, _ => []
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then []
    else match SwitchingCounting.activeTerm cs σ with
      | none => []
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => []
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ
                 then id else List.cons (T, SwitchingCounting.pivotPosOf cs σ))
                 (deepestSatSeq cs fuel (fixVar σ (litVar ℓ) false))
          else (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ
                 then id else List.cons (T, SwitchingCounting.pivotPosOf cs σ))
                 (deepestSatSeq cs fuel (fixVar σ (litVar ℓ) true))

/-- Decode a `(clause, position)` sequence: map each pair to the variable of the clause's literal at
that position. -/
def decodeSatSeq (l : List (Clause n × ℕ)) : Finset (Fin n) :=
  (l.filterMap (fun cp => (SwitchingCounting.clauseLitAt cp.1 cp.2).map litVar)).toFinset

/-- One decoded `(clause, position)` pair prepends its variable. -/
theorem decodeSatSeq_cons (C : Clause n) (p : ℕ) {v : Fin n} {l : List (Clause n × ℕ)}
    (h : (SwitchingCounting.clauseLitAt C p).map litVar = some v) :
    decodeSatSeq ((C, p) :: l) = insert v (decodeSatSeq l) := by
  unfold decodeSatSeq
  simp only [List.filterMap_cons, h, List.toFinset_cons]

/-- **The general per-step-clause recovery.**  With each position decoded through its *own* recorded
active clause, the decoded sequence is exactly `deepestSatSel` — for any branch, no regime hypothesis. -/
theorem deepestSatSel_eq_decodeSatSeq (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool),
      deepestSatSel cs F σ = decodeSatSeq (deepestSatSeq cs F σ) := by
  intro F
  induction F with
  | zero => intro σ; rw [deepestSatSel, deepestSatSeq]; rfl
  | succ F ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestSatSel, deepestSatSeq]; simp only [hany, if_true]; rfl
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => rw [deepestSatSel, deepestSatSeq]; simp only [hany, Bool.false_eq_true, if_false, hact]; rfl
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestSatSel, deepestSatSeq]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]; rfl
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hclat : (SwitchingCounting.clauseLitAt T (SwitchingCounting.pivotPosOf cs σ)).map litVar
              = some (litVar ℓ) := by
            rw [SwitchingCounting.clauseLitAt_pivotPosOf hact (by rw [hatl]; rfl), hatl]; rfl
          by_cases hd : (canonicalDT cs F (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs F (fixVar σ (litVar ℓ) false)).depth
          · rw [deepestSatSel, deepestSatSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh]
            rw [if_pos hd, if_pos hd]
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ = true
            · rw [if_pos hf, if_pos hf]; simp only [id_eq]; exact ih (fixVar σ (litVar ℓ) false)
            · rw [Bool.not_eq_true] at hf
              rw [if_neg (by rw [hf]; simp), if_neg (by rw [hf]; simp)]
              rw [decodeSatSeq_cons T (SwitchingCounting.pivotPosOf cs σ) hclat,
                ih (fixVar σ (litVar ℓ) false)]
          · rw [deepestSatSel, deepestSatSeq]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh]
            rw [if_neg hd, if_neg hd]
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ = true
            · rw [if_pos hf, if_pos hf]; simp only [id_eq]; exact ih (fixVar σ (litVar ℓ) true)
            · rw [Bool.not_eq_true] at hf
              rw [if_neg (by rw [hf]; simp), if_neg (by rw [hf]; simp)]
              rw [decodeSatSeq_cons T (SwitchingCounting.pivotPosOf cs σ) hclat,
                ih (fixVar σ (litVar ℓ) true)]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSatSel_eq_decodeSatSeq
