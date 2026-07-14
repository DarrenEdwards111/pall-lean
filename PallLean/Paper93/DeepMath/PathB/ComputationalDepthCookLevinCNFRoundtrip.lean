import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinCNFMachine

/-!
# Cook–Levin M1 — the `satCNF` evaluator glue (encode roundtrip)

`cnfMachine` (CookLevinCNFMachine) decides `satCNF x = (foldCNF x (firstEndFormula x)).2`, the machine-level
`⋀`-clauses-`⋁`-literals fold on a token stream.  This file closes the **glue** deferred there: the roundtrip
`satCNF (encodeCNF cls) = cls.all (·.any id)` — the machine, run on an *encoded* CNF, computes exactly the clean
list-level Boolean value (each clause is the `OR` of its inline literal values; the formula is their `AND`).

The heart is a **fold-shift lemma** over an append (`foldRest_shift`): folding across a length-`2n` prefix then
continuing is the same as continuing the fold on the suffix from the prefix's accumulator.  With it, one literal /
one clause / the whole formula each reduce cleanly.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinCNFRoundtrip

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFMachine

/-- `getD` on the right part of an append (local copy). -/
theorem getD_append_ge {l l' : List Bool} {n : ℕ} (h : l.length ≤ n) :
    (l ++ l').getD n false = l'.getD (n - l.length) false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, List.getD_eq_getElem?_getD]

/-- `encodeClause` uses `2(|cl|+1)` bits: `|cl|` literal tokens plus the end-of-clause token. -/
theorem encodeClause_length (cl : List Bool) : (encodeClause cl).length = 2 * (cl.length + 1) := by
  induction cl with
  | nil => rfl
  | cons b cl' ih => simp only [encodeClause, List.length_cons, ih]; omega

/-- The `(clause-OR, formula-AND)` fold from an arbitrary starting accumulator. -/
def foldRest (x : List Bool) (a : Bool × Bool) : ℕ → Bool × Bool
  | 0 => a
  | m + 1 =>
    if x.getD (2 * m) false then ((foldRest x a m).1 || x.getD (2 * m + 1) false, (foldRest x a m).2)
    else (false, (foldRest x a m).2 && (foldRest x a m).1)

/-- `foldCNF` is `foldRest` from the initial accumulator `(false, true)`. -/
theorem foldCNF_eq (x : List Bool) (j : ℕ) : foldCNF x j = foldRest x (false, true) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [foldCNF, foldRest, ih]

/-- **Fold-shift over an append.**  With `|pre| = 2n`, folding `n+m` tokens is: fold `n` tokens (through `pre`), then
fold `m` more on `rest` from that accumulator. -/
theorem foldRest_shift (pre rest : List Bool) (n : ℕ) (hpre : pre.length = 2 * n) (a : Bool × Bool) (m : ℕ) :
    foldRest (pre ++ rest) a (n + m) = foldRest rest (foldRest (pre ++ rest) a n) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hp0 : (pre ++ rest).getD (2 * (n + m)) false = rest.getD (2 * m) false := by
      rw [getD_append_ge (by rw [hpre]; omega), hpre, show 2 * (n + m) - 2 * n = 2 * m from by omega]
    have hp1 : (pre ++ rest).getD (2 * (n + m) + 1) false = rest.getD (2 * m + 1) false := by
      rw [getD_append_ge (by rw [hpre]; omega), hpre, show 2 * (n + m) + 1 - 2 * n = 2 * m + 1 from by omega]
    rw [show n + (m + 1) = (n + m) + 1 from by omega, foldRest, hp0, hp1, ih, foldRest]

/-- **One clause.**  Folding `encodeClause cl` (its `|cl|` literals then the end-of-clause marker) from `(c, f)`
lands at `(false, f && (c || cl.any id))` — the clause's literal-`OR` (seeded by `c`) is `AND`-ed into `f`. -/
theorem clause_fold (cl : List Bool) : ∀ (rest : List Bool) (c f : Bool),
    foldRest (encodeClause cl ++ rest) (c, f) (cl.length + 1) = (false, f && (c || cl.any id)) := by
  induction cl with
  | nil =>
    intro rest c f
    show foldRest ([false, true] ++ rest) (c, f) 1 = _
    rw [foldRest]
    simp [foldRest]
  | cons b cl' ih =>
    intro rest c f
    -- encodeClause (b :: cl') = [true, b] ++ encodeClause cl'; |b::cl'|+1 = 1 + (cl'.length+1)
    have hsplit : encodeClause (b :: cl') ++ rest = [true, b] ++ (encodeClause cl' ++ rest) := by
      simp [encodeClause]
    rw [hsplit, show (b :: cl').length + 1 = 1 + (cl'.length + 1) from by simp; omega,
      foldRest_shift [true, b] (encodeClause cl' ++ rest) 1 rfl (c, f) (cl'.length + 1)]
    have h1 : foldRest ([true, b] ++ (encodeClause cl' ++ rest)) (c, f) 1 = (c || b, f) := by
      rw [foldRest]; rfl
    rw [h1, ih rest (c || b) f]
    simp [List.any_cons, Bool.or_assoc]

/-- Token count of an encoded CNF (= the end-of-formula token index). -/
def tokenCount : List (List Bool) → ℕ
  | [] => 0
  | cl :: cls => (cl.length + 1) + tokenCount cls

/-- **The whole formula.**  Folding `encodeCNF cls` through all its tokens from `(false, f)` lands at
`(false, f && cls.all (·.any id))`. -/
theorem cnf_fold (cls : List (List Bool)) : ∀ (f : Bool),
    foldRest (encodeCNF cls) (false, f) (tokenCount cls) = (false, f && cls.all (·.any id)) := by
  induction cls with
  | nil => intro f; simp [encodeCNF, tokenCount, foldRest]
  | cons cl cls ih =>
    intro f
    rw [encodeCNF, tokenCount,
      foldRest_shift (encodeClause cl) (encodeCNF cls) (cl.length + 1) (encodeClause_length cl) (false, f)
        (tokenCount cls),
      clause_fold cl (encodeCNF cls) false f, ih (f && (false || cl.any id))]
    simp [List.all_cons, Bool.and_assoc]

/-- The fold over the whole encoded CNF, at the end-of-formula token, is the clean CNF value. -/
theorem foldCNF_encodeCNF (cls : List (List Bool)) :
    foldCNF (encodeCNF cls) (tokenCount cls) = (false, cls.all (·.any id)) := by
  rw [foldCNF_eq, cnf_fold cls true]; simp

/-! ## Locating the end-of-formula token -/

/-- The encoded CNF has `2·tokenCount + 2` bits. -/
theorem encodeCNF_length (cls : List (List Bool)) : (encodeCNF cls).length = 2 * tokenCount cls + 2 := by
  induction cls with
  | nil => rfl
  | cons cl cls ih => rw [encodeCNF, tokenCount, List.length_append, encodeClause_length, ih]; ring

/-- The end-of-formula token `(false, false)` sits at pair-index `tokenCount`. -/
theorem encodeCNF_EF (cls : List (List Bool)) :
    (encodeCNF cls).getD (2 * tokenCount cls) false = false
    ∧ (encodeCNF cls).getD (2 * tokenCount cls + 1) false = false := by
  induction cls with
  | nil => exact ⟨rfl, rfl⟩
  | cons cl cls ih =>
    rw [encodeCNF, tokenCount]
    refine ⟨?_, ?_⟩
    · rw [getD_append_ge (by rw [encodeClause_length]; omega), encodeClause_length,
        show 2 * (cl.length + 1 + tokenCount cls) - 2 * (cl.length + 1) = 2 * tokenCount cls from by omega]
      exact ih.1
    · rw [getD_append_ge (by rw [encodeClause_length]; omega), encodeClause_length,
        show 2 * (cl.length + 1 + tokenCount cls) + 1 - 2 * (cl.length + 1) = 2 * tokenCount cls + 1 from by omega]
      exact ih.2

/-- No token strictly inside a clause's encoding is an end-of-formula token (literals have flag `1`, the
end-of-clause has marker `1`). -/
theorem encodeClause_notEF (cl : List Bool) : ∀ (rest : List Bool) i, i < cl.length + 1 →
    ¬((encodeClause cl ++ rest).getD (2 * i) false = false
      ∧ (encodeClause cl ++ rest).getD (2 * i + 1) false = false) := by
  induction cl with
  | nil =>
    intro rest i hi
    simp only [List.length_nil] at hi
    interval_cases i
    rintro ⟨_, h2⟩
    simp [encodeClause] at h2
  | cons b cl' ih =>
    intro rest i hi
    simp only [List.length_cons] at hi
    cases i with
    | zero => rintro ⟨h1, _⟩; simp [encodeClause] at h1
    | succ i =>
      have hsplit : encodeClause (b :: cl') ++ rest = [true, b] ++ (encodeClause cl' ++ rest) := by
        simp [encodeClause]
      rw [hsplit,
        show ([true, b] ++ (encodeClause cl' ++ rest)).getD (2 * (i + 1)) false
          = (encodeClause cl' ++ rest).getD (2 * i) false from by
            rw [getD_append_ge (by simp only [List.length_cons, List.length_nil]; omega),
              show 2 * (i + 1) - [true, b].length = 2 * i from by
                simp only [List.length_cons, List.length_nil]; omega],
        show ([true, b] ++ (encodeClause cl' ++ rest)).getD (2 * (i + 1) + 1) false
          = (encodeClause cl' ++ rest).getD (2 * i + 1) false from by
            rw [getD_append_ge (by simp only [List.length_cons, List.length_nil]; omega),
              show 2 * (i + 1) + 1 - [true, b].length = 2 * i + 1 from by
                simp only [List.length_cons, List.length_nil]; omega]]
      exact ih rest i (by omega)

/-- No token before `tokenCount` is an end-of-formula token. -/
theorem encodeCNF_notEF (cls : List (List Bool)) : ∀ i, i < tokenCount cls →
    ¬((encodeCNF cls).getD (2 * i) false = false ∧ (encodeCNF cls).getD (2 * i + 1) false = false) := by
  induction cls with
  | nil => intro i hi; simp [tokenCount] at hi
  | cons cl cls ih =>
    intro i hi
    rw [tokenCount] at hi
    rw [encodeCNF]
    by_cases hlt : i < cl.length + 1
    · exact encodeClause_notEF cl (encodeCNF cls) i hlt
    · rw [show (encodeClause cl ++ encodeCNF cls).getD (2 * i) false
          = (encodeCNF cls).getD (2 * (i - (cl.length + 1))) false from by
            rw [getD_append_ge (by rw [encodeClause_length]; omega), encodeClause_length,
              show 2 * i - 2 * (cl.length + 1) = 2 * (i - (cl.length + 1)) from by omega],
        show (encodeClause cl ++ encodeCNF cls).getD (2 * i + 1) false
          = (encodeCNF cls).getD (2 * (i - (cl.length + 1)) + 1) false from by
            rw [getD_append_ge (by rw [encodeClause_length]; omega), encodeClause_length,
              show 2 * i + 1 - 2 * (cl.length + 1) = 2 * (i - (cl.length + 1)) + 1 from by omega]]
      exact ih (i - (cl.length + 1)) (by omega)

/-- The machine's halt token on an encoded CNF is exactly `tokenCount`. -/
theorem firstEndFormula_encodeCNF (cls : List (List Bool)) :
    firstEndFormula (encodeCNF cls) = tokenCount cls := by
  rw [firstEndFormula, Nat.find_eq_iff]
  exact ⟨encodeCNF_EF cls, fun i hi _ => encodeCNF_notEF cls i hi ‹_›⟩

/-! ## The roundtrip -/

/-- **`satCNF` evaluator glue.**  Run on an encoded CNF, the machine computes exactly the clean list value:
each clause is the `OR` of its literal values, and the formula is their `AND`. -/
theorem satCNF_roundtrip (cls : List (List Bool)) :
    satCNF (encodeCNF cls) = cls.all (·.any id) := by
  rw [satCNF, firstEndFormula_encodeCNF, foldCNF_encodeCNF]

end PallLean.Paper93.DeepMath.PathB.CookLevinCNFRoundtrip
