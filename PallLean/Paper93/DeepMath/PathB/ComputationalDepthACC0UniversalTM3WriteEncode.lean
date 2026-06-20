import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3WriteField
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Encode

/-!
# Entry 424 — universal-TM-table build: the writer emits the encoding `writeFieldBlock_eq_encode` (proved)

The field writer (entry 422) produces a `writeFieldBlock` tape; toward `EmitsEncodedStep3` we must know that what it writes
is *exactly the abstract encoding* `encodeNatBits3` (entry 392).  This brick proves that correspondence: writing a unary
field of length `n` at position `j = pre.length` overwrites the next `n+1` cells with `encodeNatBits3 n`, leaving the prefix
and the tail (beyond the field) intact.

This is the **writer-correctness** lemma — the output side's connection between the machine's tape and the encoding it is
supposed to emit.

## What is proved (clean axioms, no `sorry`)

* **`writeFieldBlock_eq_encode`** (PROVED) — `n < X.length ⇒ writeFieldBlock (pre ++ X) pre.length n = pre ++
  encodeNatBits3 n ++ X.drop (n+1)`: the writer lays down `encodeNatBits3 n` in place.
* **`writeUnaryFieldN3_emits`** (PROVED) — the run corollary: `∃ N, reachIn N (s, pre.length, pre ++ X) (sOut,
  pre.length + n, pre ++ encodeNatBits3 n ++ X.drop (n+1))` — running the writer emits the encoded field.

## Honest scope

This is the **writer-emits-the-encoding** correctness.  It does **not** yet emit a full encoded configuration, nor assemble
`EmitsEncodedStep3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteEncode

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteField (writeFieldBlock writeUnaryFieldN3 writeUnaryFieldN3_run)

/-- An in-bounds write is a `List.set`. -/
private theorem writeAt3_eq_set (tp : List Sym3) (p : ℕ) (w : Sym3) (hp : p < tp.length) :
    writeAt3 tp p w = tp.set p w := by
  unfold writeAt3
  rw [show p + 1 - tp.length = 0 from by omega, List.replicate_zero, List.append_nil]

/-- Setting the cell just past a prefix replaces the head of the suffix. -/
private theorem set_at_boundary (A l : List Sym3) (x y : Sym3) :
    (A ++ (x :: l)).set A.length y = A ++ (y :: l) := by
  induction A with
  | nil => rfl
  | cons a A ih =>
      show a :: ((A ++ (x :: l)).set A.length y) = a :: (A ++ (y :: l))
      rw [ih]

/-- `encodeNatBits3 (n+1) = I :: encodeNatBits3 n`. -/
private theorem encodeNatBits3_succ (n : ℕ) : encodeNatBits3 (n + 1) = Sym3.I :: encodeNatBits3 n := by
  rw [encodeNatBits3, encodeNatBits3, List.replicate_succ, List.cons_append]

/-- **The writer emits the encoding (PROVED).**  Writing a unary field of length `n` at `pre.length` lays down
`encodeNatBits3 n` over the next `n+1` cells, prefix and tail intact. -/
theorem writeFieldBlock_eq_encode (pre X : List Sym3) (n : ℕ) (hX : n < X.length) :
    writeFieldBlock (pre ++ X) pre.length n = pre ++ encodeNatBits3 n ++ X.drop (n + 1) := by
  induction n generalizing pre X with
  | zero =>
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil (show X ≠ [] by rintro rfl; simp at hX)
      show writeAt3 (pre ++ (x :: xs)) pre.length Sym3.O = pre ++ encodeNatBits3 0 ++ (x :: xs).drop (0 + 1)
      rw [writeAt3_eq_set _ _ _ (by simp), set_at_boundary]
      simp [encodeNatBits3]
  | succ n ih =>
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil (show X ≠ [] by rintro rfl; simp at hX)
      show writeFieldBlock (writeAt3 (pre ++ (x :: xs)) pre.length Sym3.I) (pre.length + 1) n
        = pre ++ encodeNatBits3 (n + 1) ++ (x :: xs).drop (n + 1 + 1)
      rw [writeAt3_eq_set _ _ _ (by simp), set_at_boundary,
        show pre ++ (Sym3.I :: xs) = (pre ++ [Sym3.I]) ++ xs from by simp,
        show pre.length + 1 = (pre ++ [Sym3.I]).length from by simp]
      rw [ih (pre ++ [Sym3.I]) xs (by simp only [List.length_cons] at hX; omega), encodeNatBits3_succ]
      simp

/-- **The writer-emits run corollary (PROVED).**  Running `writeUnaryFieldN3` on `pre ++ X` emits `encodeNatBits3 n`. -/
theorem writeUnaryFieldN3_emits (s sOut n : ℕ) (pre X : List Sym3) (hX : n < X.length) :
    ∃ N, reachIn (toNTM3 (writeUnaryFieldN3 s sOut n)) N (s, pre.length, pre ++ X)
      (sOut, pre.length + n, pre ++ encodeNatBits3 n ++ X.drop (n + 1)) := by
  obtain ⟨N, h⟩ := writeUnaryFieldN3_run sOut n s pre.length (pre ++ X)
  rw [writeFieldBlock_eq_encode pre X n hX] at h
  exact ⟨N, h⟩

/-!
**The writer emits the encoding, proved.**  `writeFieldBlock_eq_encode` shows the field writer's output is exactly
`encodeNatBits3` — the output-side correctness linking the machine's tape to the abstract encoding.  Next: chain to emit a
full encoded configuration, and assemble `EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteEncode

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteEncode.writeFieldBlock_eq_encode
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3WriteEncode.writeUnaryFieldN3_emits
