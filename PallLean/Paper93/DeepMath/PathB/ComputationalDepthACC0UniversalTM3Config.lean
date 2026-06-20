import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3FieldContent
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3EncTrans
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Unmark

/-!
# Entry 413 — universal-TM-table build: the configuration layout & symbol write `configEncode3` (proved)

The matcher (entries 407–410) and the field copy (entries 411–412) worked against *abstract* content hypotheses about the
configuration key.  This brick pins down the **configuration layout** concretely and proves the first apply operation,
the **symbol write**.

The layout mirrors the rule key (`encodeTransBits3`, entry 393): the simulated machine's configuration begins with its
current state as a unary field, then a single cell holding the current symbol, then the rest of the simulated tape:
`configEncode3 q sym rest = encodeNatBits3 q ++ boolToSym3 sym :: rest`.  So on a tape `pre ++ configEncode3 q sym rest`
with `pre.length = c`, the state field is `c … c+q` (`q` ones then the `O` separator) and the current-symbol cell is at
`c+q+1` — exactly the positions the matcher used (`a = q`, symbol at `c+a+1`).

The symbol write overwrites the current-symbol cell with the rule's write symbol.  After the matcher succeeds the head is
already at that cell, so the write is a single `unmark3` step; the content lemma is that this updates only the symbol
field of the encoded configuration.

## What is proved (clean axioms, no `sorry`)

* **`configEncode3 q sym rest`** — `encodeNatBits3 q ++ boolToSym3 sym :: rest`.
* **`configEncode3_content`** (PROVED) — the bridge to the matcher: the state field (`q` ones at `c`, `O` at `c+q`) and
  the symbol cell (`boolToSym3 sym` at `c+q+1`), where `c = pre.length`.
* **`configEncode3_set_sym`** (PROVED) — the list surgery: `writeAt3 (pre ++ configEncode3 q sym rest) (c+q+1)
  (boolToSym3 sym') = pre ++ configEncode3 q sym' rest`.
* **`writeSym3_run`** (PROVED) — with the head at the symbol cell, one `unmark3` step rewrites the configuration's symbol
  field from `sym` to `sym'`, the rest untouched.

## Honest scope

This **pins the configuration layout** and proves the **symbol write**.  It does **not** yet carry the write symbol from
the rule, move the simulated head, nor assemble `apply3`.  Building those fragment by fragment is the genuine remaining
construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3 writeAt3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Encode (encodeNatBits3 encodeNatBits3_length)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldContent (field_content3 getD_append_shift3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Unmark (unmark3 unmark3_run)

/-- **The configuration layout.**  Current state (unary), then the current-symbol cell, then the rest of the simulated
tape. -/
def configEncode3 (q : ℕ) (sym : Bool) (rest : List Sym3) : List Sym3 :=
  encodeNatBits3 q ++ boolToSym3 sym :: rest

/-- **The configuration content (PROVED).**  State field `q` ones at `c` then `O` at `c+q`, symbol cell at `c+q+1` — the
hypotheses the matcher consumes, with `c = pre.length`. -/
theorem configEncode3_content (pre rest : List Sym3) (q : ℕ) (sym : Bool) :
    (∀ i, i < q → (pre ++ configEncode3 q sym rest).getD (pre.length + i) Sym3.O = Sym3.I)
    ∧ (pre ++ configEncode3 q sym rest).getD (pre.length + q) Sym3.O = Sym3.O
    ∧ (pre ++ configEncode3 q sym rest).getD (pre.length + q + 1) Sym3.O = boolToSym3 sym := by
  have hfc := field_content3 pre (boolToSym3 sym :: rest) (pre ++ configEncode3 q sym rest) q pre.length rfl
    (by rw [configEncode3])
  refine ⟨hfc.1, hfc.2, ?_⟩
  have hassoc : pre ++ configEncode3 q sym rest = (pre ++ encodeNatBits3 q) ++ (boolToSym3 sym :: rest) := by
    rw [configEncode3, List.append_assoc]
  rw [hassoc, show pre.length + q + 1 = (pre ++ encodeNatBits3 q).length + 0 from by
    rw [List.length_append, encodeNatBits3_length]; omega, getD_append_shift3]
  rfl

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

/-- **The symbol-write surgery (PROVED).**  Overwriting the current-symbol cell `c+q+1` with `boolToSym3 sym'` updates
only the configuration's symbol field. -/
theorem configEncode3_set_sym (pre rest : List Sym3) (q : ℕ) (sym sym' : Bool) :
    writeAt3 (pre ++ configEncode3 q sym rest) (pre.length + q + 1) (boolToSym3 sym')
      = pre ++ configEncode3 q sym' rest := by
  have hlt : pre.length + q + 1 < (pre ++ configEncode3 q sym rest).length := by
    simp only [configEncode3, encodeNatBits3, List.length_append, List.length_cons, List.length_replicate]
    omega
  rw [writeAt3_eq_set _ _ _ hlt]
  unfold configEncode3
  rw [← List.append_assoc, show pre.length + q + 1 = (pre ++ encodeNatBits3 q).length from by
    rw [List.length_append, encodeNatBits3_length]; omega, set_at_boundary, List.append_assoc]

/-- **The symbol-write step run (PROVED).**  With the head at the current-symbol cell `c+q+1`, one `unmark3` step rewrites
the configuration's symbol from `sym` to `sym'`, the rest of the tape untouched. -/
theorem writeSym3_run (s s' q : ℕ) (sym sym' : Bool) (pre rest : List Sym3) :
    reachIn (toNTM3 (unmark3 s s' (boolToSym3 sym'))) 1
      (s, pre.length + q + 1, pre ++ configEncode3 q sym rest)
      (s', pre.length + q + 1, pre ++ configEncode3 q sym' rest) := by
  have h := unmark3_run s s' (boolToSym3 sym') (pre.length + q + 1) (pre ++ configEncode3 q sym rest)
  rwa [configEncode3_set_sym] at h

/-!
**The configuration layout & symbol write, proved.**  `configEncode3` fixes how the simulated state/symbol/tape sit on
the marker tape (consistent with the rule encoding), and `writeSym3_run` performs the apply phase's symbol update on it.
Next: carry the write symbol from the matched rule, move the simulated head, and assemble `apply3` — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config.configEncode3_set_sym
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Config.writeSym3_run
