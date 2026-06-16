import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ConcreteNTM

/-!
# The tape-rewrite sub-machine — write correctness/locality proved, physical rewrite socketed

The third sub-machine of the physical universal machine rewrites the simulated tape: it realises `writeAt` (write a
symbol at the simulated head, extending the tape if needed).  The genuinely-provable spec is the **write contract**:

* **read-after-write** — reading the head after writing `w` gives `w`;
* **locality elsewhere** — every other cell is unchanged;
* **minimal extension** — the tape grows only to cover the written cell (length `= max tape.length (p+1)`).

The physical realisation — `U`-transitions that rewrite the simulated cell on the `encodeTape` layout — is the socket.

## What is proved (clean axioms, no `sorry`)

* **`writeAt_length`** — `(writeAt tape p w).length = max tape.length (p+1)` (minimal extension / locality of the region).
* **`writeAt_getD_self`** — read-after-write: `(writeAt tape p w).getD p false = w`.
* **`writeAt_getD_ne`** — elsewhere unchanged: `q ≠ p → (writeAt tape p w).getD q false = tape.getD q false`.
* **`applyTrans_write`** — applying a rule writes its symbol at the old head: `(applyTrans c t).2.2.getD c.2.1 false =
  t.2.2.1`.

## Honest scope

The write *contract* (read-after-write, unchanged-elsewhere, minimal extension) is proved — what the physical rewrite
sub-machine must satisfy.  Realising it as `U`-transitions over the `encodeTape` layout is the socket.  This does
**not** build the physical sub-machine.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`,
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TapeRewrite

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (CConfig TMTrans writeAt applyTrans)

/-- **Appending `false`-padding does not change `getD … false` (proved).**  The padding cells equal the default. -/
theorem appendReplicate_getD (l : List Bool) (n q : ℕ) :
    (l ++ List.replicate n false).getD q false = l.getD q false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases hq : q < l.length
  · rw [List.getElem?_append_left hq]
  · push_neg at hq
    rw [List.getElem?_eq_none hq]
    by_cases hq2 : q < l.length + n
    · rw [List.getElem?_append_right hq, List.getElem?_replicate]
      simp [show q - l.length < n by omega]
    · push_neg at hq2
      rw [List.getElem?_eq_none (by rw [List.length_append, List.length_replicate]; omega)]

/-- **Minimal extension (proved): `(writeAt tape p w).length = max tape.length (p+1)`.** -/
theorem writeAt_length (tape : List Bool) (p : ℕ) (w : Bool) :
    (writeAt tape p w).length = max tape.length (p + 1) := by
  unfold writeAt
  rw [List.length_set, List.length_append, List.length_replicate]
  omega

/-- **Read-after-write (proved): `(writeAt tape p w).getD p false = w`.** -/
theorem writeAt_getD_self (tape : List Bool) (p : ℕ) (w : Bool) :
    (writeAt tape p w).getD p false = w := by
  have hp : p < (tape ++ List.replicate (p + 1 - tape.length) false).length := by
    rw [List.length_append, List.length_replicate]; omega
  unfold writeAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hp]
  rfl

/-- **Elsewhere unchanged (proved): `q ≠ p → (writeAt tape p w).getD q false = tape.getD q false`.** -/
theorem writeAt_getD_ne (tape : List Bool) (p : ℕ) (w : Bool) {q : ℕ} (hq : q ≠ p) :
    (writeAt tape p w).getD q false = tape.getD q false := by
  unfold writeAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hq), ← List.getD_eq_getElem?_getD]
  exact appendReplicate_getD tape _ q

/-- **Applying a rule writes its symbol at the old head (proved): `(applyTrans c t).2.2.getD c.2.1 false = t.2.2.1`.** -/
theorem applyTrans_write (c : CConfig) (t : TMTrans) :
    (applyTrans c t).2.2.getD c.2.1 false = t.2.2.1 := by
  simp only [applyTrans]
  exact writeAt_getD_self c.2.2 c.2.1 t.2.2.1

end PallLean.Paper93.DeepMath.PathB.ACC0TapeRewrite

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TapeRewrite.writeAt_length
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TapeRewrite.writeAt_getD_self
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TapeRewrite.writeAt_getD_ne
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TapeRewrite.applyTrans_write
