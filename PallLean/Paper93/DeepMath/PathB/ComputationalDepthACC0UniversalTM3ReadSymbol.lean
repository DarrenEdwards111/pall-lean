import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SkipOnes

/-!
# Entry 484 — generic scan loop: structural symbol read `readSymbolAt` (proved)

After the unary state fields of two records match, the comparison must also check the one-cell *symbol* of each record.  The
symbol sits right after the field's `O` terminator, so a fixed machine reaches it *structurally*: consume the unary field
(`skipOnesRight`, entry 468) to the terminator, step once, and branch on the symbol cell (`branchOne3`, 468) — routing to a
state that remembers `I` vs `O`.  No marker is needed: the field is self-delimiting and the symbol value is carried in the
control state.

`readSymbolAt s m1 cont m2 sI sO := skipOnesRight s m1 cont ++ moveRight3 m1 m2 ++ branchOne3 m2 sI sO`.

## What is proved (clean axioms, no `sorry`)

* **`readSymbolAt …`** — navigate to and read a record's symbol.
* **`readSymbolAt_run_I`** (PROVED) — field of `a` ones, terminator `O`, symbol `I`: `∃ N, reachIn N (s, fs, tp) (sI,
  fs+a+1, tp)`, tape identical.
* **`readSymbolAt_run_O`** (PROVED) — same with symbol `O`: reaches `(sO, fs+a+1, tp)`.

## Honest scope

This is **structural symbol reading** (the symbol-compare's read half, using existing primitives — the verdict half is just
`branchOne3`).  It does **not** wire the symbol compare into the record comparison, build the generic apply, nor a fixed `U`
/ `EmitsEncodedStepEx3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadSymbol

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SkipOnes
  (skipOnesRight skipOnesRight_run branchOne3 branchOne3_run_one branchOne3_run_stop)

/-- **Navigate to and read a record's symbol.**  Consume the unary field, step past the terminator, branch on the symbol. -/
def readSymbolAt (s m1 cont m2 sI sO : ℕ) : TMachine3 :=
  skipOnesRight s m1 cont ++ moveRight3 m1 m2 ++ branchOne3 m2 sI sO

/-- **Reading a record with symbol `I` reaches `sI` (PROVED).** -/
theorem readSymbolAt_run_I (s m1 cont m2 sI sO : ℕ) (tp : List Sym3) (a fs : ℕ)
    (hones : ∀ k, k < a → tp.getD (fs + k) Sym3.O = Sym3.I) (hsep : tp.getD (fs + a) Sym3.O = Sym3.O)
    (hsym : tp.getD (fs + a + 1) Sym3.O = Sym3.I) (hbound : fs + a + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (readSymbolAt s m1 cont m2 sI sO)) N (s, fs, tp) (sI, fs + a + 1, tp) := by
  obtain ⟨N1, h1⟩ := skipOnesRight_run s m1 cont tp a fs hones (by rw [hsep]; decide) (by omega)
  have h2 := moveRight3_run_eq m1 m2 (fs + a) tp (by omega)
  have h3 := branchOne3_run_one m2 sI sO (fs + a + 1) tp hsym (by omega)
  have hAB := reachIn_seq3 (skipOnesRight s m1 cont) (moveRight3 m1 m2) N1 1 _ _ _ h1 h2
  exact ⟨N1 + 1 + 1, reachIn_seq3 (skipOnesRight s m1 cont ++ moveRight3 m1 m2) (branchOne3 m2 sI sO)
    (N1 + 1) 1 _ _ _ hAB h3⟩

/-- **Reading a record with symbol `O` reaches `sO` (PROVED).** -/
theorem readSymbolAt_run_O (s m1 cont m2 sI sO : ℕ) (tp : List Sym3) (a fs : ℕ)
    (hones : ∀ k, k < a → tp.getD (fs + k) Sym3.O = Sym3.I) (hsep : tp.getD (fs + a) Sym3.O = Sym3.O)
    (hsym : tp.getD (fs + a + 1) Sym3.O = Sym3.O) (hbound : fs + a + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (readSymbolAt s m1 cont m2 sI sO)) N (s, fs, tp) (sO, fs + a + 1, tp) := by
  obtain ⟨N1, h1⟩ := skipOnesRight_run s m1 cont tp a fs hones (by rw [hsep]; decide) (by omega)
  have h2 := moveRight3_run_eq m1 m2 (fs + a) tp (by omega)
  have h3 := branchOne3_run_stop m2 sI sO (fs + a + 1) tp
    (by show tp.getD (fs + a + 1) Sym3.O ≠ Sym3.I; rw [hsym]; decide) (by omega)
  have hAB := reachIn_seq3 (skipOnesRight s m1 cont) (moveRight3 m1 m2) N1 1 _ _ _ h1 h2
  exact ⟨N1 + 1 + 1, reachIn_seq3 (skipOnesRight s m1 cont ++ moveRight3 m1 m2) (branchOne3 m2 sI sO)
    (N1 + 1) 1 _ _ _ hAB h3⟩

/-!
**Structural symbol read, proved.**  `readSymbolAt` reaches and reads a record's symbol generically — the read half of the
symbol compare (the verdict half is `branchOne3`).  Next: combine config and record symbol reads into the symbol compare,
then wire the full record comparison into the scan loop — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadSymbol

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadSymbol.readSymbolAt_run_I
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadSymbol.readSymbolAt_run_O
