import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ConfigSymbol
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3EncTrans

/-!
# Entry 487 — generic scan loop: the full symbol compare `symbolCompare` (proved)

The complete one-cell symbol comparison of two records: read the record symbol (`readSymbolAt`, entry 484), routing into a
state that remembers it, then go to the config and read its symbol (`configSymbolVerdict`, entry 486) with the verdict
states wired so that **equal symbols reach `matchSt` and unequal reach `failSt`**.  The record symbol read provides the two
paths (`I`/`O`); each path runs its own `configSymbolVerdict` with match/fail swapped accordingly.

`symbolCompare … := readSymbolAt (record) ++ configSymbolVerdict (rec=I path: I↦match,O↦fail) ++ configSymbolVerdict (rec=O
path: I↦fail,O↦match)`.

## What is proved (clean axioms, no `sorry`)

* **`symbolCompare …`** — the full symbol-compare machine.
* **`symbolCompare_run`** (PROVED) — for record symbol `boolToSym3 rsym` and config symbol `boolToSym3 csym` (with the
  field/home/clean hypotheses): `∃ N, reachIn N (s, fsR, tp) ((if rsym = csym then matchSt else failSt), 1+ac+1, tp)` —
  reaching `matchSt` iff the symbols are equal.

## Honest scope

This is the **full symbol compare**.  It does **not** yet combine with the state-field comparison into the full record
comparison, wire it into the scan loop, build the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those
fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SymbolCompare

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3 reachIn_append_left3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadSymbol (readSymbolAt readSymbolAt_run_I readSymbolAt_run_O)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ConfigSymbol
  (configSymbolVerdict configSymbolVerdict_run_I configSymbolVerdict_run_O)

/-- **The full symbol-compare machine.** -/
def symbolCompare (s rm1 rcont rm2 sRecI sRecO igm igf igc irm irc irm2 ogm ogf ogc orm orc orm2 matchSt failSt : ℕ) :
    TMachine3 :=
  readSymbolAt s rm1 rcont rm2 sRecI sRecO
    ++ configSymbolVerdict sRecI igm igf igc irm irc irm2 matchSt failSt
    ++ configSymbolVerdict sRecO ogm ogf ogc orm orc orm2 failSt matchSt

/-- **The full symbol compare: `matchSt` iff symbols equal (PROVED).** -/
theorem symbolCompare_run (s rm1 rcont rm2 sRecI sRecO igm igf igc irm irc irm2 ogm ogf ogc orm orc orm2 matchSt failSt : ℕ)
    (tp : List Sym3) (fsR ar ac : ℕ) (rsym csym : Bool)
    (hRones : ∀ k, k < ar → tp.getD (fsR + k) Sym3.O = Sym3.I) (hRsep : tp.getD (fsR + ar) Sym3.O = Sym3.O)
    (hRsym : tp.getD (fsR + ar + 1) Sym3.O = boolToSym3 rsym) (hRbound : fsR + ar + 1 < tp.length)
    (hmark : tp.getD 0 Sym3.O = Sym3.M) (hclean : ∀ k, 0 < k → k ≤ fsR + ar + 1 → tp.getD k Sym3.O ≠ Sym3.M)
    (hCones : ∀ k, k < ac → tp.getD (1 + k) Sym3.O = Sym3.I) (hCsep : tp.getD (1 + ac) Sym3.O = Sym3.O)
    (hCsym : tp.getD (1 + ac + 1) Sym3.O = boolToSym3 csym) (hCbound : 1 + ac + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (symbolCompare s rm1 rcont rm2 sRecI sRecO igm igf igc irm irc irm2 ogm ogf ogc orm orc orm2
      matchSt failSt)) N (s, fsR, tp) ((if rsym = csym then matchSt else failSt), 1 + ac + 1, tp) := by
  set A := readSymbolAt s rm1 rcont rm2 sRecI sRecO with hA
  set B := configSymbolVerdict sRecI igm igf igc irm irc irm2 matchSt failSt with hB
  set C := configSymbolVerdict sRecO ogm ogf ogc orm orc orm2 failSt matchSt with hC
  cases rsym with
  | true =>
      obtain ⟨Na, hAr⟩ := readSymbolAt_run_I s rm1 rcont rm2 sRecI sRecO tp ar fsR hRones hRsep
        (by rw [hRsym]; rfl) hRbound
      cases csym with
      | true =>
          obtain ⟨Nb, hBr⟩ := configSymbolVerdict_run_I sRecI igm igf igc irm irc irm2 matchSt failSt tp
            (fsR + ar + 1) ac hmark hclean hRbound hCones hCsep (by rw [hCsym]; rfl) hCbound
          rw [if_pos rfl]
          exact ⟨Na + Nb, reachIn_append_left3 (A ++ B) C (Na + Nb) _ _ (reachIn_seq3 A B Na Nb _ _ _ hAr hBr)⟩
      | false =>
          obtain ⟨Nb, hBr⟩ := configSymbolVerdict_run_O sRecI igm igf igc irm irc irm2 matchSt failSt tp
            (fsR + ar + 1) ac hmark hclean hRbound hCones hCsep (by rw [hCsym]; rfl) hCbound
          rw [if_neg (by decide)]
          exact ⟨Na + Nb, reachIn_append_left3 (A ++ B) C (Na + Nb) _ _ (reachIn_seq3 A B Na Nb _ _ _ hAr hBr)⟩
  | false =>
      obtain ⟨Na, hAr⟩ := readSymbolAt_run_O s rm1 rcont rm2 sRecI sRecO tp ar fsR hRones hRsep
        (by rw [hRsym]; rfl) hRbound
      have hAr' := reachIn_append_left3 A B Na _ _ hAr
      cases csym with
      | true =>
          obtain ⟨Nc, hCr⟩ := configSymbolVerdict_run_I sRecO ogm ogf ogc orm orc orm2 failSt matchSt tp
            (fsR + ar + 1) ac hmark hclean hRbound hCones hCsep (by rw [hCsym]; rfl) hCbound
          rw [if_neg (by decide)]
          exact ⟨Na + Nc, reachIn_seq3 (A ++ B) C Na Nc _ _ _ hAr' hCr⟩
      | false =>
          obtain ⟨Nc, hCr⟩ := configSymbolVerdict_run_O sRecO ogm ogf ogc orm orc orm2 failSt matchSt tp
            (fsR + ar + 1) ac hmark hclean hRbound hCones hCsep (by rw [hCsym]; rfl) hCbound
          rw [if_pos rfl]
          exact ⟨Na + Nc, reachIn_seq3 (A ++ B) C Na Nc _ _ _ hAr' hCr⟩

/-!
**The full symbol compare, proved.**  `symbolCompare` reaches `matchSt` exactly when the two records' symbols agree —
completing the symbol half of the record comparison (the state half is entries 480–483).  Next: combine the state and symbol
comparisons into the full record comparison, then wire it into the scan loop — fragment by verified fragment, not faked.  Not
a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SymbolCompare

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SymbolCompare.symbolCompare_run
