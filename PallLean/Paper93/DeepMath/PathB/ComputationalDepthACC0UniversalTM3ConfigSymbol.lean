import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ReadSymbol
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3GotoConfig

/-!
# Entry 486 — generic scan loop: read the config symbol `configSymbolVerdict` (proved)

The config-side half of the symbol compare: from a record position, navigate back to the config field start (`gotoConfigStart`,
entry 485) and read the config symbol there (`readSymbolAt`, entry 484), routing on whether it is `I` or `O`.  Composed with
a prior record-symbol read (which remembers the record symbol in the control state, routing into the right verdict states),
this gives the full symbol comparison of two records.

`configSymbolVerdict s gm gf gc rm rc rm2 sI sO := gotoConfigStart s gm gf gc ++ readSymbolAt gf rm rc rm2 sI sO`.

## What is proved (clean axioms, no `sorry`)

* **`configSymbolVerdict …`** — go to the config start and read its symbol.
* **`configSymbolVerdict_run_I`** (PROVED) — home marker at `0`, region to the record clean, config field of `ac` ones with
  separator `O` and symbol `I`: `∃ N, reachIn N (s, p, tp) (sI, 1+ac+1, tp)`.
* **`configSymbolVerdict_run_O`** (PROVED) — config symbol `O`: reaches `(sO, 1+ac+1, tp)`.

## Honest scope

This is the **config-side symbol read** (navigate + read).  It does **not** yet combine it with the record-symbol read into
the full symbol compare, wire match-or-advance into the scan loop, build the generic apply, nor a fixed `U` /
`EmitsEncodedStepEx3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ConfigSymbol

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ReadSymbol (readSymbolAt readSymbolAt_run_I readSymbolAt_run_O)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3GotoConfig (gotoConfigStart gotoConfigStart_run)

/-- **Go to the config start and read its symbol.** -/
def configSymbolVerdict (s gm gf gc rm rc rm2 sI sO : ℕ) : TMachine3 :=
  gotoConfigStart s gm gf gc ++ readSymbolAt gf rm rc rm2 sI sO

/-- **Config symbol `I` ⇒ reach `sI` (PROVED).** -/
theorem configSymbolVerdict_run_I (s gm gf gc rm rc rm2 sI sO : ℕ) (tp : List Sym3) (p ac : ℕ)
    (hmark : tp.getD 0 Sym3.O = Sym3.M) (hclean : ∀ k, 0 < k → k ≤ p → tp.getD k Sym3.O ≠ Sym3.M) (hp : p < tp.length)
    (hcones : ∀ k, k < ac → tp.getD (1 + k) Sym3.O = Sym3.I) (hcsep : tp.getD (1 + ac) Sym3.O = Sym3.O)
    (hcsym : tp.getD (1 + ac + 1) Sym3.O = Sym3.I) (hcbound : 1 + ac + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (configSymbolVerdict s gm gf gc rm rc rm2 sI sO)) N (s, p, tp) (sI, 1 + ac + 1, tp) := by
  obtain ⟨N1, h1⟩ := gotoConfigStart_run s gm gf gc p tp hmark hclean hp
  obtain ⟨N2, h2⟩ := readSymbolAt_run_I gf rm rc rm2 sI sO tp ac 1 hcones hcsep hcsym hcbound
  exact ⟨N1 + N2, reachIn_seq3 (gotoConfigStart s gm gf gc) (readSymbolAt gf rm rc rm2 sI sO) N1 N2 _ _ _ h1 h2⟩

/-- **Config symbol `O` ⇒ reach `sO` (PROVED).** -/
theorem configSymbolVerdict_run_O (s gm gf gc rm rc rm2 sI sO : ℕ) (tp : List Sym3) (p ac : ℕ)
    (hmark : tp.getD 0 Sym3.O = Sym3.M) (hclean : ∀ k, 0 < k → k ≤ p → tp.getD k Sym3.O ≠ Sym3.M) (hp : p < tp.length)
    (hcones : ∀ k, k < ac → tp.getD (1 + k) Sym3.O = Sym3.I) (hcsep : tp.getD (1 + ac) Sym3.O = Sym3.O)
    (hcsym : tp.getD (1 + ac + 1) Sym3.O = Sym3.O) (hcbound : 1 + ac + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (configSymbolVerdict s gm gf gc rm rc rm2 sI sO)) N (s, p, tp) (sO, 1 + ac + 1, tp) := by
  obtain ⟨N1, h1⟩ := gotoConfigStart_run s gm gf gc p tp hmark hclean hp
  obtain ⟨N2, h2⟩ := readSymbolAt_run_O gf rm rc rm2 sI sO tp ac 1 hcones hcsep hcsym hcbound
  exact ⟨N1 + N2, reachIn_seq3 (gotoConfigStart s gm gf gc) (readSymbolAt gf rm rc rm2 sI sO) N1 N2 _ _ _ h1 h2⟩

/-!
**The config-side symbol read, proved.**  `configSymbolVerdict` navigates to the config start and reads its symbol — the
config half of the symbol compare.  Next: prefix it with the record-symbol read (routing into the right verdict states) for
the full symbol compare, then wire the record comparison into the scan loop — fragment by verified fragment, not faked.  Not
a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ConfigSymbol

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ConfigSymbol.configSymbolVerdict_run_I
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ConfigSymbol.configSymbolVerdict_run_O
