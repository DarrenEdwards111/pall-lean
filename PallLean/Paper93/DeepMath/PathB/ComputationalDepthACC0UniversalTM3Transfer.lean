import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Navigate
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3CopyFieldLeft

/-!
# Entry 428 — universal-TM-table build: the full field transfer `transferFieldLeft3` (proved)

This assembles the apply's *transfer* end to end: bring a unary field from the matched rule into the configuration.  It
composes the transfer-side navigation (`navigateToSource3`, entry 427) — which reaches the data-dependent rule source
`c+d'` from anywhere in the config window, via the home marker plus the fixed offset `d'` — with the leftward field copy
(`copyFieldLeft3`, entry 415), which copies the field at `c+d'` back to the config region at `c`.

This is the genuine cross-region field transfer, the mechanism that was the recurring wall, now built from proven parts
with no counter-driven walk.

## What is proved (clean axioms, no `sorry`)

* **`transferFieldLeft3 s found cont mid d' sDone L`** — `navigateToSource3 s found cont mid d' ++ copyFieldLeft3 (mid+d')
  sDone d' L`.
* **`transferFieldLeft3_run`** (PROVED) — with the home marker at `home`, no marker in `(home, home+dq]`, budget `m < L`,
  `1 ≤ d'`, `home+1+d'+m < tp.length`, and the rule field (`m` ones then `O` at the source `home+1+d'`): `∃ N, reachIn N
  (s, home+dq, tp) (sDone, home+1+d'+m, copyBlockLeft tp (home+1+d') d' m)` — the rule field is copied into the config at
  `home+1`, from any starting config-window position.

## Honest scope

This is the **full cross-region field transfer** (navigate + copy).  It does **not** yet clear the old config field before
the copy (so it assumes the destination is overwritten cleanly / sized right), nor assemble the complete state update or
`EmitsEncodedStep3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Transfer

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Navigate (navigateToSource3 navigateToSource3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3CopyFieldLeft (copyFieldLeft3 copyFieldLeft3_run copyBlockLeft)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The full field transfer.**  Navigate to the rule source `c+d'`, then copy its field leftward into the config at `c`. -/
def transferFieldLeft3 (s found cont mid d' sDone L : ℕ) : TMachine3 :=
  navigateToSource3 s found cont mid d' ++ copyFieldLeft3 (mid + d') sDone d' L

/-- **The full field transfer run (PROVED).**  Copies the rule field at `home+1+d'` into the config at `home+1`, from any
config-window starting position. -/
theorem transferFieldLeft3_run (s found cont mid d' sDone L home dq m : ℕ) (tp : List Sym3)
    (hmark : tp.getD home Sym3.O = Sym3.M) (hno : ∀ k, 0 < k → k ≤ dq → tp.getD (home + k) Sym3.O ≠ Sym3.M)
    (hbnd1 : home + dq < tp.length) (hmL : m < L) (hd : 1 ≤ d') (hbnd : home + 1 + d' + m < tp.length)
    (hco : ∀ i, i < m → tp.getD (home + 1 + d' + i) Sym3.O = Sym3.I)
    (hcs : tp.getD (home + 1 + d' + m) Sym3.O = Sym3.O) :
    ∃ N, reachIn (toNTM3 (transferFieldLeft3 s found cont mid d' sDone L)) N (s, home + dq, tp)
      (sDone, home + 1 + d' + m, copyBlockLeft tp (home + 1 + d') d' m) := by
  obtain ⟨N1, hnav⟩ := navigateToSource3_run s found cont mid d' home dq tp hmark hno hbnd1 (by omega)
  obtain ⟨N2, hcopy⟩ := copyFieldLeft3_run sDone d' L (mid + d') (home + 1 + d') m tp hmL hd (by omega) hbnd hco hcs
  exact ⟨N1 + N2, reachIn_seq3 (navigateToSource3 s found cont mid d') (copyFieldLeft3 (mid + d') sDone d' L)
    N1 N2 _ _ _ hnav hcopy⟩

/-!
**The full field transfer, proved.**  `transferFieldLeft3` brings a unary field from the matched rule into the
configuration — navigate to the data-dependent rule source, then copy leftward — composing proven parts with no
counter-driven walk.  Next: clear the old config field before the copy, assemble the full state update, and connect to
`EmitsEncodedStep3` — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Transfer

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Transfer.transferFieldLeft3_run
