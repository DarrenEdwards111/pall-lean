import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Seek

/-!
# Entry 485 — generic scan loop: return to the config start `gotoConfigStart` (proved)

The symbol compare (and general re-positioning) needs to return the head to the **config field start**.  On the stitched
tape the home marker `M` sits at cell `0` and the config field begins at cell `1`, so a fixed machine reaches the config
start from anywhere to its right by seeking left to the home marker (`seekMarkLeft`, entry 387) and stepping once right.
The config + rule region is marker-free (entry 463), so the seek lands on the home marker.

`gotoConfigStart s mid found cont := seekMarkLeft s mid cont ++ moveRight3 mid found`.

## What is proved (clean axioms, no `sorry`)

* **`gotoConfigStart s mid found cont`** — the return-to-config-start machine.
* **`gotoConfigStart_run`** (PROVED) — home marker at `0`, cells `1 … p` marker-free, in bounds: `∃ N, reachIn N (s, p, tp)
  (found, 1, tp)`, tape identical.

## Honest scope

This is **navigation back to the config start** (glue for the symbol compare).  It does **not** build the symbol compare,
the match-or-advance wiring, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those fragment by fragment
is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3GotoConfig

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Seek (seekMarkLeft seekMarkLeft_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **Return to the config field start.**  Seek left to the home marker, then step right onto cell `1`. -/
def gotoConfigStart (s mid found cont : ℕ) : TMachine3 :=
  seekMarkLeft s mid cont ++ moveRight3 mid found

/-- **The return-to-config-start reaches cell `1` (PROVED).** -/
theorem gotoConfigStart_run (s mid found cont p : ℕ) (tp : List Sym3)
    (hmark : tp.getD 0 Sym3.O = Sym3.M) (hclean : ∀ k, 0 < k → k ≤ p → tp.getD k Sym3.O ≠ Sym3.M)
    (hp : p < tp.length) :
    ∃ N, reachIn (toNTM3 (gotoConfigStart s mid found cont)) N (s, p, tp) (found, 1, tp) := by
  obtain ⟨N1, hsk⟩ := seekMarkLeft_run s mid cont 0 tp hmark p
    (fun k hk0 hkp => by simpa using hclean k hk0 hkp) (by omega)
  rw [show (0 : ℕ) + p = p from by omega] at hsk
  have hmr := moveRight3_run_eq mid found 0 tp (by omega)
  exact ⟨N1 + 1, reachIn_seq3 (seekMarkLeft s mid cont) (moveRight3 mid found) N1 1 _ _ _ hsk hmr⟩

/-!
**Return to the config start, proved.**  `gotoConfigStart` repositions the head at the config field start via the home
anchor — the navigation glue for the symbol compare.  Next: read the config symbol there and verdict against the
record symbol (both via existing primitives), then wire the full record comparison into the scan loop — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3GotoConfig

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3GotoConfig.gotoConfigStart_run
