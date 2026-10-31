import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3SeekR

/-!
# Entry 473 — generic scan loop: inter-cursor shuttle `crossRight` / `crossLeft` (proved)

The comparison shuttle (per the fixed-`U` finding, entry 467) keeps two cursors — a marker `M` in the config field and one
in the record field — and the head moves between them.  Since each cursor advance (`markAdvance3`, entry 472) leaves the head
*on* its cursor, crossing to the partner cursor means: step **off** the current cursor (one move), then **seek** to the
partner marker.  This brick is exactly that composite, in both directions.

`crossRight s mid found cont := moveRight3 s mid ++ seekMarkRight mid found cont` and the leftward mirror.

## What is proved (clean axioms, no `sorry`)

* **`crossRight s mid found cont`** / **`crossLeft s mid found cont`** — the shuttle machines.
* **`crossRight_run`** (PROVED) — from a cursor at `p`, with the partner marker at `p+1+d` and the cells `p+1 … p+d`
  marker-free: `∃ N, reachIn N (s, p, tp) (found, p+1+d, tp)`, tape identical.
* **`crossLeft_run`** (PROVED) — from a cursor at `q+d+1`, with the partner marker at `q` and the cells `q+1 … q+d`
  marker-free: `∃ N, reachIn N (s, q+d+1, tp) (found, q, tp)`, tape identical.

## Honest scope

This is the **inter-cursor shuttle** of the comparison.  It does **not** yet build the two-field comparison loop, the
match-or-advance branch, the generic apply, nor a fixed `U` / `EmitsEncodedStepEx3`.  Building those fragment by fragment is
the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Cross

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Mark (moveLeft3 moveLeft3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Seek (seekMarkLeft seekMarkLeft_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3SeekR (seekMarkRight seekMarkRight_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_seq3)

/-- **The rightward inter-cursor shuttle.**  Step off the current cursor, then seek right to the partner marker. -/
def crossRight (s mid found cont : ℕ) : TMachine3 :=
  moveRight3 s mid ++ seekMarkRight mid found cont

/-- **The leftward inter-cursor shuttle.**  Step off the current cursor, then seek left to the partner marker. -/
def crossLeft (s mid found cont : ℕ) : TMachine3 :=
  moveLeft3 s mid ++ seekMarkLeft mid found cont

/-- **The rightward shuttle reaches the partner (PROVED).** -/
theorem crossRight_run (s mid found cont p d : ℕ) (tp : List Sym3)
    (hp : p < tp.length) (hM : tp.getD (p + 1 + d) Sym3.O = Sym3.M)
    (hclear : ∀ k, k < d → tp.getD (p + 1 + k) Sym3.O ≠ Sym3.M) (hbound : p + 1 + d < tp.length) :
    ∃ N, reachIn (toNTM3 (crossRight s mid found cont)) N (s, p, tp) (found, p + 1 + d, tp) := by
  have h1 := moveRight3_run_eq s mid p tp hp
  obtain ⟨N2, h2⟩ := seekMarkRight_run mid found cont tp d (p + 1) hM hclear hbound
  exact ⟨1 + N2, reachIn_seq3 (moveRight3 s mid) (seekMarkRight mid found cont) 1 N2 _ _ _ h1 h2⟩

/-- **The leftward shuttle reaches the partner (PROVED).** -/
theorem crossLeft_run (s mid found cont q d : ℕ) (tp : List Sym3)
    (hM : tp.getD q Sym3.O = Sym3.M) (hclear : ∀ k, 0 < k → k ≤ d → tp.getD (q + k) Sym3.O ≠ Sym3.M)
    (hbound : q + d + 1 < tp.length) :
    ∃ N, reachIn (toNTM3 (crossLeft s mid found cont)) N (s, q + d + 1, tp) (found, q, tp) := by
  have h1 := moveLeft3_run_eq s mid (q + d + 1) tp (by omega)
  rw [show q + d + 1 - 1 = q + d from by omega] at h1
  obtain ⟨N2, h2⟩ := seekMarkLeft_run mid found cont q tp hM d hclear (by omega)
  exact ⟨1 + N2, reachIn_seq3 (moveLeft3 s mid) (seekMarkLeft mid found cont) 1 N2 _ _ _ h1 h2⟩

/-!
**The inter-cursor shuttle, proved.**  `crossRight`/`crossLeft` move the head from one cursor to its partner across the
marker-free gap, in both directions — the head-transport of the comparison shuttle.  Next: chain `markAdvance3` and these
shuttles into the two-field comparison loop, then the match-or-advance branch and the generic apply — fragment by verified
fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Cross

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Cross.crossRight_run
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Cross.crossLeft_run
