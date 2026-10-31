import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MatchTable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3EncTrans
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTMBitLookup

/-!
# Entry 455 — universal-TM-table build: the matcher ↔ lookup correspondence `recMatch_iff_lookup` (proved)

The crux bridge between the concrete rule-table matcher (`matchTable3`, entry 410) and the abstract bit-level lookup
(`bitLookup`, already proven equal to `lookup`).  The matcher's match-existence hypothesis is `∃ rec ∈ recs, RecMatch a cs
rec`, where `RecMatch a cs (d,b,rs) := a = b ∧ rs = cs` (the record's state length and read symbol equal the config's).
The abstract lookup matches a rule `r` when `r.1 = (c.1, readSym c)` (its source state and read symbol equal the config's).

These are the **same condition**: encoding each rule `r` of `M` as a descriptor `(1, r.1.1, boolToSym3 r.1.2)`, a descriptor
matches (in the `RecMatch` sense) iff the rule matches (in the `lookup` sense) — because `boolToSym3` is injective and a
config's state `c.1` plays the role of the unary state length `a`, its symbol `boolToSym3 (readSym c)` the role of `cs`.

This connects the matcher's hypothesis to lookup/`bitLookup` success at the **condition** level (the heart of the
correspondence); it is independent of the tape layout and of the per-step cost.

## What is proved (clean axioms, no `sorry`)

* **`recsOf M c`** — the descriptor list `M.map (fun r => (1, r.1.1, boolToSym3 r.1.2))`.
* **`boolToSym3_inj`** (PROVED) — `boolToSym3` is injective.
* **`recMatch_iff_lookup`** (PROVED) — `(∃ rec ∈ recsOf M c, RecMatch c.1 (boolToSym3 (readSym c)) rec) ↔ (lookup M
  c).isSome`.
* **`recMatch_iff_bitLookup`** (PROVED) — the same with `bitLookup (encodeMachineBits M) c` (via `bitLookup =
  lookup`).

## Honest scope

This is the **condition-level** matcher↔lookup correspondence — the match conditions coincide.  It does **not** assemble
the full layout `φ` / run-level correspondence (which also carries the **fixed-`cost` obstruction** of `EmitsEncodedStep3`).
Building the rest fragment by fragment is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰`
or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatcherLookup

open PallLean.Paper93.DeepMath.PathB.ACC0ConcreteNTM (TMachine TMTrans CConfig readSym)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMLookup (lookup)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMBitLookup (bitLookup bitLookup_encodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTMScannable (encodeMachineBits)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable (RecMatch)

/-- The matcher's record descriptors derived from a machine `M`: each rule `r` becomes `(1, r.1.1, boolToSym3 r.1.2)`
(dummy distance, source-state length, read symbol). -/
def recsOf (M : TMachine) (_c : CConfig) : List (ℕ × ℕ × Sym3) :=
  M.map (fun r => (1, r.1.1, boolToSym3 r.1.2))

/-- **`boolToSym3` is injective (PROVED).** -/
theorem boolToSym3_inj {a b : Bool} (h : boolToSym3 a = boolToSym3 b) : a = b := by
  cases a <;> cases b <;> simp_all [boolToSym3]

/-- **The matcher ↔ lookup correspondence (PROVED).**  A descriptor matches (`RecMatch`) iff the abstract lookup finds a
rule. -/
theorem recMatch_iff_lookup (M : TMachine) (c : CConfig) :
    (∃ rec ∈ recsOf M c, RecMatch c.1 (boolToSym3 (readSym c)) rec) ↔ (lookup M c).isSome := by
  rw [show (lookup M c).isSome ↔ ∃ r ∈ M, r.1 = (c.1, readSym c) from by
    unfold lookup
    rw [List.find?_isSome]
    constructor
    · rintro ⟨r, hr, hp⟩; exact ⟨r, hr, of_decide_eq_true hp⟩
    · rintro ⟨r, hr, hp⟩; exact ⟨r, hr, decide_eq_true_eq.mpr hp⟩]
  unfold recsOf
  constructor
  · rintro ⟨rec, hmem, ha, hb⟩
    rw [List.mem_map] at hmem
    obtain ⟨r, hrM, rfl⟩ := hmem
    refine ⟨r, hrM, ?_⟩
    have hbb : r.1.2 = readSym c := boolToSym3_inj hb
    rw [show r.1 = (r.1.1, r.1.2) from rfl, ha.symm, hbb]
  · rintro ⟨r, hrM, hp⟩
    refine ⟨(1, r.1.1, boolToSym3 r.1.2), List.mem_map.mpr ⟨r, hrM, rfl⟩, ?_, ?_⟩
    · show c.1 = r.1.1
      rw [hp]
    · show boolToSym3 r.1.2 = boolToSym3 (readSym c)
      rw [hp]

/-- **The matcher ↔ bitLookup correspondence (PROVED).**  Connects the matcher's match-existence hypothesis to the
bit-level lookup on the encoded table. -/
theorem recMatch_iff_bitLookup (M : TMachine) (c : CConfig) :
    (∃ rec ∈ recsOf M c, RecMatch c.1 (boolToSym3 (readSym c)) rec) ↔ (bitLookup (encodeMachineBits M) c).isSome := by
  rw [recMatch_iff_lookup, bitLookup_encodeMachineBits]

/-!
**The matcher ↔ lookup correspondence, proved.**  The concrete matcher's `RecMatch` condition coincides with the abstract
`lookup`/`bitLookup` success — the heart of the universal-simulation correspondence, at the condition level.  Combined with
`matchTable3_run` (entry 410), a rule existing in the encoded table implies the matcher reaches the match-found state.  Next:
the full layout `φ` / run-level correspondence (subject to the fixed-`cost` obstruction of `EmitsEncodedStep3`) — fragment
by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatcherLookup

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatcherLookup.recMatch_iff_lookup
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatcherLookup.recMatch_iff_bitLookup
