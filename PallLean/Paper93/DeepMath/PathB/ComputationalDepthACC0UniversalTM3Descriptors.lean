import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3MatchTable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3EncTrans

/-!
# Entry 467 — universal-TM-table build: the descriptor list `descriptorsOf` / `descriptorsOf_match` (proved)

The matcher's record descriptors for a rule-key list, with cumulative offsets (each record's distance is the prior records'
total length).  This brick proves the **match-existence ↔ rule-keys** bridge: a descriptor matches the config key
(`RecMatch`) iff some rule key matches `(a, csBool)` — the offset is irrelevant to `RecMatch`, so this is clean.  Combined
with entry 455, the matcher's match condition coincides with `lookup`/`bitLookup` on the descriptor model.

## Important honest finding (the fixed-`U` gap)

`matchTable3` (entry 410) is defined by **recursion over the record list**, concatenating one transition block per record —
so its machine *size grows with the number of rules*.  Hence `matchTable3` (and any `U` built from it) is a
**per-machine-compiled** matcher, **not a fixed universal machine**.  `EmitsEncodedStep(Ex)3` requires a *single fixed* `U`
for all `Mbits`.  A true fixed `U` therefore needs a **generic tape-driven scan loop** (a fixed-size machine that reads each
record from the tape and loops), which is a separate construction not built in this arc.  This is a genuine architectural
limitation, surfaced here — **not faked over**.

## What is proved (clean axioms, no `sorry`)

* **`descriptorsOf a rules`** — the descriptor list with cumulative offsets.
* **`descriptorsOf_match`** (PROVED) — `(∃ rec ∈ descriptorsOf a rules, RecMatch a (boolToSym3 csBool) rec) ↔ (∃ p ∈ rules,
  a = p.1 ∧ p.2 = csBool)`.

## Honest scope

This is the descriptor **match-existence** bridge for the (non-fixed) unrolled matcher model.  It does **not** give a fixed
`U` (see the finding above), nor prove the per-descriptor `RecOK` at the cumulative offsets, nor `EmitsEncodedStepEx3`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Descriptors

open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3EncTrans (boolToSym3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable (RecMatch)

/-- `boolToSym3` is injective. -/
private theorem boolToSym3_inj {a b : Bool} (h : boolToSym3 a = boolToSym3 b) : a = b := by
  cases a <;> cases b <;> simp_all [boolToSym3]

/-- The descriptor list with an accumulating offset (each record's distance = the prior records' total length plus `a+2`). -/
def descriptorsAux (a : ℕ) : ℕ → List (ℕ × Bool) → List (ℕ × ℕ × Sym3)
  | _, [] => []
  | acc, (b, rs) :: rest => (a + 2 + acc, b, boolToSym3 rs) :: descriptorsAux a (acc + (b + 2)) rest

/-- The descriptor list for a rule-key list. -/
def descriptorsOf (a : ℕ) (rules : List (ℕ × Bool)) : List (ℕ × ℕ × Sym3) := descriptorsAux a 0 rules

/-- **Descriptor match-existence equals rule-key matching (auxiliary, PROVED).** -/
theorem descriptorsAux_match (a : ℕ) (csBool : Bool) : ∀ (acc : ℕ) (rules : List (ℕ × Bool)),
    (∃ rec ∈ descriptorsAux a acc rules, RecMatch a (boolToSym3 csBool) rec) ↔
      (∃ p ∈ rules, a = p.1 ∧ p.2 = csBool) := by
  intro acc rules
  induction rules generalizing acc with
  | nil => simp [descriptorsAux]
  | cons p rest ih =>
      obtain ⟨b, rs⟩ := p
      constructor
      · rintro ⟨rec, hmem, hM⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · obtain ⟨h1, h2⟩ := hM
          exact ⟨(b, rs), List.mem_cons_self, h1, boolToSym3_inj h2⟩
        · obtain ⟨q, hq, hqP⟩ := (ih (acc + (b + 2))).mp ⟨rec, hmem', hM⟩
          exact ⟨q, List.mem_cons_of_mem _ hq, hqP⟩
      · rintro ⟨q, hq, hq1, hq2⟩
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact ⟨(a + 2 + acc, b, boolToSym3 rs), List.mem_cons_self, hq1, by rw [show rs = csBool from hq2]⟩
        · obtain ⟨rec, hrec, hrecM⟩ := (ih (acc + (b + 2))).mpr ⟨q, hq', hq1, hq2⟩
          exact ⟨rec, List.mem_cons_of_mem _ hrec, hrecM⟩

/-- **Descriptor match-existence equals rule-key matching (PROVED).** -/
theorem descriptorsOf_match (a : ℕ) (csBool : Bool) (rules : List (ℕ × Bool)) :
    (∃ rec ∈ descriptorsOf a rules, RecMatch a (boolToSym3 csBool) rec) ↔
      (∃ p ∈ rules, a = p.1 ∧ p.2 = csBool) :=
  descriptorsAux_match a csBool 0 rules

/-!
**The descriptor match bridge, proved.**  A descriptor matches the config key iff a rule key matches `(a, csBool)`.
Honest finding: `matchTable3` is unrolled (size ∝ rule count), so it is **not** a fixed universal machine — a true `U`
needs a generic tape-driven scan loop, a separate construction.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Descriptors

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Descriptors.descriptorsOf_match
