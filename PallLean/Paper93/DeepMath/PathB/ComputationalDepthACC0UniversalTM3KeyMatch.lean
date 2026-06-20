import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3FieldCompare

/-!
# Entry 407 — universal-TM-table build: the single-record key matcher `recordKeyMatch3` (proved)

A transition record is `encodeTransBits3 t = encodeNatBits3 state ++ boolToSym3 read :: (RHS)` (entry 393), so the *key*
that decides whether the rule fires is its first two fields: a **unary state field** followed by a single **symbol
(read-bit) cell**.  The configuration carries the same shape — current state (unary) then current symbol cell.  This
brick decides, from the record's start, whether the rule key matches the configuration key: it routes to `recMatch` iff
**both** the state fields are equal *and* the symbol cells agree.

The construction composes the two comparison primitives already built:

* `fieldCompare3` (entry 406) on the two **state** fields (config at `c`, rule at `c+d`).  On mismatch it routes
  straight to `recFail`; on match it lands at the config state separator `c+a` and falls through to the symbol compare.
* a single `moveRight3` advancing the head from the separator `c+a` onto the config **symbol** cell `c+a+1`.
* `bitCompareAtDist3` (entry 404) on the two symbol cells.  *Crucially*, once the state fields are equal (`a = b`) the
  two symbol cells sit at the **same** distance `d` apart (config at `c+a+1`, rule at `c+d+b+1 = (c+a+1)+d`), so the
  single-bit compare reuses the very same `d`.  It routes to `recMatch` iff the symbols agree, else `recFail`.

## What is proved (clean axioms, no `sorry`)

* **`recordKeyMatch3 base recMatch recFail d L`** — `fieldCompare3 base M₀ recFail d L ++ moveRight3 M₀ (M₀+1) ++
  bitCompareAtDist3 (M₀+1) recMatch recFail d`, where `M₀ = base + L*(2d+16)` is the first state past the field-compare
  corridor.
* **`recordKeyMatch3_run`** (PROVED) — with no marker anywhere on `tp`, `d ≥ 1`, the budget `min a b < L`, the bound
  `c+a+1+d < tp.length`, the two state fields' content (`a` ones then `O` at `c`; `b` ones then `O` at `c+d`) and the two
  symbol cells (`cs` at `c+a+1`, `rs` at `c+d+b+1`, both in `{O,I}`): `∃ N q, reachIn (toNTM3 (recordKeyMatch3 …)) N
  (base, c, tp) ((if a = b ∧ rs = cs then recMatch else recFail), q, tp)` — routes to `recMatch` iff the two keys match,
  tape restored.

## Honest scope

This is the **per-record key matcher** — the decision "does *this* rule fire?", composed from the field loop and the
single-bit compare.  It does **not** yet loop over the whole rule table (scan to the next record on `recFail`), nor apply
the matched rule.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatch

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldCompare (fieldCompare3 fieldCompare3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3BitCompare (bitCompareAtDist3 bitCompareAtDist3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_seq3)

/-- **The single-record key matcher.**  Compare the state fields (`fieldCompare3`), advance onto the symbol cell, then
compare the symbol cells (`bitCompareAtDist3`); route to `recMatch` iff both agree.  `M₀ = base + L*(2d+16)` is the first
state past the field-compare corridor. -/
def recordKeyMatch3 (base recMatch recFail d L : ℕ) : TMachine3 :=
  fieldCompare3 base (base + L * (2 * d + 16)) recFail d L
    ++ moveRight3 (base + L * (2 * d + 16)) (base + L * (2 * d + 16) + 1)
    ++ bitCompareAtDist3 (base + L * (2 * d + 16) + 1) recMatch recFail d

/-- **The single-record key matcher run (PROVED).**  Routes to `recMatch` iff the state fields are equal (`a = b`) and
the symbol cells agree (`rs = cs`); tape restored. -/
theorem recordKeyMatch3_run (base recMatch recFail d : ℕ) (tp : List Sym3) (hd : 1 ≤ d)
    (hM : ∀ j, tp.getD j Sym3.O ≠ Sym3.M)
    (L c a b : ℕ) (cs rs : Sym3) (hcs : cs = Sym3.O ∨ cs = Sym3.I)
    (hL : min a b < L) (hbnd : c + a + 1 + d < tp.length)
    (hco : ∀ i, i < a → tp.getD (c + i) Sym3.O = Sym3.I) (hcsep : tp.getD (c + a) Sym3.O = Sym3.O)
    (hro : ∀ i, i < b → tp.getD (c + d + i) Sym3.O = Sym3.I) (hrsep : tp.getD (c + d + b) Sym3.O = Sym3.O)
    (hcsym : tp.getD (c + a + 1) Sym3.O = cs) (hrsym : tp.getD (c + d + b + 1) Sym3.O = rs) :
    ∃ N q, reachIn (toNTM3 (recordKeyMatch3 base recMatch recFail d L)) N (base, c, tp)
      ((if a = b ∧ rs = cs then recMatch else recFail), q, tp) := by
  -- compare the two state fields first
  obtain ⟨N1, hFCraw⟩ := fieldCompare3_run (base + L * (2 * d + 16)) recFail d tp hd hM L base c a b
    hL (by omega) hco hcsep hro hrsep
  by_cases hab : a = b
  · -- state fields equal: advance onto the symbol cell and compare the symbol cells
    rw [if_pos hab, show c + min a b = c + a from by omega] at hFCraw
    -- advance from the separator c+a onto the config symbol cell c+a+1
    have hMR := moveRight3_run_eq (base + L * (2 * d + 16)) (base + L * (2 * d + 16) + 1) (c + a) tp (by omega)
    -- the single-bit compare on the two symbol cells, at the same distance d
    have hbit' : tp.getD (c + a + 1) Sym3.O = Sym3.O ∨ tp.getD (c + a + 1) Sym3.O = Sym3.I := by
      rw [hcsym]; exact hcs
    have hno' : ∀ k, 0 < k → k ≤ d → tp.getD (c + a + 1 + k) Sym3.O ≠ Sym3.M := fun k _ _ => hM (c + a + 1 + k)
    obtain ⟨N3, hBC⟩ := bitCompareAtDist3_run (base + L * (2 * d + 16) + 1) recMatch recFail (c + a + 1) d tp
      hbit' hd hno' (by omega) (by omega)
    have hRsym' : tp.getD (c + a + 1 + d) Sym3.O = rs := by
      rw [show c + a + 1 + d = c + d + b + 1 from by omega]; exact hrsym
    simp only [hcsym, hRsym'] at hBC
    -- chain the three pieces
    have seq1 := reachIn_seq3 (fieldCompare3 base (base + L * (2 * d + 16)) recFail d L)
      (moveRight3 (base + L * (2 * d + 16)) (base + L * (2 * d + 16) + 1)) N1 1 _ _ _ hFCraw hMR
    have seq2 := reachIn_seq3 _ (bitCompareAtDist3 (base + L * (2 * d + 16) + 1) recMatch recFail d)
      (N1 + 1) N3 _ _ _ seq1 hBC
    simp only [show (a = b ∧ rs = cs) ↔ (rs = cs) from by simp [hab]]
    exact ⟨N1 + 1 + N3, c + a + 1, seq2⟩
  · -- state fields differ: route straight to recFail
    rw [if_neg hab] at hFCraw
    have h1 := reachIn_append_left3 (fieldCompare3 base (base + L * (2 * d + 16)) recFail d L)
      (moveRight3 (base + L * (2 * d + 16)) (base + L * (2 * d + 16) + 1)) N1 _ _ hFCraw
    have h2 := reachIn_append_left3 _ (bitCompareAtDist3 (base + L * (2 * d + 16) + 1) recMatch recFail d) N1 _ _ h1
    rw [if_neg (show ¬ (a = b ∧ rs = cs) from fun h => hab h.1)]
    exact ⟨N1, c + min a b, h2⟩

/-!
**The single-record key matcher, proved.**  `recordKeyMatch3` decides whether one encoded rule fires on the current
configuration — state field compare (`fieldCompare3`) then symbol cell compare (`bitCompareAtDist3`), at the same
distance `d`, routing to `recMatch` iff both keys agree, tape restored.  Next: the rule-table match loop — on `recFail`
scan to the next record and re-run this matcher; on `recMatch` enter the apply phase — fragment by verified fragment, not
faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatch

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatch.recordKeyMatch3_run
