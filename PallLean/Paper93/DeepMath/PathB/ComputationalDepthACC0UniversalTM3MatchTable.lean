import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3KeyMatchWin
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3ResetHome

/-!
# Entry 410 — universal-TM-table build: the rule-table match loop `matchTable3` (proved)

This assembles the whole rule-table search: walk the encoded transition list, and for each record decide whether its key
matches the configuration key (`recordKeyMatch3`, windowed — entry 409); on a mismatch, return the head to the config
home and try the next record (`resetToHome3` — entry 408); on a match, exit to the global `recMatch` (apply) state.  The
loop relies on a persistent *home* marker at `c-1` (tolerated by the windowed matcher) and the fact that each matcher
attempt leaves the head in the bounded config window `[c, c+a+1]`.

The records are modelled as a list of descriptors `(d, b, rs)` — the distance `d` from the config key `c` to the record's
state field, the record's state length `b`, and its read symbol cell `rs`.  `RecOK` bundles the layout/bound facts for one
record; `RecMatch` is the key-equality predicate (`a = b ∧ rs = cs`).

## What is proved (clean axioms, no `sorry`)

* **`matchTable3 recMatch L base recs`** — `[] ↦ []`; `(d,_,_)::rest ↦ recordKeyMatch3 base recMatch RF d L ++
  resetToHome3 RF (RF+1) (RF+2) nextBase ++ matchTable3 recMatch L nextBase rest`, with `RF = base + L*(2d+16) + 2d + 16`
  and `nextBase = RF + 3`.
* **`matchTable3_run`** (PROVED) — with a home marker at `c-1`, no marker elsewhere, the config key content, every record
  `RecOK`, and **some** record matching the config key (`∃ rec ∈ recs, RecMatch a cs rec`): `∃ N q, reachIn (toNTM3
  (matchTable3 …)) N (base, c, tp) (recMatch, q, tp)` — the loop reaches the match-found state.  Proved by induction on
  the record list: a head match exits immediately; a head mismatch fails, resets home, and recurses on the tail (which
  still contains the match).

## Honest scope

This is the **rule-table match loop** — the search that finds the applicable transition (in the non-deterministic `toNTM3`
model, the `∃`-direction: some applicable rule ⇒ the match-found state is reachable).  It does **not** yet prove the
exhaustion direction (no rule ⇒ a reject/halt state), nor *apply* the matched rule.  Building those fragment by fragment
is the genuine remaining construction, **not faked**.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatch (recordKeyMatch3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3KeyMatchWin (recordKeyMatch3_run_windowed)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3ResetHome (resetToHome3 resetToHome3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_seq3)

/-- **A record's key matches the configuration key.**  `rec = (d, b, rs)`: state lengths agree (`a = b`) and the read
symbols agree (`rs = cs`). -/
def RecMatch (a : ℕ) (cs : Sym3) (rec : ℕ × ℕ × Sym3) : Prop := a = rec.2.1 ∧ rec.2.2 = cs

/-- **Layout/bound facts for one record** `rec = (d, b, rs)` on the tape: distance `d ≥ 1`, budget, in-bounds, and the
record's state field (`b` ones then `O` at `c+d`) and symbol cell (`rs` at `c+d+b+1`). -/
def RecOK (tp : List Sym3) (c a L : ℕ) (rec : ℕ × ℕ × Sym3) : Prop :=
  1 ≤ rec.1 ∧ min a rec.2.1 < L ∧ c + a + 1 + rec.1 < tp.length ∧
    (∀ i, i < rec.2.1 → tp.getD (c + rec.1 + i) Sym3.O = Sym3.I) ∧
    tp.getD (c + rec.1 + rec.2.1) Sym3.O = Sym3.O ∧
    tp.getD (c + rec.1 + rec.2.1 + 1) Sym3.O = rec.2.2

/-- **The rule-table match loop.**  Per record: run the windowed matcher; on mismatch reset to the config home and
recurse; on match exit to `recMatch`.  `RF = base + L*(2d+16) + 2d + 16` is the matcher's fail state, `RF+3` the next
record's base. -/
def matchTable3 (recMatch L : ℕ) : ℕ → List (ℕ × ℕ × Sym3) → TMachine3
  | _, [] => []
  | base, (d, _, _) :: rest =>
      recordKeyMatch3 base recMatch (base + L * (2 * d + 16) + 2 * d + 16) d L
        ++ resetToHome3 (base + L * (2 * d + 16) + 2 * d + 16) (base + L * (2 * d + 16) + 2 * d + 17)
             (base + L * (2 * d + 16) + 2 * d + 18) (base + L * (2 * d + 16) + 2 * d + 19)
        ++ matchTable3 recMatch L (base + L * (2 * d + 16) + 2 * d + 19) rest

/-- **The rule-table match loop run (PROVED).**  If some record's key matches the configuration key, the loop reaches the
match-found state `recMatch`, the tape restored. -/
theorem matchTable3_run (recMatch L : ℕ) (tp : List Sym3) (c a : ℕ) (cs : Sym3)
    (hc : 1 ≤ c) (hcs : cs = Sym3.O ∨ cs = Sym3.I)
    (hmark : tp.getD (c - 1) Sym3.O = Sym3.M) (hclean : ∀ j, j ≠ c - 1 → tp.getD j Sym3.O ≠ Sym3.M)
    (hco : ∀ i, i < a → tp.getD (c + i) Sym3.O = Sym3.I) (hcsep : tp.getD (c + a) Sym3.O = Sym3.O)
    (hcsym : tp.getD (c + a + 1) Sym3.O = cs) :
    ∀ (recs : List (ℕ × ℕ × Sym3)) (base : ℕ),
      (∀ rec ∈ recs, RecOK tp c a L rec) → (∃ rec ∈ recs, RecMatch a cs rec) →
      ∃ N q, reachIn (toNTM3 (matchTable3 recMatch L base recs)) N (base, c, tp) (recMatch, q, tp) := by
  intro recs
  induction recs with
  | nil => intro base _ hEx; rcases hEx with ⟨x, hmem, -⟩; simp at hmem
  | cons rec rest ih =>
      intro base hOK hEx
      obtain ⟨d, b, rs⟩ := rec
      have hhead := (List.forall_mem_cons.mp hOK).1
      have hOKrest := (List.forall_mem_cons.mp hOK).2
      simp only [RecOK] at hhead
      obtain ⟨hd, hbudget, hbnd, hcoR, hcsepR, hcsymR⟩ := hhead
      obtain ⟨N1, q, hrun, hq1, hq2⟩ := recordKeyMatch3_run_windowed base recMatch
        (base + L * (2 * d + 16) + 2 * d + 16) d tp hd L c a b cs rs hcs hbudget hbnd
        (fun j hj1 _ => hclean j (by omega)) hco hcsep hcoR hcsepR hcsym hcsymR
      by_cases hmatch : a = b ∧ rs = cs
      · -- head record matches: exit to recMatch
        rw [if_pos hmatch] at hrun
        refine ⟨N1, q, ?_⟩
        have hl1 := reachIn_append_left3 _ (resetToHome3 (base + L * (2 * d + 16) + 2 * d + 16)
          (base + L * (2 * d + 16) + 2 * d + 17) (base + L * (2 * d + 16) + 2 * d + 18)
          (base + L * (2 * d + 16) + 2 * d + 19)) N1 _ _ hrun
        exact reachIn_append_left3 _ (matchTable3 recMatch L (base + L * (2 * d + 16) + 2 * d + 19) rest) N1 _ _ hl1
      · -- head record fails: reset to home and recurse on the tail
        rw [if_neg hmatch] at hrun
        obtain ⟨N2, hReset⟩ := resetToHome3_run (base + L * (2 * d + 16) + 2 * d + 16)
          (base + L * (2 * d + 16) + 2 * d + 17) (base + L * (2 * d + 16) + 2 * d + 18)
          (base + L * (2 * d + 16) + 2 * d + 19) (c - 1) (q - (c - 1)) tp hmark
          (fun k hk0 _ => hclean (c - 1 + k) (by omega)) (by omega)
        rw [show c - 1 + (q - (c - 1)) = q from by omega, show c - 1 + 1 = c from by omega] at hReset
        have hExrest : ∃ rec ∈ rest, RecMatch a cs rec := by
          rcases hEx with ⟨x, hxmem, hxP⟩
          rcases List.mem_cons.mp hxmem with rfl | hxtl
          · exact absurd hxP hmatch
          · exact ⟨x, hxtl, hxP⟩
        obtain ⟨N3, q3, hIH⟩ := ih (base + L * (2 * d + 16) + 2 * d + 19) hOKrest hExrest
        have sAB := reachIn_seq3 (recordKeyMatch3 base recMatch (base + L * (2 * d + 16) + 2 * d + 16) d L)
          (resetToHome3 (base + L * (2 * d + 16) + 2 * d + 16) (base + L * (2 * d + 16) + 2 * d + 17)
            (base + L * (2 * d + 16) + 2 * d + 18) (base + L * (2 * d + 16) + 2 * d + 19))
          N1 N2 _ _ _ hrun hReset
        have sABC := reachIn_seq3 _ (matchTable3 recMatch L (base + L * (2 * d + 16) + 2 * d + 19) rest)
          (N1 + N2) N3 _ _ _ sAB hIH
        exact ⟨N1 + N2 + N3, q3, sABC⟩

/-!
**The rule-table match loop, proved.**  `matchTable3` searches the encoded transition list and reaches the match-found
state whenever some record's key matches the configuration — the genuine rule lookup of the universal machine (in the
non-deterministic model).  Next: the apply phase (`apply3`) that copies the matched rule's RHS into the configuration, and
the exhaustion direction (no rule ⇒ halt) — fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3MatchTable.matchTable3_run
