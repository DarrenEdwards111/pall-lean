import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3FieldStep
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UniversalTM3Move

/-!
# Entry 406 — universal-TM-table build: the full unary field compare `fieldCompare3` (proved)

`fieldStep3` (entry 405) decides *one* cell-pair of a field compare — continue / match / fail.  This brick loops it over a
whole unary key field: it compares the config-key field (a unary nat `a`, starting at `c`) against the rule-key field (a
unary nat `b`, starting at `c+d`, the same distance `d` away cell by cell) and routes to `sMatch` iff `a = b`.

The construction is a **corridor** unrolled `L` times, `L` a static budget on the field length (the rule keys of a fixed
encoded machine have bounded length).  Each iteration is `fieldStep3` followed by a single `moveRight3` that advances the
head from cell `c+t` to `c+t+1` on the *continue* (`sCont`) path; the rule pointer tracks automatically because the
inter-field distance `d` is constant.  The run is proved by induction on the budget `L`: the recursion reduces
`(a,b) → (a-1, b-1)` (both fields still have a one) and terminates the moment either field reaches its `O` separator.  In
every case the comparison terminates after `min a b + 1` cell-pairs, so the head ends at `c + min a b`, with the tape
restored throughout (each `fieldStep3` lays and clears its own marker).

## What is proved (clean axioms, no `sorry`)

* **`fieldCompare3 s sMatch sFail d`** — `0 ↦ []`, `L+1 ↦ fieldStep3 s (s+2d+15) sMatch sFail d ++ moveRight3 (s+2d+15)
  (s+2d+16) ++ fieldCompare3 (s+2d+16) sMatch sFail d L` (continue target = the advance state, then the next iteration).
* **`fieldCompare3_run`** (PROVED) — with no marker anywhere on `tp`, `d ≥ 1`, `c+a+d < tp.length`, a budget `min a b <
  L`, and the two fields' content (`a` ones then `O` at `c`; `b` ones then `O` at `c+d`): `∃ N, reachIn (toNTM3
  (fieldCompare3 …)) N (s, c, tp) ((if a = b then sMatch else sFail), c + min a b, tp)` — routes to `sMatch` iff the two
  unary fields are equal, head at `c + min a b`, tape restored.

## Honest scope

This is the **whole key-field compare** — the genuine field loop, isolated as a clean theorem.  With it, the rule-table
match loop becomes ordinary scanner/control engineering (scan to each record's key, `fieldCompare3` it against the config
key, jump on fail / enter apply on match).  It does **not** yet build that table loop, nor the apply, nor
`EmitsEncodedStep3`.  Building those fragment by fragment is the genuine remaining construction, **not faked**.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldCompare

open PallLean.Paper93.DeepMath.PathB.ACC0NTM (reachIn)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Sym (Sym3 TMachine3 toNTM3)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldStep (fieldStep3 fieldStep3_run)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Move (moveRight3 moveRight3_run_eq)
open PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3Compose (reachIn_append_left3 reachIn_seq3)

/-- **The unary field-compare loop.**  Each iteration: one `fieldStep3` cell-pair (continue ↦ the advance state), a
`moveRight3` to the next config cell, then recurse with one less budget. -/
def fieldCompare3 (s sMatch sFail d : ℕ) : ℕ → TMachine3
  | 0 => []
  | (L + 1) =>
      fieldStep3 s (s + 2 * d + 15) sMatch sFail d
        ++ moveRight3 (s + 2 * d + 15) (s + 2 * d + 16)
        ++ fieldCompare3 (s + 2 * d + 16) sMatch sFail d L

/-- **The unary field-compare run (PROVED).**  Routes to `sMatch` iff the two unary fields are equal (`a = b`); the head
ends at `c + min a b` and the tape is restored. -/
theorem fieldCompare3_run (sMatch sFail d : ℕ) (tp : List Sym3) (hd : 1 ≤ d)
    (hM : ∀ j, tp.getD j Sym3.O ≠ Sym3.M) :
    ∀ (L s c a b : ℕ), min a b < L → c + a + d < tp.length →
      (∀ i, i < a → tp.getD (c + i) Sym3.O = Sym3.I) → tp.getD (c + a) Sym3.O = Sym3.O →
      (∀ i, i < b → tp.getD (c + d + i) Sym3.O = Sym3.I) → tp.getD (c + d + b) Sym3.O = Sym3.O →
      ∃ N, reachIn (toNTM3 (fieldCompare3 s sMatch sFail d L)) N (s, c, tp)
        ((if a = b then sMatch else sFail), c + min a b, tp) := by
  intro L
  induction L with
  | zero => intro s c a b hL _ _ _ _ _; exact absurd hL (Nat.not_lt_zero _)
  | succ L ih =>
    intro s c a b hL hbnd hco hcs hro hrs
    -- bounds shared by every branch
    have hp : c < tp.length := by omega
    have hbound : c + d < tp.length := by omega
    have hno : ∀ k, 0 < k → k ≤ d → tp.getD (c + k) Sym3.O ≠ Sym3.M := fun k _ _ => hM (c + k)
    have hbit : tp.getD c Sym3.O = Sym3.O ∨ tp.getD c Sym3.O = Sym3.I := by
      rcases Nat.eq_zero_or_pos a with ha | ha
      · left; have := hcs; rw [ha, Nat.add_zero] at this; exact this
      · right; have := hco 0 ha; rwa [Nat.add_zero] at this
    obtain ⟨N1, hFS⟩ := fieldStep3_run s (s + 2 * d + 15) sMatch sFail c d tp hbit hd hno hp hbound
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · -- a = 0, b = 0: both fields empty ⇒ match
        have hc0 : tp.getD c Sym3.O = Sym3.O := by simpa using hcs
        have hd0 : tp.getD (c + d) Sym3.O = Sym3.O := by simpa using hrs
        rw [hc0, if_pos rfl, hd0, if_pos rfl] at hFS
        have h1 := reachIn_append_left3 (fieldStep3 s (s + 2 * d + 15) sMatch sFail d)
          (moveRight3 (s + 2 * d + 15) (s + 2 * d + 16)) N1 _ _ hFS
        have h2 := reachIn_append_left3 _ (fieldCompare3 (s + 2 * d + 16) sMatch sFail d L) N1 _ _ h1
        rw [if_pos rfl, show c + min 0 0 = c from by omega]
        exact ⟨N1, h2⟩
      · -- a = 0, b > 0: config field shorter ⇒ fail
        have hc0 : tp.getD c Sym3.O = Sym3.O := by simpa using hcs
        have hdI : tp.getD (c + d) Sym3.O = Sym3.I := by have := hro 0 hbpos; rwa [Nat.add_zero] at this
        rw [hc0, if_pos rfl, hdI, if_neg (by decide : ¬ (Sym3.I = Sym3.O))] at hFS
        have h1 := reachIn_append_left3 (fieldStep3 s (s + 2 * d + 15) sMatch sFail d)
          (moveRight3 (s + 2 * d + 15) (s + 2 * d + 16)) N1 _ _ hFS
        have h2 := reachIn_append_left3 _ (fieldCompare3 (s + 2 * d + 16) sMatch sFail d L) N1 _ _ h1
        rw [if_neg (show ¬ ((0 : ℕ) = b) from by omega), show c + min 0 b = c from by omega]
        exact ⟨N1, h2⟩
    · rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · -- a > 0, b = 0: rule field shorter ⇒ fail
        have hcI : tp.getD c Sym3.O = Sym3.I := by have := hco 0 hapos; rwa [Nat.add_zero] at this
        have hd0 : tp.getD (c + d) Sym3.O = Sym3.O := by simpa using hrs
        rw [hcI, if_neg (by decide : ¬ (Sym3.I = Sym3.O)), hd0,
          if_neg (by decide : ¬ (Sym3.O = Sym3.I))] at hFS
        have h1 := reachIn_append_left3 (fieldStep3 s (s + 2 * d + 15) sMatch sFail d)
          (moveRight3 (s + 2 * d + 15) (s + 2 * d + 16)) N1 _ _ hFS
        have h2 := reachIn_append_left3 _ (fieldCompare3 (s + 2 * d + 16) sMatch sFail d L) N1 _ _ h1
        rw [if_neg (show ¬ (a = 0) from by omega), show c + min a 0 = c from by omega]
        exact ⟨N1, h2⟩
      · -- a > 0, b > 0: both fields continue ⇒ advance and recurse
        have hcI : tp.getD c Sym3.O = Sym3.I := by have := hco 0 hapos; rwa [Nat.add_zero] at this
        have hdI : tp.getD (c + d) Sym3.O = Sym3.I := by have := hro 0 hbpos; rwa [Nat.add_zero] at this
        rw [hcI, if_neg (by decide : ¬ (Sym3.I = Sym3.O)), hdI, if_pos rfl] at hFS
        have hMR := moveRight3_run_eq (s + 2 * d + 15) (s + 2 * d + 16) c tp hp
        obtain ⟨N2, hREC⟩ := ih (s + 2 * d + 16) (c + 1) (a - 1) (b - 1)
          (by omega) (by omega)
          (fun i hi => by rw [show c + 1 + i = c + (i + 1) from by omega]; exact hco (i + 1) (by omega))
          (by rw [show c + 1 + (a - 1) = c + a from by omega]; exact hcs)
          (fun i hi => by rw [show c + 1 + d + i = c + d + (i + 1) from by omega]; exact hro (i + 1) (by omega))
          (by rw [show c + 1 + d + (b - 1) = c + d + b from by omega]; exact hrs)
        simp only [show (a - 1 = b - 1) ↔ (a = b) from by omega] at hREC
        rw [show c + 1 + min (a - 1) (b - 1) = c + min a b from by omega] at hREC
        have seqFM := reachIn_seq3 (fieldStep3 s (s + 2 * d + 15) sMatch sFail d)
          (moveRight3 (s + 2 * d + 15) (s + 2 * d + 16)) N1 1 _ _ _ hFS hMR
        have seqAll := reachIn_seq3 _ (fieldCompare3 (s + 2 * d + 16) sMatch sFail d L)
          (N1 + 1) N2 _ _ _ seqFM hREC
        exact ⟨N1 + 1 + N2, seqAll⟩

/-!
**The unary field compare, proved.**  `fieldCompare3` loops `fieldStep3` over a whole key field, routing to `sMatch` iff
the two unary fields are equal, with the head ending at `c + min a b` and the tape restored.  Next: the rule-table match
loop — scan to each record's key, `fieldCompare3` it against the config key, jump on fail / enter apply on match —
fragment by verified fragment, not faked.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldCompare

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UniversalTM3FieldCompare.fieldCompare3_run
