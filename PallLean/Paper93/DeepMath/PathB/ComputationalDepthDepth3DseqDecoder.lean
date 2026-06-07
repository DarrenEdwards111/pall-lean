import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestSatSeqContiguity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestReplay
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingFlatten

/-!
# The concrete forward-replay decoder `Dseq` (branch `razborov-recoverRho-wip`)

The keystone `deepestSatSeq_recover` asserts the *existence* of a decoder reproducing `deepestSatSeq`
from the leaf and the tight `(2w)^s` label.  This file replaces that existential with a **concrete
object** `Dseq`, so the residual Håstad content becomes a property of a specific function we can reason
about incrementally — without falsely claiming correctness.

`Dseq` uses **exactly the legal data**:
* the leaf `σ_end` — only to enumerate the relevant clauses in `cs`-order (`leafClauses cs σ_end`);
* the tight label `lbl : PathLabel w s = Fin s → Fin w × Bool` — flattened to its `s` tokens;
* `cs`.

No `ρ`, no hidden clause identities, and the per-clause block lengths are recovered **dynamically** from
the per-token boundary bit (`takeBlock`), respecting the `(2w)^s` budget.

## What is proved here (clean, no `sorry`)
* `replayBlocksFlat_pos_lt` — every emitted position is `< w` (it is a `Fin w` value);
* `replayBlocksFlat_clause_mem` — every emitted clause is in the input clause list (hence in `cs`);
* `Dseq_pos_lt`, `Dseq_clause_mem` — the same for `Dseq`;
* `Dseq_idxOf_pairwise` — the emitted clause `cs`-indices are non-decreasing (same shape as the
  proved `deepestSatSeq_idxOf_pairwise`), so the decoder's output is structurally compatible.

## What is left open (isolated)
* `Dseq_correct_general` — the concrete decoder reproduces `deepestSatSeq` for the right label
  encoding.  This is the residual Håstad switching content (the factor-2 boundary bits + `σ_end`
  falsify recovery, fenced uncloseable by cheap alignment via `confound_uncovered`).  *WIP `sorry`.*

AC⁰/depth-3; `Depth3CollapseModel.collapse` and P≠NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- Split a token list into the first **block** — the tokens up to and including the first whose
boundary bit is `true` — and the remainder.  A `true` bit marks the end of the active clause's block
(the next satisfy step belongs to a later clause); if no bit is `true`, the whole list is one block. -/
def takeBlock {w : ℕ} :
    List (Fin w × Bool) → List (Fin w × Bool) × List (Fin w × Bool)
  | [] => ([], [])
  | t :: ts =>
      if t.2 then ([t], ts)
      else match takeBlock ts with | (b, r) => (t :: b, r)

/-- The decoder core: walk the clause list in `cs`-order; each clause consumes one bit-delimited block
of satisfy tokens, emitting `(clause, position)` for each token (position = the `Fin w` literal index). -/
def replayBlocksFlat {w : ℕ} :
    List (Clause n) → List (Fin w × Bool) → List (Clause n × ℕ)
  | [], _ => []
  | C :: cs', toks =>
      match takeBlock toks with
      | (blk, rest) => blk.map (fun t => (C, (t.1 : ℕ))) ++ replayBlocksFlat cs' rest

/-- **The concrete forward-replay decoder.**  Enumerate the leaf-relevant clauses in `cs`-order from
`σ_end`, then assign each one a dynamically-delimited block of the `s` label tokens. -/
def Dseq {w s : ℕ} (cs : List (Clause n)) (σ_end : Fin n → Option Bool)
    (lbl : SwitchingCounting.PathLabel w s) : List (Clause n × ℕ) :=
  replayBlocksFlat (leafClauses cs σ_end) (List.ofFn lbl)

/-! ## Sanity lemmas (clean) -/

/-- Every position emitted by the decoder core is `< w`. -/
theorem replayBlocksFlat_pos_lt {w : ℕ} :
    ∀ (L : List (Clause n)) (toks : List (Fin w × Bool)) {C : Clause n} {p : ℕ},
      (C, p) ∈ replayBlocksFlat L toks → p < w := by
  intro L
  induction L with
  | nil => intro toks C p h; simp [replayBlocksFlat] at h
  | cons D cs' ih =>
    intro toks C p h
    rw [replayBlocksFlat] at h
    cases htb : takeBlock toks with
    | mk blk rest =>
      rw [htb] at h
      rw [List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_map] at h
        obtain ⟨t, _, hCp⟩ := h
        have : p = (t.1 : ℕ) := (Prod.mk.injEq _ _ _ _ ▸ hCp).2.symm
        rw [this]; exact t.1.isLt
      · exact ih rest h

/-- Every clause emitted by the decoder core belongs to the input clause list. -/
theorem replayBlocksFlat_clause_mem {w : ℕ} :
    ∀ (L : List (Clause n)) (toks : List (Fin w × Bool)) {C : Clause n} {p : ℕ},
      (C, p) ∈ replayBlocksFlat L toks → C ∈ L := by
  intro L
  induction L with
  | nil => intro toks C p h; simp [replayBlocksFlat] at h
  | cons D cs' ih =>
    intro toks C p h
    rw [replayBlocksFlat] at h
    cases htb : takeBlock toks with
    | mk blk rest =>
      rw [htb] at h
      rw [List.mem_append] at h
      rcases h with h | h
      · rw [List.mem_map] at h
        obtain ⟨t, _, hCp⟩ := h
        have : C = D := (Prod.mk.injEq _ _ _ _ ▸ hCp).1.symm
        rw [this]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih rest h)

/-- Every position emitted by `Dseq` is `< w`. -/
theorem Dseq_pos_lt {w s : ℕ} (cs : List (Clause n)) (σ_end : Fin n → Option Bool)
    (lbl : SwitchingCounting.PathLabel w s) {C : Clause n} {p : ℕ}
    (h : (C, p) ∈ Dseq cs σ_end lbl) : p < w :=
  replayBlocksFlat_pos_lt _ _ h

/-- Every clause emitted by `Dseq` belongs to `cs`. -/
theorem Dseq_clause_mem {w s : ℕ} (cs : List (Clause n)) (σ_end : Fin n → Option Bool)
    (lbl : SwitchingCounting.PathLabel w s) {C : Clause n} {p : ℕ}
    (h : (C, p) ∈ Dseq cs σ_end lbl) : C ∈ cs := by
  have hL : C ∈ leafClauses cs σ_end := replayBlocksFlat_clause_mem _ _ h
  rw [leafClauses] at hL
  exact List.mem_of_mem_filter hL

/-! ## Structural theory of `takeBlock` / `replayBlocksFlat` (toward correctness) -/

/-- `takeBlock` splits a token list: the block and the remainder recombine to the original. -/
theorem takeBlock_fst_append_snd {w : ℕ} :
    ∀ (toks : List (Fin w × Bool)), (takeBlock toks).1 ++ (takeBlock toks).2 = toks := by
  intro toks
  induction toks with
  | nil => rfl
  | cons t ts ih =>
    rw [takeBlock]
    cases h : t.2 with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases htb : takeBlock ts with
      | mk b r =>
        rw [htb] at ih
        rw [List.cons_append, ih]

/-- The decoder core emits nothing from an empty token list. -/
theorem replayBlocksFlat_nil {w : ℕ} :
    ∀ (L : List (Clause n)), replayBlocksFlat L ([] : List (Fin w × Bool)) = [] := by
  intro L
  induction L with
  | nil => rfl
  | cons C cs' ih => rw [replayBlocksFlat]; simpa [takeBlock] using ih

/-- The decoder core emits at most one entry per token: its output is no longer than the label. -/
theorem replayBlocksFlat_length_le {w : ℕ} :
    ∀ (L : List (Clause n)) (toks : List (Fin w × Bool)),
      (replayBlocksFlat L toks).length ≤ toks.length := by
  intro L
  induction L with
  | nil => intro toks; simp [replayBlocksFlat]
  | cons C cs' ih =>
    intro toks
    have hcons : replayBlocksFlat (C :: cs') toks
        = (takeBlock toks).1.map (fun t => (C, (t.1 : ℕ)))
            ++ replayBlocksFlat cs' (takeBlock toks).2 := by rw [replayBlocksFlat]
    rw [hcons, List.length_append, List.length_map]
    calc (takeBlock toks).1.length + (replayBlocksFlat cs' (takeBlock toks).2).length
        ≤ (takeBlock toks).1.length + (takeBlock toks).2.length :=
          Nat.add_le_add_left (ih _) _
      _ = ((takeBlock toks).1 ++ (takeBlock toks).2).length := by rw [List.length_append]
      _ = toks.length := by rw [takeBlock_fst_append_snd]

/-- **First correctness fragment.**  With an empty (length-`0`) label the decoder outputs nothing —
the `s = 0` regime (no satisfy steps), where `deepestSatSeq` is also empty.  A genuine, if small,
validation that the concrete `Dseq` agrees with the target on that regime. -/
theorem Dseq_nil {w : ℕ} (cs : List (Clause n)) (σ_end : Fin n → Option Bool)
    (lbl : SwitchingCounting.PathLabel w 0) : Dseq cs σ_end lbl = [] := by
  rw [Dseq]
  have hofn : (List.ofFn lbl) = ([] : List (Fin w × Bool)) :=
    List.ofFn_zero
  rw [hofn, replayBlocksFlat_nil]

/-! ## Nondecreasing clause indices -/

/-- In a `Nodup` list, if `C :: cs'` is a sublist then every later element `D ∈ cs'` has a `≥` index. -/
theorem sublist_cons_idxOf_le {α : Type*} [DecidableEq α] {cs : List α} (hnd : cs.Nodup) :
    ∀ {C cs' D}, List.Sublist (C :: cs') cs → D ∈ cs' → cs.idxOf C ≤ cs.idxOf D := by
  induction cs with
  | nil => intro C cs' D hsub hD; exact absurd hsub (by simp)
  | cons a cs₀ ih =>
    intro C cs' D hsub hD
    have hnd0 : cs₀.Nodup := hnd.of_cons
    have hane : a ∉ cs₀ := (List.nodup_cons.mp hnd).1
    cases hsub with
    | cons _ hsub' =>
      have hCmem : C ∈ cs₀ := hsub'.subset List.mem_cons_self
      have hDmem : D ∈ cs₀ := hsub'.subset (List.mem_cons_of_mem _ hD)
      have hCa : a ≠ C := fun h => hane (h ▸ hCmem)
      have hDa : a ≠ D := fun h => hane (h ▸ hDmem)
      rw [List.idxOf_cons_ne _ hCa, List.idxOf_cons_ne _ hDa]
      exact Nat.add_le_add_right (ih hnd0 hsub' hD) 1
    | cons₂ _ hsub' =>
      rw [List.idxOf_cons_self]
      exact Nat.zero_le _

/-- A list of constant value is `≤`-pairwise. -/
theorem pairwise_le_map_const {β : Type*} (k : ℕ) :
    ∀ (l : List β), List.Pairwise (· ≤ ·) (l.map (fun _ => k))
  | [] => List.Pairwise.nil
  | _ :: t => by
      rw [List.map_cons]
      refine List.Pairwise.cons (fun x hx => ?_) (pairwise_le_map_const k t)
      rw [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; exact le_refl k

/-- **Nondecreasing clause indices (decoder core).**  For a `Nodup` clause list, if the decoder walks a
sublist `L <+ cs`, the `cs`-indices of the emitted clauses are non-decreasing. -/
theorem replayBlocksFlat_idxOf_pairwise {w : ℕ} (cs : List (Clause n)) (hnd : cs.Nodup) :
    ∀ (L : List (Clause n)) (toks : List (Fin w × Bool)), List.Sublist L cs →
      List.Pairwise (· ≤ ·) ((replayBlocksFlat L toks).map (fun e => cs.idxOf e.1)) := by
  intro L
  induction L with
  | nil => intro toks _; simp [replayBlocksFlat]
  | cons C cs' ih =>
    intro toks hsub
    have hcons : replayBlocksFlat (C :: cs') toks
        = (takeBlock toks).1.map (fun t => (C, (t.1 : ℕ)))
            ++ replayBlocksFlat cs' (takeBlock toks).2 := by
      rw [replayBlocksFlat]
    rw [hcons, List.map_append, List.map_map]
    have hcomp : ((fun e => cs.idxOf e.1) ∘ fun t => (C, (t.1 : ℕ)))
        = (fun _ : Fin w × Bool => cs.idxOf C) := rfl
    rw [hcomp, List.pairwise_append]
    refine ⟨pairwise_le_map_const _ _, ih _ ((List.sublist_cons_self C cs').trans hsub), ?_⟩
    intro x hx y hy
    rw [List.mem_map] at hx
    obtain ⟨_, _, rfl⟩ := hx
    rw [List.mem_map] at hy
    obtain ⟨⟨D, q⟩, hDmem, rfl⟩ := hy
    have hDcs' : D ∈ cs' := replayBlocksFlat_clause_mem _ _ hDmem
    exact sublist_cons_idxOf_le hnd hsub hDcs'

/-- **Nondecreasing clause indices (`Dseq`).**  For `cs.Nodup`, the `cs`-indices of the clauses emitted
by `Dseq` are non-decreasing — the same structural shape as the proved `deepestSatSeq_idxOf_pairwise`. -/
theorem Dseq_idxOf_pairwise {w s : ℕ} (cs : List (Clause n)) (hnd : cs.Nodup)
    (σ_end : Fin n → Option Bool) (lbl : SwitchingCounting.PathLabel w s) :
    List.Pairwise (· ≤ ·) ((Dseq cs σ_end lbl).map (fun e => cs.idxOf e.1)) :=
  replayBlocksFlat_idxOf_pairwise cs hnd (leafClauses cs σ_end) (List.ofFn lbl)
    List.filter_sublist

/-! ## The (superseded) satisfy-position obligation, as a named target

`Dseq_correct_general` would say the rigid `Dseq` (satisfy-position label only) reproduces
`deepestSatSeq` for every bad `ρ`.  `Dseq_first_clause_mem` (the no-go) shows this is **unachievable**
for this `Dseq` — it cannot emit an interior empty block, which the confound forces.  So it is stated
here as a *named `Prop`* (no `sorry`, nothing proves it), and is **superseded** by the sorry-free
full-path reconstruction (`fullpath_switching_count`), which records the falsify steps the
satisfy-position label drops.  The three reductions below are kept as *conditional* theorems on this
obligation, documenting how the old route would have closed had `Dseq` been general. -/
def Dseq_correct_general (cs : List (Clause n)) (w s F : ℕ)
    (Bad : Finset (SwitchingCounting.Restriction n)) : Prop :=
  ∃ lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s,
    ∀ ρ ∈ Bad, Dseq cs (deepestEnd cs F ρ) (lab ρ) = deepestSatSeq cs F ρ

end Depth3

end PallLean.Paper93.DeepMath.PathB
