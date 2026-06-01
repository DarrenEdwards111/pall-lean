import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingIterStable
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingRevPeel

/-!
# The within-single-clause decoder: `decodeVars` and its recovery

**STATUS: REAL.  decode_encode_id FOR THE WITHIN-CLAUSE CASE.**

For a path that stays within a single active clause `C₀` (`s` below `C₀`'s
free-literal count), the canonical decoder is now fully realisable on proved lemmas:

* `decodeVarsWC cs τ idxs`: recompute the active clause `C := activeClause cs τ`
  (constant within a clause, recovered from the *end* state by
  `activeClause_actPath_end`), and look up each recorded index in `C.lits`;
* `pathIdxsRev cs ρ s`: the encoder — record, at each step, the position of the
  fixed literal inside the active clause (`idxOf` into `C.lits`), a `Fin (width)`
  datum;
* `decodeVarsWC_recover`: `decodeVarsWC cs (actPath cs ρ s) (pathIdxsRev cs ρ s)
  = pathVarsRev cs ρ s` — the decoder reconstructs the path's variable list from the
  end state plus the index label, *without* `ρ`.

Composed with `revPeel_pathVarsRev`, this gives `ρ` back from `(actPath cs ρ s,
pathIdxsRev cs ρ s)` — `decode_encode_id` for the within-clause case
(`revPeel_decodeVarsWC`).  The remaining gap is purely the *multi-clause boundary*
threading (find the just-exhausted clause when the active clause has advanced).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The index recorded at one step: the position of the active literal inside the
active clause (a clause-relative `Fin (width)` datum). -/
def stepIdx (cs : List (Clause n)) (σ : Restriction n) : Option ℕ :=
  match activeClause cs σ, activeLit cs σ with
  | some C, some ℓ => some (C.lits.idxOf ℓ)
  | _, _ => none

/-- The encoder: the recorded index list, in reverse fixing order. -/
def pathIdxsRev (cs : List (Clause n)) (ρ : Restriction n) : ℕ → List ℕ
  | 0 => []
  | k + 1 =>
    match stepIdx cs (actPath cs ρ k) with
    | none => pathIdxsRev cs ρ k
    | some i => i :: pathIdxsRev cs ρ k

/-- The decoder: recompute the active clause from the current state, then look up each
recorded index inside it. -/
def decodeVarsWC (cs : List (Clause n)) (τ : Restriction n) (idxs : List ℕ) : List (Fin n) :=
  match activeClause cs τ with
  | none => []
  | some C => idxs.filterMap (fun i => (C.lits[i]?).map litVar)

/-- Core recovery: against a fixed clause `C₀` active throughout, the recorded indices
look up to exactly the path's selected variables. -/
theorem decode_core (cs : List (Clause n)) (ρ : Restriction n) (C₀ : Clause n) :
    ∀ s, (∀ k, k ≤ s → activeClause cs (actPath cs ρ k) = some C₀) →
      (pathIdxsRev cs ρ s).filterMap (fun i => (C₀.lits[i]?).map litVar)
        = pathVarsRev cs ρ s := by
  intro s
  induction s with
  | zero => intro _; simp [pathIdxsRev, pathVarsRev]
  | succ s ih =>
    intro hall
    have hCs : activeClause cs (actPath cs ρ s) = some C₀ := hall s (Nat.le_succ s)
    obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp (activeLit_isSome hCs)
    have hstepidx : stepIdx cs (actPath cs ρ s) = some (C₀.lits.idxOf ℓ) := by
      simp only [stepIdx, hCs, hℓ]
    have hpir : pathIdxsRev cs ρ (s + 1) = C₀.lits.idxOf ℓ :: pathIdxsRev cs ρ s := by
      simp only [pathIdxsRev, hstepidx]
    have hpvr : pathVarsRev cs ρ (s + 1) = litVar ℓ :: pathVarsRev cs ρ s := by
      simp only [pathVarsRev, hℓ]
    have hℓmem : ℓ ∈ C₀.lits := by
      have hhead : (freeLits (actPath cs ρ s) C₀).head? = some ℓ := by
        unfold activeLit at hℓ; rw [hCs] at hℓ; exact hℓ
      exact (List.mem_filter.mp (List.mem_of_mem_head? hhead)).1
    have hf : (C₀.lits[C₀.lits.idxOf ℓ]?).map litVar = some (litVar ℓ) := by
      rw [List.getElem?_idxOf hℓmem]; rfl
    rw [hpir, hpvr]
    simp only [List.filterMap_cons, hf]
    rw [ih (fun k hk => hall k (Nat.le_succ_of_le hk))]

/-- **`decodeVars` recovers the path's variable list** from the end state plus the
index label, with no access to `ρ` (within-clause case). -/
theorem decodeVarsWC_recover {cs : List (Clause n)} {ρ : Restriction n} {C₀ : Clause n}
    (hnodup : (C₀.lits.map litVar).Nodup) (hC : activeClause cs ρ = some C₀)
    {s : ℕ} (hs : s < (freeLits ρ C₀).length) :
    decodeVarsWC cs (actPath cs ρ s) (pathIdxsRev cs ρ s) = pathVarsRev cs ρ s := by
  have hCs : activeClause cs (actPath cs ρ s) = some C₀ := activeClause_actPath_end hnodup hC hs
  simp only [decodeVarsWC, hCs]
  exact decode_core cs ρ C₀ s
    (fun k hk => activeClause_actPath_end hnodup hC (Nat.lt_of_le_of_lt hk hs))

/-- **`decode_encode_id` (within-clause case).**  `ρ` is recovered from its end state
and its index label. -/
theorem revPeel_decodeVarsWC {cs : List (Clause n)} {ρ : Restriction n} {C₀ : Clause n}
    (hnodup : (C₀.lits.map litVar).Nodup) (hC : activeClause cs ρ = some C₀)
    {s : ℕ} (hs : s < (freeLits ρ C₀).length) :
    revPeel (actPath cs ρ s) (decodeVarsWC cs (actPath cs ρ s) (pathIdxsRev cs ρ s)) = ρ := by
  rw [decodeVarsWC_recover hnodup hC hs, revPeel_pathVarsRev]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.decodeVarsWC_recover
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.revPeel_decodeVarsWC
