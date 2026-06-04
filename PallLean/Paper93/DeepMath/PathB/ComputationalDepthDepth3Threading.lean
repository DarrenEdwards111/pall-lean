import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ForwardScanPath
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestFalsifyPart

/-!
# Threading the falsify and satisfy mechanisms into one decomposition of `deepestSel`

The two mechanisms isolated so far recover *disjoint* parts of the deepest selected set:

* **falsify steps** — the stepped literal is set *false*; its variable carries a false literal at the
  end-state and is recovered **label-free** by `decodedSel` (`decodedSel_subset_deepestSel`);
* **satisfy/advance steps** — the stepped literal is set *true*; its variable carries *no* false
  literal, so it needs the `(2w)^s` label (and `activeTerm_advance_stable` re-identifies its clause).

This file *threads* them: it splits `deepestSel` along the deepest branch into the falsify-step set
`deepestFalSel` and the satisfy-step set `deepestSatSel`, and proves — under **only** "ρ falsifies
nothing", no read-once — that

    decodedSel (deepestEnd cs F ρ) ∪ deepestSatSel cs F ρ = deepestSel cs F ρ.

So the falsify half is **fully discharged** by the proved label-free `decodedSel`, and the open kernel
shrinks from "recover `deepestSel`" to "recover `deepestSatSel`" (the satisfy variables only).

* `litFalse_deepestEnd_of` — path-level persistence of a false literal to the end-state (the
  `litFalse` analogue of `termFalsified_deepestEnd`).
* `deepestFalSel` / `deepestSatSel` — the falsify- and satisfy-step variable sets (same recursion as
  `deepestSel`, each step's variable routed by whether its literal is forced false).
* `deepestSel_eq_falSel_union_satSel` — **the partition**: `deepestSel = deepestFalSel ∪ deepestSatSel`.
* `deepestFalSel_subset_decodedSel` — every falsify-step variable is read off the end-state (its
  literal stays false to the leaf, its clause stays falsified).  **No** "ρ falsifies nothing" needed.
* `decodedSel_union_satSel_eq_deepestSel` — **the threading equality** (needs only "ρ falsifies
  nothing"): the union of the proved label-free part and the satisfy part is the whole selected set.
* `reconstruction_of_satSel_decoder` — **the sharpened reduction**: `ReconstructionCorrect` follows
  from a decoder recovering just `deepestSatSel` from `(end-state, label)`; the falsify half is wired
  in by `decodedSel`.

The satisfy-variable recovery (`deepestSatSel` from the label) remains the open core — **not** faked;
but it is now the *only* remaining obligation, with the falsify half threaded in by proof.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Path-level persistence of a false literal.**  A literal forced false at `σ` stays false at the
deepest-branch end-state `deepestEnd cs fuel σ`: each step fixes a *free* variable (the active
literal's), distinct from the already-fixed variable of `ℓ`, so `litFalse_fixVar_of_free` applies all
the way down.  The `litFalse` analogue of `termFalsified_deepestEnd`. -/
theorem litFalse_deepestEnd_of (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool) (ℓ : Rung4Literal n),
      SwitchingCounting.litFalse σ ℓ = true →
      SwitchingCounting.litFalse (deepestEnd cs fuel σ) ℓ = true := by
  intro fuel
  induction fuel with
  | zero => intro σ ℓ h; exact h
  | succ fuel ih =>
    intro σ ℓ h
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestEnd]; simp only [hany, if_true]; exact h
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact]; exact h
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; exact h
        | some ℓ₀ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ₀ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hfree : σ (litVar ℓ₀) = none := activeTermLit_var_free hatl
          rw [deepestEnd]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]
          split
          · exact ih _ _ (litFalse_fixVar_of_free h hfree)
          · exact ih _ _ (litFalse_fixVar_of_free h hfree)

/-- The **falsify-step** variables of the deepest branch: the same recursion as `deepestSel`, but a
step's variable is collected only when its stepped literal is forced *false*. -/
def deepestFalSel (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → Finset (Fin n)
  | 0, _ => ∅
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then ∅
    else match SwitchingCounting.activeTerm cs σ with
      | none => ∅
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => ∅
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ
                 then insert (litVar ℓ) else id) (deepestFalSel cs fuel (fixVar σ (litVar ℓ) false))
          else (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ
                 then insert (litVar ℓ) else id) (deepestFalSel cs fuel (fixVar σ (litVar ℓ) true))

/-- The **satisfy-step** variables of the deepest branch: dual to `deepestFalSel`, collecting a step's
variable only when its stepped literal is *not* forced false (set true). -/
def deepestSatSel (cs : List (Clause n)) : ℕ → (Fin n → Option Bool) → Finset (Fin n)
  | 0, _ => ∅
  | fuel + 1, σ =>
    if SwitchingCounting.anyTermSat cs σ then ∅
    else match SwitchingCounting.activeTerm cs σ with
      | none => ∅
      | some T => match (SwitchingCounting.freeLits σ T).head? with
        | none => ∅
        | some ℓ =>
          if (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
             (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          then (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ
                 then id else insert (litVar ℓ)) (deepestSatSel cs fuel (fixVar σ (litVar ℓ) false))
          else (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ
                 then id else insert (litVar ℓ)) (deepestSatSel cs fuel (fixVar σ (litVar ℓ) true))

/-- **The partition.**  Every deepest-branch step's variable is either a falsify step or a satisfy
step, so `deepestSel = deepestFalSel ∪ deepestSatSel`. -/
theorem deepestSel_eq_falSel_union_satSel (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool),
      deepestSel cs fuel σ = deepestFalSel cs fuel σ ∪ deepestSatSel cs fuel σ := by
  intro fuel
  induction fuel with
  | zero => intro σ; simp [deepestSel, deepestFalSel, deepestSatSel]
  | succ fuel ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => simp [deepestSel, deepestFalSel, deepestSatSel, hany]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => simp [deepestSel, deepestFalSel, deepestSatSel, hany, hact]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp [deepestSel, deepestFalSel, deepestSatSel, hany, hact, hh]
        | some ℓ =>
          by_cases hd : (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          · -- then-branch: `b = false`
            rw [deepestSel, deepestFalSel, deepestSatSel]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh]
            rw [if_pos hd, if_pos hd, if_pos hd]
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) false) ℓ = true
            · rw [if_pos hf, if_pos hf, id_eq, ih (fixVar σ (litVar ℓ) false), Finset.insert_union]
            · rw [if_neg hf, if_neg hf, id_eq, ih (fixVar σ (litVar ℓ) false), Finset.union_insert]
          · -- else-branch: `b = true`
            rw [deepestSel, deepestFalSel, deepestSatSel]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh]
            rw [if_neg hd, if_neg hd, if_neg hd]
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) true) ℓ = true
            · rw [if_pos hf, if_pos hf, id_eq, ih (fixVar σ (litVar ℓ) true), Finset.insert_union]
            · rw [if_neg hf, if_neg hf, id_eq, ih (fixVar σ (litVar ℓ) true), Finset.union_insert]

/-- **Every falsify-step variable is read off the end-state.**  A falsify step's literal `ℓ` is forced
false at the successor state, persists false to the leaf (`litFalse_deepestEnd_of`), and lies in the
active clause `T` (which is then falsified at the leaf) — so `litVar ℓ ∈ decodedSel (deepestEnd …)`.
This needs **no** "ρ falsifies nothing" hypothesis. -/
theorem deepestFalSel_subset_decodedSel (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool),
      deepestFalSel cs fuel σ ⊆ SwitchingCounting.decodedSel cs (deepestEnd cs fuel σ) := by
  intro fuel
  induction fuel with
  | zero => intro σ; simp [deepestFalSel]
  | succ fuel ih =>
    intro σ
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => simp [deepestFalSel, hany]
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => simp [deepestFalSel, hany, hact]
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none => simp [deepestFalSel, hany, hact, hh]
        | some ℓ =>
          have hℓT : ℓ ∈ T.lits := (List.mem_filter.mp (List.mem_of_mem_head? hh)).1
          have hTmem : T ∈ cs := SwitchingCounting.activeTerm_mem hact
          -- a uniform body for both depth-branches (parameterised by the chosen bit `b`)
          have body : ∀ b : Bool,
              (if SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ then insert (litVar ℓ) else id)
                (deepestFalSel cs fuel (fixVar σ (litVar ℓ) b)) ⊆
              SwitchingCounting.decodedSel cs (deepestEnd cs fuel (fixVar σ (litVar ℓ) b)) := by
            intro b
            by_cases hf : SwitchingCounting.litFalse (fixVar σ (litVar ℓ) b) ℓ = true
            · rw [if_pos hf]
              refine Finset.insert_subset ?_ (ih _)
              -- `litVar ℓ ∈ decodedSel (deepestEnd …)`
              have hend : SwitchingCounting.litFalse (deepestEnd cs fuel (fixVar σ (litVar ℓ) b)) ℓ = true :=
                litFalse_deepestEnd_of cs fuel _ ℓ hf
              have hTf : SwitchingCounting.termFalsified
                  (deepestEnd cs fuel (fixVar σ (litVar ℓ) b)) T = true := by
                rw [SwitchingCounting.termFalsified, List.any_eq_true]; exact ⟨ℓ, hℓT, hend⟩
              rw [SwitchingCounting.decodedSel, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, T, hTmem, hTf, ℓ, hℓT, rfl, hend⟩
            · rw [if_neg hf, id_eq]; exact ih _
          by_cases hd : (canonicalDT cs fuel (fixVar σ (litVar ℓ) true)).depth ≤
              (canonicalDT cs fuel (fixVar σ (litVar ℓ) false)).depth
          · rw [deepestFalSel, deepestEnd]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh]
            rw [if_pos hd, if_pos hd]
            exact body false
          · rw [deepestFalSel, deepestEnd]
            simp only [hany, Bool.false_eq_true, if_false, hact, hh]
            rw [if_neg hd, if_neg hd]
            exact body true

/-- **The threading equality.**  Under "ρ falsifies nothing", the proved label-free falsify part
(`decodedSel`) and the satisfy part (`deepestSatSel`) together recover the whole selected set:
`decodedSel (deepestEnd cs F ρ) ∪ deepestSatSel cs F ρ = deepestSel cs F ρ`. -/
theorem decodedSel_union_satSel_eq_deepestSel {cs : List (Clause n)} {F : ℕ}
    {ρ : Fin n → Option Bool} (hnf : ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false) :
    SwitchingCounting.decodedSel cs (deepestEnd cs F ρ) ∪ deepestSatSel cs F ρ
      = deepestSel cs F ρ := by
  apply Finset.Subset.antisymm
  · -- `⊆`: both parts are inside `deepestSel`.
    refine Finset.union_subset (decodedSel_subset_deepestSel hnf) ?_
    rw [deepestSel_eq_falSel_union_satSel]; exact Finset.subset_union_right
  · -- `⊇`: `deepestSel = falSel ∪ satSel ⊆ decodedSel ∪ satSel` (falSel ⊆ decodedSel).
    rw [deepestSel_eq_falSel_union_satSel]
    exact Finset.union_subset_union (deepestFalSel_subset_decodedSel cs F ρ) (Finset.Subset.refl _)

/-- **The sharpened reduction.**  `ReconstructionCorrect` follows from a decoder recovering only the
satisfy variables `deepestSatSel` from `(end-state, label)` — the falsify half is wired in by the
proved label-free `decodedSel`.  So the open kernel is now exactly the satisfy-variable recovery. -/
theorem reconstruction_of_satSel_decoder {cs : List (Clause n)} {w s F : ℕ}
    {Bad : Finset (SwitchingCounting.Restriction n)}
    (hnf : ∀ ρ ∈ Bad, ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    (Dsat : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s → Finset (Fin n))
    (lab : SwitchingCounting.Restriction n → SwitchingCounting.PathLabel w s)
    (hsat : ∀ ρ ∈ Bad, Dsat (deepestEnd cs F ρ) (lab ρ) = deepestSatSel cs F ρ) :
    ReconstructionCorrect cs w s F Bad := by
  refine ⟨lab, fun π l => SwitchingCounting.decodedSel cs π ∪ Dsat π l, ?_⟩
  intro ρ hρ
  show SwitchingCounting.decodedSel cs (deepestEnd cs F ρ) ∪ Dsat (deepestEnd cs F ρ) (lab ρ)
    = deepestSel cs F ρ
  rw [hsat ρ hρ, decodedSel_union_satSel_eq_deepestSel (hnf ρ hρ)]

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.litFalse_deepestEnd_of
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSel_eq_falSel_union_satSel
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestFalSel_subset_decodedSel
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.decodedSel_union_satSel_eq_deepestSel
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.reconstruction_of_satSel_decoder
