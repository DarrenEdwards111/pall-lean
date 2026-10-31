import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATFamilyDenseFloor
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGWireSurgery
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWireTreeCircuit

/-!
# The SAT live chain: full-length gate elimination on the exact target family

Fourth rung: the SAT-specific restriction structure, built on the existing DAG surgery
engine (`cbudget_onekill` / `cbudget_livechain`) — nothing re-proved, the engine is
reused as-is.  Two deliverables:

* **The full-length SAT live chain (proved).**  `SATFamily N` admits a `LiveChain` of
  length `N − 22`: pin positions `N−1, N−2, …, 22` to `false`, top down.  At every
  step SAT stays live *inside the pinned cube* because the rung-3 steering word for
  position `i` has an **all-false tail** — it is compatible with every pin above `i`
  by construction.  This is the "SAT remains nonconstant through a long controlled
  sequence of restrictions" structure, at maximal order `n − O(1)` on the exact codec
  family (the surgery file's roadmap sketched `~3mv ≈ N` steps for the abstract
  `sat3Family`; here it is realized on `SATFamily` itself).

* **The composite engine (proved).**  `cbudget_livechain` discards the residual;
  `cbudget_livechain_residual` keeps it:
  `LiveChain f steps → DependsOnF (restrictAll f steps) j →
   steps.length + cbudget (restrictAll f steps) ≤ cbudget f` — restriction banking
  composable with any lower bound on the residual (e.g. the cone bound).

## Honest accounting

The one-kill rate caps a pure chain bound at `n`, and the composite
chain-plus-cone at `2n` — a live restriction banks 1 gate but retires a coordinate
that the cone bound would have charged 2 for.  Both are therefore **subsumed by the
rung-3 dense floor** `2N − 45` as bounds; the value here is the structure: the chain
witnesses and the composite engine are exactly what a DAG **two-kill** step would
convert into `> 2n`.  The surgery file records that no DAG two-kill analogue is
currently proved — that, not longer chains, is the named missing piece; beyond it the
Schnorr/FGHK/Li–Yang ladder (`2n`, `2.5n`, `3.01n`, `3.1n` in the standard
convention — constants not directly comparable to `cbudget`, which charges input
access) and then the superpolynomial wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATFamilyLiveChain

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec

/-! ### The composite engine: chain banking plus the residual -/

theorem restrictAll_const {n : ℕ} :
    ∀ (steps : List (Fin n × Bool)) (g : (Fin n → Bool) → Bool),
      (∀ u w, g u = g w) → ∀ u w, restrictAll g steps u = restrictAll g steps w := by
  intro steps
  induction steps with
  | nil => intro g hg u w; exact hg u w
  | cons s rest ih =>
    intro g hg u w
    exact ih (restrictF g s.1 s.2) (fun u' w' => hg _ _) u w

/-- **The composite engine (proved).**  A live schedule banks one gate per step *on
top of* the residual's own circuit budget. -/
theorem cbudget_livechain_residual {n : ℕ} :
    ∀ (steps : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool) (j : Fin n),
      LiveChain f steps → DependsOnF (restrictAll f steps) j →
      steps.length + cbudget (restrictAll f steps) ≤ cbudget f := by
  intro steps
  induction steps with
  | nil =>
    intro f j _ _
    show 0 + cbudget f ≤ cbudget f
    omega
  | cons s rest ih =>
    intro f j h hres
    obtain ⟨hdep, hchain⟩ := (h : DependsOnF f s.1 ∧ LiveChain (restrictF f s.1 s.2) rest)
    have hnc : ∃ u w, restrictF f s.1 s.2 u ≠ restrictF f s.1 s.2 w := by
      by_contra hc
      push_neg at hc
      obtain ⟨x₁, x₀, -, hne⟩ := hres
      exact hne (restrictAll_const rest (restrictF f s.1 s.2) hc x₁ x₀)
    have hkill := cbudget_onekill f s.1 s.2 hdep hnc
    have hih := ih (restrictF f s.1 s.2) j hchain hres
    show rest.length + 1 + cbudget (restrictAll (restrictF f s.1 s.2) rest) ≤ cbudget f
    omega

/-! ### The steering words are pin-compatible: all-false tails -/

theorem denseWord_getD_high (N i j : ℕ) (hi : 22 ≤ i) (hij : i < j) :
    (denseWord N i).getD j false = false := by
  have hL : (encodeFormula' (phiD (i - 21) true)).length = i + 1 := by
    rw [encode_phiD_length]
    omega
  rcases Nat.lt_or_ge j (denseWord N i).length with h | h
  · have hlen2 : (denseWord N i).length = (i + 1) + (N - i - 1) := by
      rw [denseWord, List.length_append, hL, List.length_replicate]
    rw [denseWord, List.getD_append_right _ _ false j (by rw [hL]; omega), hL]
    exact getD_replicate_lt _ _ _ (by omega)
  · exact List.getD_eq_default _ _ h

/-- The rung-3 flip, packaged for chain use: the steering word is a true-point and its
one-bit flip a false-point of `SATFamily N`. -/
theorem dense_flip (N i : ℕ) (hi : 22 ≤ i) (hiN : i < N) :
    SATFamily N (fun k : Fin N => (denseWord N i).getD k.val false) = true
    ∧ SATFamily N (Function.update
        (fun k : Fin N => (denseWord N i).getD k.val false) ⟨i, hiN⟩ false) = false := by
  constructor
  · rw [SATFamily_apply, wordOfFin_getD_eq _ (denseWord_length N i hi hiN), denseWord]
    exact SATLang_append_sat _ _ (satisfiable_phiD _ (by omega))
  · rw [SATFamily_apply, wordOfFin_update, wordOfFin_getD_eq _ (denseWord_length N i hi hiN)]
    show SATLang ((denseWord N i).set i false) = false
    rw [denseWord_set N i hi]
    exact SATLang_append_unsat _ _ (unsat_phiD _)

/-! ### The descending pin schedule -/

/-- Pin positions `21+l, 21+l−1, …, 22` to `false`, top down. -/
def descSteps (N : ℕ) : (l : ℕ) → 21 + l < N → List (Fin N × Bool)
  | 0, _ => []
  | l + 1, h => (⟨22 + l, by omega⟩, false) :: descSteps N l (by omega)

theorem descSteps_length (N : ℕ) :
    ∀ (l : ℕ) (h : 21 + l < N), (descSteps N l h).length = l := by
  intro l
  induction l with
  | zero => intro h; rfl
  | succ l ih =>
    intro h
    show (descSteps N l _).length + 1 = l + 1
    rw [ih]

/-! ### The chain is live at every step -/

/-- **The descending chain is live (proved).**  If `g` is `SATFamily N` with all
positions above `21+l` pinned `false`, the schedule down to position `22` keeps SAT
live at every step — the steering word for the current position lies inside the
pinned cube. -/
theorem liveChain_desc (N : ℕ) :
    ∀ (l : ℕ) (h : 21 + l < N) (g : (Fin N → Bool) → Bool),
      (∀ x, g x = SATFamily N (fun k => if 21 + l < k.val then false else x k)) →
      LiveChain g (descSteps N l h) := by
  intro l
  induction l with
  | zero => intro h g hg; trivial
  | succ l ih =>
    intro h g hg
    have hlt : 22 + l < N := by omega
    refine ⟨?_, ?_⟩
    · -- SAT is live at position 22+l inside the pinned cube
      refine ⟨(fun k : Fin N => (denseWord N (22 + l)).getD k.val false),
        Function.update (fun k : Fin N => (denseWord N (22 + l)).getD k.val false)
          ⟨22 + l, hlt⟩ false, ?_, ?_⟩
      · intro c hc
        by_contra hcne
        exact absurd (Function.update_of_ne hcne false
          (fun k : Fin N => (denseWord N (22 + l)).getD k.val false)).symm hc
      · have hmask₁ : (fun k : Fin N => if 21 + (l + 1) < k.val then false
            else (denseWord N (22 + l)).getD k.val false)
            = (fun k : Fin N => (denseWord N (22 + l)).getD k.val false) := by
          funext k
          by_cases hk : 21 + (l + 1) < k.val
          · rw [if_pos hk]
            exact (denseWord_getD_high N (22 + l) k.val (by omega) (by omega)).symm
          · rw [if_neg hk]
        have hmask₀ : (fun k : Fin N => if 21 + (l + 1) < k.val then false
            else Function.update (fun k' : Fin N => (denseWord N (22 + l)).getD k'.val false)
              ⟨22 + l, hlt⟩ false k)
            = Function.update (fun k' : Fin N => (denseWord N (22 + l)).getD k'.val false)
              ⟨22 + l, hlt⟩ false := by
          funext k
          by_cases hk : 21 + (l + 1) < k.val
          · rw [if_pos hk,
              Function.update_of_ne
                (show k ≠ ⟨22 + l, hlt⟩ from fun he => by rw [he] at hk; simp at hk; omega)
                false (fun k' : Fin N => (denseWord N (22 + l)).getD k'.val false)]
            exact (denseWord_getD_high N (22 + l) k.val (by omega) (by omega)).symm
          · rw [if_neg hk]
        rw [hg, hg, hmask₁, hmask₀, (dense_flip N (22 + l) (by omega) hlt).1,
          (dense_flip N (22 + l) (by omega) hlt).2]
        simp
    · -- the tail chain: the pin extends the mask by one position
      apply ih (by omega)
      intro x
      show g (Function.update x ⟨22 + l, hlt⟩ false) = _
      rw [hg]
      congr 1
      funext k
      by_cases hk21 : 21 + l < k.val
      · by_cases hk22 : 21 + (l + 1) < k.val
        · rw [if_pos hk22, if_pos hk21]
        · -- k.val = 22 + l exactly: the freshly pinned position
          have hkv : k.val = 22 + l := by omega
          have hke : k = (⟨22 + l, hlt⟩ : Fin N) := Fin.ext hkv
          rw [if_neg hk22, if_pos hk21, hke, Function.update_self]
      · have hk22 : ¬ 21 + (l + 1) < k.val := by omega
        rw [if_neg hk22, if_neg hk21,
          Function.update_of_ne (fun he => by rw [he] at hk21; simp at hk21) false x]

/-- **THE FULL-LENGTH SAT LIVE CHAIN (proved).**  `SATFamily N` admits a live
restriction schedule of length `N − 22`. -/
theorem SATFamily_liveChain (N : ℕ) (hN : 22 ≤ N) :
    LiveChain (SATFamily N) (descSteps N (N - 22) (by omega)) := by
  apply liveChain_desc
  intro x
  congr 1
  funext k
  rw [if_neg (by have := k.isLt; omega)]

/-- The chain instantiation of the surgery engine on the exact target (subsumed as a
bound by the rung-3 dense floor `2N − 45`; recorded as the engine's SAT record). -/
theorem cbudget_SATFamily_livechain (N : ℕ) (hN : 22 ≤ N) :
    N - 22 ≤ cbudget (SATFamily N) := by
  have h := cbudget_livechain (descSteps N (N - 22) (by omega)) (SATFamily N)
    (SATFamily_liveChain N hN)
  rwa [descSteps_length] at h

end PallLean.Paper93.DeepMath.PathB.SATFamilyLiveChain

#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyLiveChain.cbudget_livechain_residual
#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyLiveChain.SATFamily_liveChain
#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyLiveChain.cbudget_SATFamily_livechain
