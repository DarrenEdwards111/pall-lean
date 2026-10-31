import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATFamilyLiveChain
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGuardedTwoKillChain

/-!
# SATFamily guard witnesses: the full-length guarded chain

The two-kill guard holds along a full descending pin schedule on the exact codec
family, so the guarded chain engine fires end to end:

  **`2·(N − 23) ≤ cbudget (SATFamily N)` by pure gate elimination** —
  the `2n`-scale floor re-proved with no cone/parent-edge counting at all.

Per step at position `i ∈ [23, N)` (positions above pinned `false`), the guard's four
components are witnessed inside the pinned cube:

* nonconstancy of each restriction — the position-22 steering word and its flip,
  with bit `i` set either way (it lands in the decoder-ignored tail);
* the restrictions differ — the dense flip at `i` itself;
* they are not complementary — the all-false completion decodes to the empty
  (satisfiable) formula under both settings of bit `i`, so the restrictions agree.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATFamilyGuardedChain

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATFamilyDenseFloor
open PallLean.Paper93.DeepMath.PathB.SATFamilyLiveChain
open PallLean.Paper93.DeepMath.PathB.SATCircuitSeparationBridge
open PallLean.Paper93.DeepMath.PathB.SeparationTarget
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit

/-! ### List helpers -/

theorem getD_set_self (l : List Bool) (i : ℕ) (b : Bool) (h : i < l.length) :
    (l.set i b).getD i false = b := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact h), List.getElem_set,
    if_pos rfl]

theorem getD_set_ne (l : List Bool) (i : ℕ) (b : Bool) (k : ℕ) (h : i ≠ k) :
    (l.set i b).getD k false = l.getD k false := by
  by_cases hk : k < l.length
  · rw [List.getD_eq_getElem _ _ (by rw [List.length_set]; exact hk),
      List.getD_eq_getElem _ _ hk, List.getElem_set, if_neg h]
  · rw [List.getD_eq_default _ _ (by rw [List.length_set]; omega),
      List.getD_eq_default _ _ (by omega)]

theorem set_append_ge {α : Type} : ∀ (A B : List α) (t : ℕ) (v : α), A.length ≤ t →
    (A ++ B).set t v = A ++ B.set (t - A.length) v := by
  intro A
  induction A with
  | nil =>
    intro B t v _
    simp
  | cons a A ih =>
    intro B t v ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by
      have : 1 ≤ t := le_trans (by simp) ht
      omega⟩
    show a :: ((A ++ B).set t' v) = a :: (A ++ B.set (t' + 1 - (A.length + 1)) v)
    rw [ih B t' v (by
        have := ht
        rw [List.length_cons] at this
        omega),
      show t' + 1 - (A.length + 1) = t' - A.length from by omega]

theorem replicate_false_getD (N t : ℕ) : (List.replicate N false).getD t false = false := by
  by_cases ht : t < N
  · exact getD_replicate_lt false N t ht
  · exact List.getD_eq_default _ _ (by rw [List.length_replicate]; omega)

/-! ### SATLang facts for the witnesses -/

theorem SATLang_false_head (rest : List Bool) : SATLang (false :: rest) = true := by
  have hdec : decodeFormula' (false :: rest) = [] := by
    rw [show (false :: rest) = encodeNat 0 ++ rest from rfl, decodeFormula',
      decodeNat_encodeNat]
    rfl
  rw [SATLang, hdec, if_pos ⟨fun _ => true, rfl⟩]

theorem SATLang_replicate_set (N i : ℕ) (h1 : 1 ≤ i) (hN : 1 ≤ N) (b' : Bool) :
    SATLang ((List.replicate N false).set i b') = true := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  show SATLang (false :: (List.replicate N' false).set i' b') = true
  exact SATLang_false_head _

theorem SATLang_denseWord (N j : ℕ) (hj : 22 ≤ j) :
    SATLang (denseWord N j) = true := by
  rw [denseWord]
  exact SATLang_append_sat _ _ (satisfiable_phiD _ (by omega))

theorem SATLang_denseWord_set_high (N j t : ℕ) (hj : 22 ≤ j) (hjt : j < t) (b' : Bool) :
    SATLang ((denseWord N j).set t b') = true := by
  rw [denseWord, set_append_ge _ _ t b' (by rw [encode_phiD_length]; omega)]
  exact SATLang_append_sat _ _ (satisfiable_phiD _ (by omega))

theorem SATLang_denseWordFlip_set_high (N j t : ℕ) (hj : 22 ≤ j) (hjt : j < t) (b' : Bool) :
    SATLang (((denseWord N j).set j false).set t b') = false := by
  rw [denseWord_set N j hj, set_append_ge _ _ t b' (by rw [encode_phiD_length]; omega)]
  exact SATLang_append_unsat _ _ (unsat_phiD _)

theorem denseWord_set_true (N i : ℕ) (hi : 22 ≤ i) :
    (denseWord N i).set i true = denseWord N i := by
  show (encodeFormula' (phiD (i - 21) true) ++ List.replicate (N - i - 1) false).set i true
    = encodeFormula' (phiD (i - 21) true) ++ List.replicate (N - i - 1) false
  rw [encode_phiD, List.append_assoc, List.singleton_append,
    set_append_cons' _ _ _ _ i (by rw [densePre_length]; omega)]

theorem SATLang_denseWord_set_self (N i : ℕ) (hi : 22 ≤ i) :
    SATLang ((denseWord N i).set i false) = false := by
  rw [denseWord_set N i hi]
  exact SATLang_append_unsat _ _ (unsat_phiD _)

/-! ### The descending pin schedule down to position 23 -/

/-- Pin positions `22+l, …, 23` to `false`, top down. -/
def descSteps' (N : ℕ) : (l : ℕ) → 22 + l < N → List (Fin N × Bool)
  | 0, _ => []
  | l + 1, h => (⟨23 + l, by omega⟩, false) :: descSteps' N l (by omega)

theorem descSteps'_length (N : ℕ) :
    ∀ (l : ℕ) (h : 22 + l < N), (descSteps' N l h).length = l := by
  intro l
  induction l with
  | zero => intro h; rfl
  | succ l ih =>
    intro h
    show (descSteps' N l _).length + 1 = l + 1
    rw [ih]

/-! ### The guard holds at every step -/

theorem guardedChain_desc (N : ℕ) :
    ∀ (l : ℕ) (h : 22 + l < N) (g : (Fin N → Bool) → Bool),
      (∀ x, g x = SATFamily N (fun k => if 22 + l < k.val then false else x k)) →
      GuardedChain g (descSteps' N l h) := by
  intro l
  induction l with
  | zero => intro h g hg; trivial
  | succ l ih =>
    intro h g hg
    have hlt : 23 + l < N := by omega
    -- the workhorse: restricting the masked function at position 23+l on a word-vector
    -- with an all-false high tail computes SATLang of the set word
    have hval : ∀ (w : List Bool), w.length = N →
        (∀ t, 23 + l < t → w.getD t false = false) → ∀ b',
        restrictF g ⟨23 + l, hlt⟩ b' (fun k : Fin N => w.getD k.val false)
          = SATLang (w.set (23 + l) b') := by
      intro w hwlen hwhigh b'
      show g (Function.update (fun k : Fin N => w.getD k.val false) ⟨23 + l, hlt⟩ b')
        = SATLang (w.set (23 + l) b')
      rw [hg]
      have hmask : (fun k : Fin N => if 22 + (l + 1) < k.val then false
          else Function.update (fun k' : Fin N => w.getD k'.val false) ⟨23 + l, hlt⟩ b' k)
          = fun k : Fin N => (w.set (23 + l) b').getD k.val false := by
        funext k
        by_cases hk : 22 + (l + 1) < k.val
        · rw [if_pos hk]
          exact (by rw [getD_set_ne w _ b' _ (by omega), hwhigh k.val (by omega)] :
            (w.set (23 + l) b').getD k.val false = false).symm
        · rw [if_neg hk]
          by_cases hki : k.val = 23 + l
          · have hke : k = ⟨23 + l, hlt⟩ := Fin.ext hki
            rw [hke, Function.update_self]
            exact (getD_set_self w _ b' (by omega)).symm
          · rw [Function.update_of_ne (fun he => hki (by rw [he])) b'
              (fun k' : Fin N => w.getD k'.val false)]
            exact (getD_set_ne w _ b' _ (fun he => hki he.symm)).symm
      rw [hmask, SATFamily_apply,
        wordOfFin_getD_eq _ (by rw [List.length_set]; exact hwlen)]
    -- witness-word facts
    have hW22len : (denseWord N 22).length = N := denseWord_length N 22 (le_refl _) (by omega)
    have hW22high : ∀ t, 23 + l < t → (denseWord N 22).getD t false = false :=
      fun t ht => denseWord_getD_high N 22 t (le_refl _) (by omega)
    have hW22flen : ((denseWord N 22).set 22 false).length = N := by
      rw [List.length_set]
      exact hW22len
    have hW22fhigh : ∀ t, 23 + l < t →
        ((denseWord N 22).set 22 false).getD t false = false := by
      intro t ht
      rw [getD_set_ne _ _ _ _ (by omega)]
      exact hW22high t ht
    have hWilen : (denseWord N (23 + l)).length = N :=
      denseWord_length N (23 + l) (by omega) hlt
    have hWihigh : ∀ t, 23 + l < t → (denseWord N (23 + l)).getD t false = false :=
      fun t ht => denseWord_getD_high N (23 + l) t (by omega) (by omega)
    have hRlen : (List.replicate N false).length = N := List.length_replicate
    have hRhigh : ∀ t, 23 + l < t → (List.replicate N false).getD t false = false :=
      fun t _ => replicate_false_getD N t
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · -- f|₀ nonconstant
      refine ⟨(fun k : Fin N => (denseWord N 22).getD k.val false),
        (fun k : Fin N => ((denseWord N 22).set 22 false).getD k.val false), ?_⟩
      rw [hval _ hW22len hW22high false, hval _ hW22flen hW22fhigh false,
        SATLang_denseWord_set_high N 22 (23 + l) (le_refl _) (by omega) false,
        SATLang_denseWordFlip_set_high N 22 (23 + l) (le_refl _) (by omega) false]
      simp
    · -- f|₁ nonconstant
      refine ⟨(fun k : Fin N => (denseWord N 22).getD k.val false),
        (fun k : Fin N => ((denseWord N 22).set 22 false).getD k.val false), ?_⟩
      rw [hval _ hW22len hW22high true, hval _ hW22flen hW22fhigh true,
        SATLang_denseWord_set_high N 22 (23 + l) (le_refl _) (by omega) true,
        SATLang_denseWordFlip_set_high N 22 (23 + l) (le_refl _) (by omega) true]
      simp
    · -- the restrictions differ: the dense flip at 23+l
      intro heq
      have hc := congrFun heq (fun k : Fin N => (denseWord N (23 + l)).getD k.val false)
      rw [hval _ hWilen hWihigh true, hval _ hWilen hWihigh false,
        denseWord_set_true N (23 + l) (by omega), SATLang_denseWord N (23 + l) (by omega),
        SATLang_denseWord_set_self N (23 + l) (by omega)] at hc
      simp at hc
    · -- the restrictions are not complementary: the empty-formula completion
      intro heq
      have hc0 := congrFun heq (fun k : Fin N => (List.replicate N false).getD k.val false)
      have hc : restrictF g ⟨23 + l, hlt⟩ true
            (fun k : Fin N => (List.replicate N false).getD k.val false)
          = !(restrictF g ⟨23 + l, hlt⟩ false
            (fun k : Fin N => (List.replicate N false).getD k.val false)) := hc0
      rw [hval _ hRlen hRhigh true, hval _ hRlen hRhigh false,
        SATLang_replicate_set N (23 + l) (by omega) (by omega) true,
        SATLang_replicate_set N (23 + l) (by omega) (by omega) false] at hc
      simp at hc
    · -- the tail chain: the pin extends the mask by one position
      apply ih (by omega)
      intro x
      show g (Function.update x ⟨23 + l, hlt⟩ false) = _
      rw [hg]
      congr 1
      funext k
      by_cases hk21 : 22 + l < k.val
      · by_cases hk22 : 22 + (l + 1) < k.val
        · rw [if_pos hk22, if_pos hk21]
        · have hkv : k.val = 23 + l := by omega
          have hke : k = ⟨23 + l, hlt⟩ := Fin.ext hkv
          rw [if_neg hk22, if_pos hk21, hke, Function.update_self]
      · have hk22 : ¬ 22 + (l + 1) < k.val := by omega
        rw [if_neg hk22, if_neg hk21,
          Function.update_of_ne (fun he => by rw [he] at hk21; simp at hk21) false x]

/-- **THE FULL-LENGTH GUARDED CHAIN ON THE TARGET (proved).** -/
theorem SATFamily_guardedChain (N : ℕ) (hN : 23 ≤ N) :
    GuardedChain (SATFamily N) (descSteps' N (N - 23) (by omega)) := by
  apply guardedChain_desc
  intro x
  congr 1
  funext k
  rw [if_neg (by have := k.isLt; omega)]

/-- **The elimination floor (proved)**: `2(N − 23) ≤ cbudget (SATFamily N)` — the
`2n`-scale bound on the exact target by pure gate elimination, cone-free. -/
theorem cbudget_SATFamily_elimination (N : ℕ) (hN : 23 ≤ N) :
    2 * (N - 23) ≤ cbudget (SATFamily N) := by
  have h := cbudget_guardedchain (descSteps' N (N - 23) (by omega)) (SATFamily N)
    (SATFamily_guardedChain N hN)
  rwa [descSteps'_length] at h

end PallLean.Paper93.DeepMath.PathB.SATFamilyGuardedChain

#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyGuardedChain.SATFamily_guardedChain
#print axioms PallLean.Paper93.DeepMath.PathB.SATFamilyGuardedChain.cbudget_SATFamily_elimination
