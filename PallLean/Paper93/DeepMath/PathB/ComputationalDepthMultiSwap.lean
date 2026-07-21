import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSlotCount

/-!
# Brick D of the ∀m `SlackComposes` campaign: the simultaneous swap

Swapping *every* reconvergence wire for the value it carries leaves the run
unchanged, and the swapped circuit sees only variables with clean paths:

* `swapG` / `runFrom_swapG` — the general single swap preserves the whole run
  (not just the output) when fed the true wire value;
* `multiSwap` / `runFrom_multiSwap` — folded over any duplicate-free list of
  in-range positions;
* `CleanIn` / `multiSwap_cone_clean` — a cone derivation of the multi-swapped
  circuit is literally a reconvergence-free path of the original;
* **`multiSwap_blind` (proved)** — if no var gate of `i` is reachable through
  reconvergence-free paths, the multi-swapped circuit is blind to `i`.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-! ### The general single swap -/

/-- Replace the gate at position `s` by a constant. -/
def swapG {n : ℕ} (c : List (CGate n)) (s : ℕ) (w : Bool) : List (CGate n) :=
  c.take s ++ CGate.cst w :: c.drop (s + 1)

theorem swapG_length {n : ℕ} (c : List (CGate n)) (s : ℕ) (w : Bool)
    (hs : s < c.length) : (swapG c s w).length = c.length := by
  rw [swapG]
  simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
  omega

theorem swapG_getD_self {n : ℕ} {c : List (CGate n)} {s : ℕ} (hs : s < c.length)
    (w : Bool) : (swapG c s w).getD s (.cst false) = CGate.cst w := by
  rw [swapG, List.getD_append_right _ _ (CGate.cst false) s
    (by rw [List.length_take]; omega),
    show s - (c.take s).length = 0 from by rw [List.length_take]; omega]
  rfl

theorem swapG_getD_ne {n : ℕ} {c : List (CGate n)} {s : ℕ} (hs : s < c.length)
    (w : Bool) {q : ℕ} (hq : q ≠ s) :
    (swapG c s w).getD q (.cst false) = c.getD q (.cst false) := by
  rcases Nat.lt_or_ge q s with h | h
  · rw [swapG, List.getD_append _ _ (CGate.cst false) q
      (by rw [List.length_take]; omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt h]
  · have h' : s < q := by omega
    rw [swapG, List.getD_append_right _ _ (CGate.cst false) q
      (by rw [List.length_take]; omega),
      show q - (c.take s).length = (q - s - 1) + 1 from by rw [List.length_take]; omega]
    show (c.drop (s + 1)).getD (q - s - 1) (.cst false) = c.getD q (.cst false)
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
      show s + 1 + (q - s - 1) = q from by omega]

/-- **The single swap at the true wire value preserves the whole run (proved).** -/
theorem runFrom_swapG {n : ℕ} (c : List (CGate n)) {s : ℕ} (hs : s < c.length)
    (x : Fin n → Bool) :
    runFrom x [] (swapG c s (wire c x s)) = runFrom x [] c := by
  have hsplit := split_at_getD c hs
  conv_rhs => rw [hsplit]
  show runFrom x [] (c.take s ++ CGate.cst (wire c x s) :: c.drop (s + 1))
    = runFrom x [] (c.take s ++ c.getD s (.cst false) :: c.drop (s + 1))
  rw [runFrom_append, runFrom_append]
  show runFrom x (runFrom x [] (c.take s)
      ++ [evalGate x (runFrom x [] (c.take s)) (CGate.cst (wire c x s))])
      (c.drop (s + 1))
    = runFrom x (runFrom x [] (c.take s)
      ++ [evalGate x (runFrom x [] (c.take s)) (c.getD s (.cst false))])
      (c.drop (s + 1))
  rw [show evalGate x (runFrom x [] (c.take s)) (CGate.cst (wire c x s))
    = evalGate x (runFrom x [] (c.take s)) (c.getD s (.cst false)) from wire_eq c x hs]

/-! ### The simultaneous swap -/

/-- Swap every position in the list for its prescribed constant. -/
def multiSwap {n : ℕ} (c : List (CGate n)) (w : ℕ → Bool) : List ℕ → List (CGate n)
  | [] => c
  | s :: rest => swapG (multiSwap c w rest) s (w s)

theorem multiSwap_length {n : ℕ} (c : List (CGate n)) (w : ℕ → Bool)
    (l : List ℕ) (hl : ∀ s ∈ l, s < c.length) :
    (multiSwap c w l).length = c.length := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    have hrest : ∀ s' ∈ rest, s' < c.length := fun s' hs' => hl s' (by simp [hs'])
    show (swapG (multiSwap c w rest) s (w s)).length = c.length
    rw [swapG_length _ _ _ (by rw [ih hrest]; exact hl s (by simp)), ih hrest]

theorem multiSwap_getD_notmem {n : ℕ} (c : List (CGate n)) (w : ℕ → Bool)
    (l : List ℕ) (hl : ∀ s ∈ l, s < c.length) {q : ℕ} (hq : q ∉ l) :
    (multiSwap c w l).getD q (.cst false) = c.getD q (.cst false) := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    have hrest : ∀ s' ∈ rest, s' < c.length := fun s' hs' => hl s' (by simp [hs'])
    have hqs : q ≠ s := fun he => hq (by rw [he]; exact List.mem_cons_self)
    have hqrest : q ∉ rest := fun hmem => hq (List.mem_cons_of_mem s hmem)
    show (swapG (multiSwap c w rest) s (w s)).getD q (.cst false) = _
    rw [swapG_getD_ne (by rw [multiSwap_length c w rest hrest]; exact hl s (by simp))
      (w s) hqs]
    exact ih hrest hqrest

theorem multiSwap_getD_mem {n : ℕ} (c : List (CGate n)) (w : ℕ → Bool)
    (l : List ℕ) (hl : ∀ s ∈ l, s < c.length) (hnd : l.Nodup) {q : ℕ} (hq : q ∈ l) :
    (multiSwap c w l).getD q (.cst false) = CGate.cst (w q) := by
  induction l with
  | nil => exact absurd hq (by simp)
  | cons s rest ih =>
    have hrest : ∀ s' ∈ rest, s' < c.length := fun s' hs' => hl s' (by simp [hs'])
    have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hsnr : s ∉ rest := (List.nodup_cons.mp hnd).1
    show (swapG (multiSwap c w rest) s (w s)).getD q (.cst false) = _
    rcases List.mem_cons.mp hq with he | hmem
    · rw [he]
      rw [swapG_getD_self (by rw [multiSwap_length c w rest hrest]; exact hl s (by simp))
        (w s)]
    · have hqs : q ≠ s := fun he' => hsnr (he' ▸ hmem)
      rw [swapG_getD_ne (by rw [multiSwap_length c w rest hrest]; exact hl s (by simp))
        (w s) hqs]
      exact ih hrest hnd' hmem

/-- **The simultaneous swap at the true wire values preserves the run (proved).** -/
theorem runFrom_multiSwap {n : ℕ} (c : List (CGate n)) (x : Fin n → Bool)
    (l : List ℕ) (hl : ∀ s ∈ l, s < c.length) :
    runFrom x [] (multiSwap c (fun u => wire c x u) l) = runFrom x [] c := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
    have hrest : ∀ s' ∈ rest, s' < c.length := fun s' hs' => hl s' (by simp [hs'])
    have hIH := ih hrest
    have hlen : (multiSwap c (fun u => wire c x u) rest).length = c.length :=
      multiSwap_length c _ rest hrest
    have hwire : wire (multiSwap c (fun u => wire c x u) rest) x s = wire c x s := by
      rw [wire, wire, hIH]
    show runFrom x [] (swapG (multiSwap c (fun u => wire c x u) rest) s
      (wire c x s)) = runFrom x [] c
    rw [← hwire,
      runFrom_swapG (multiSwap c (fun u => wire c x u) rest)
        (by rw [hlen]; exact hl s (by simp)) x]
    exact hIH

theorem output_multiSwap {n : ℕ} (c : List (CGate n)) (x : Fin n → Bool)
    (l : List ℕ) (hl : ∀ s ∈ l, s < c.length) :
    output (multiSwap c (fun u => wire c x u) l) x = output c x := by
  show (runFrom x [] (multiSwap c (fun u => wire c x u) l)).getD
    ((multiSwap c (fun u => wire c x u) l).length - 1) false = output c x
  rw [runFrom_multiSwap c x l hl, multiSwap_length c _ l hl]
  rfl

/-! ### Clean paths -/

/-- Cone reachability through readers avoiding `R`. -/
inductive CleanIn (c : List (CGate n)) (R : Finset ℕ) : ℕ → Prop
  | root : CleanIn c R (c.length - 1)
  | step {w j : ℕ} : CleanIn c R w → w ∉ R →
      j ∈ gateReads (c.getD w (.cst false)) → j < w → CleanIn c R j

/-- Membership facts for the reconvergence set. -/
theorem mem_reconvR {n : ℕ} {c : List (CGate n)} {q : ℕ} (hq : q ∈ reconvR c) :
    q < c.length ∧ q ≠ c.length - 1 ∧ 2 ≤ slotReads c q := by
  rw [reconvR, Finset.mem_filter, Finset.mem_erase] at hq
  exact ⟨(mem_cone.mp hq.1.2).1, hq.1.1, hq.2⟩

/-- **A multi-swapped cone derivation is a clean path (proved).** -/
theorem multiSwap_cone_clean {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    (w : ℕ → Bool) :
    ∀ q, InCone (multiSwap c w (reconvR c).toList) q → CleanIn c (reconvR c) q := by
  have hl : ∀ s ∈ (reconvR c).toList, s < c.length := fun s hsm =>
    (mem_reconvR (Finset.mem_toList.mp hsm)).1
  have hlen : (multiSwap c w (reconvR c).toList).length = c.length :=
    multiSwap_length c w _ hl
  intro q hq
  induction hq with
  | root =>
    rw [hlen]
    exact CleanIn.root
  | step hw' ht hlt ih =>
    rename_i w' t
    by_cases hwR : w' ∈ reconvR c
    · rw [multiSwap_getD_mem c w _ hl (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hwR)] at ht
      exact absurd ht (by simp [gateReads])
    · rw [multiSwap_getD_notmem c w _ hl
        (fun hmem => hwR (Finset.mem_toList.mp hmem))] at ht
      exact CleanIn.step ih hwR ht hlt

/-- **Blindness of the multi-swapped circuit (proved)**: no cleanly-reachable
var gate of `i` means the swapped circuit cannot see `i`. -/
theorem multiSwap_blind {n : ℕ} (c : List (CGate n)) (hs : 0 < c.length)
    (w : ℕ → Bool) (i : Fin n)
    (hnc : ∀ q, CleanIn c (reconvR c) q → c.getD q (.cst false) ≠ CGate.var i)
    (x : Fin n → Bool) (b : Bool) :
    output (multiSwap c w (reconvR c).toList) (Function.update x i b)
      = output (multiSwap c w (reconvR c).toList) x := by
  have hl : ∀ s ∈ (reconvR c).toList, s < c.length := fun s hsm =>
    (mem_reconvR (Finset.mem_toList.mp hsm)).1
  have hlen : (multiSwap c w (reconvR c).toList).length = c.length :=
    multiSwap_length c w _ hl
  have hnv : ∀ w', InCone (multiSwap c w (reconvR c).toList) w' →
      (multiSwap c w (reconvR c).toList).getD w' (.cst false) ≠ CGate.var i := by
    intro w' hw' hg
    by_cases hwR : w' ∈ reconvR c
    · rw [multiSwap_getD_mem c w _ hl (Finset.nodup_toList _)
        (Finset.mem_toList.mpr hwR)] at hg
      simp at hg
    · rw [multiSwap_getD_notmem c w _ hl
        (fun hmem => hwR (Finset.mem_toList.mp hmem))] at hg
      exact hnc w' (multiSwap_cone_clean c hs w w' hw') hg
  rw [output_eq_wire, output_eq_wire]
  exact cone_wire_agree (multiSwap c w (reconvR c).toList) i x b (by omega) hnv
    _ InCone.root

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.runFrom_multiSwap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.multiSwap_blind
