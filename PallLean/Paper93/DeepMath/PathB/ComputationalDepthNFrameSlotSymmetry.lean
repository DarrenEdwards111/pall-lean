import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSelectorData

/-!
# N-Frame: slot symmetry — transporting the drag arsenal to all three slots

The final balance count cannot close on slot-0 drags alone: a cut living entirely in the slot-1/2
region satisfies every slot-0 constraint vacuously.  The repair is a symmetry, not a rebuild:
swapping slot `0 ↔ t` inside every block is an **input permutation fixing `sat3Family`**, and a
cut factorization transports along any involutive invariance.  Every slot-0 drag therefore holds
at every slot, for free.

  `swapSlotNat` / `slotSwapBit` — the involutive bit permutation swapping slot chunks in each
        live block, fixing the tail.
  `sat3Family_slotSwap` — **PROVED, the invariance**: `sat3Family (x ∘ slotSwap) = sat3Family x`.
  `cut_transport` — **PROVED, the transport**: an involutive invariance of `f` carries
        `CutFactorization f S j` to `CutFactorization f (S.image σ) j`.
  `sat3_seldata_min_bound` — **PROVED, the mirror min form**: per block, at most `j` slot-0
        selectors inside `S` or at most `j` pin signs outside `S`.
  `sat3_min_bound_slot` / `sat3_seldata_bound_slot` — **PROVED, the all-slot drags**: both min
        forms at every slot `t`, by transport.

## Honest scope

These are the per-block constraints the final balance count consumes; the count itself is the
next file.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The slot swap -/

/-- The slot-index swap `0 ↔ t`, fixing the third index. -/
def swapSlotNat (t s : ℕ) : ℕ := if s = 0 then t else if s = t then 0 else s

theorem swapSlotNat_invol (t s : ℕ) : swapSlotNat t (swapSlotNat t s) = s := by
  unfold swapSlotNat
  split_ifs <;> omega

theorem swapSlotNat_lt (t s : ℕ) (ht : t < 3) (hs : s < 3) : swapSlotNat t s < 3 := by
  unfold swapSlotNat
  split_ifs <;> omega

/-- The slot swap as a map on `Fin 3`. -/
def swapSlotF (t s : Fin 3) : Fin 3 :=
  ⟨swapSlotNat t.val s.val, swapSlotNat_lt _ _ t.isLt s.isLt⟩

theorem swapSlotF_invol (t s : Fin 3) : swapSlotF t (swapSlotF t s) = s :=
  Fin.ext (swapSlotNat_invol t.val s.val)

theorem swapSlotF_zero (t : Fin 3) (h0 : (0 : ℕ) < 3) : swapSlotF t ⟨0, h0⟩ = t := by
  apply Fin.ext
  show swapSlotNat t.val 0 = t.val
  unfold swapSlotNat
  rw [if_pos rfl]

theorem slotSwapBit_lt (N : ℕ) (t : Fin 3) (b : Fin N)
    (hb : b.val / sat3D N < sat3M N) :
    b.val / sat3D N * sat3D N
      + swapSlotNat t.val (b.val % sat3D N / (sat3V N + 1)) * (sat3V N + 1)
      + b.val % sat3D N % (sat3V N + 1) < N := by
  have hD : sat3D N = 3 * (sat3V N + 1) := rfl
  have hs : b.val % sat3D N / (sat3V N + 1) < 3 := by
    apply Nat.div_lt_of_lt_mul
    have := Nat.mod_lt b.val (sat3D_pos N)
    omega
  have hsw : swapSlotNat t.val (b.val % sat3D N / (sat3V N + 1)) < 3 :=
    swapSlotNat_lt _ _ t.isLt hs
  have hf : b.val % sat3D N % (sat3V N + 1) < sat3V N + 1 :=
    Nat.mod_lt _ (by omega)
  have h1 : swapSlotNat t.val (b.val % sat3D N / (sat3V N + 1)) * (sat3V N + 1)
      ≤ 2 * (sat3V N + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : (b.val / sat3D N + 1) * sat3D N ≤ sat3M N * sat3D N :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : sat3M N * sat3D N ≤ N := Nat.div_mul_le_self N (sat3D N)
  have h4 : (b.val / sat3D N + 1) * sat3D N = b.val / sat3D N * sat3D N + sat3D N := by
    rw [Nat.succ_mul]
  omega

/-- The bit-level slot swap: swap the slot-`0` and slot-`t` chunks in every live block, fix the
tail. -/
def slotSwapBit (N : ℕ) (t : Fin 3) (b : Fin N) : Fin N :=
  if hb : b.val / sat3D N < sat3M N then
    ⟨b.val / sat3D N * sat3D N
      + swapSlotNat t.val (b.val % sat3D N / (sat3V N + 1)) * (sat3V N + 1)
      + b.val % sat3D N % (sat3V N + 1), slotSwapBit_lt N t b hb⟩
  else b

/-- The swap's action on layout bits: it moves slot `s` to slot `swapSlotF t s`, same field. -/
theorem slotSwapBit_bit (N : ℕ) (t : Fin 3) (c : Fin (sat3M N)) (s : Fin 3)
    (f : ℕ) (hf : f < sat3V N + 1) :
    slotSwapBit N t (sat3Bit N c s f hf) = sat3Bit N c (swapSlotF t s) f hf := by
  have hdiv : (sat3Bit N c s f hf).val / sat3D N = c.val := sat3Bit_clause N c s f hf
  have hrem : (sat3Bit N c s f hf).val % sat3D N = s.val * (sat3V N + 1) + f :=
    sat3Bit_rem N c s f hf
  have hcond : (sat3Bit N c s f hf).val / sat3D N < sat3M N := by
    rw [hdiv]
    exact c.isLt
  have hslot : (sat3Bit N c s f hf).val % sat3D N / (sat3V N + 1) = s.val := by
    rw [hrem, Nat.mul_comm s.val (sat3V N + 1), Nat.mul_add_div (by omega),
      Nat.div_eq_of_lt hf]
    omega
  have hfield : (sat3Bit N c s f hf).val % sat3D N % (sat3V N + 1) = f := by
    rw [hrem, Nat.mul_comm s.val (sat3V N + 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hf]
  unfold slotSwapBit
  rw [dif_pos hcond]
  apply Fin.ext
  show (sat3Bit N c s f hf).val / sat3D N * sat3D N
      + swapSlotNat t.val ((sat3Bit N c s f hf).val % sat3D N / (sat3V N + 1))
        * (sat3V N + 1)
      + (sat3Bit N c s f hf).val % sat3D N % (sat3V N + 1)
    = c.val * sat3D N + (swapSlotF t s).val * (sat3V N + 1) + f
  rw [hdiv, hslot, hfield]
  rfl

theorem slotSwapBit_invol (N : ℕ) (t : Fin 3) (b : Fin N) :
    slotSwapBit N t (slotSwapBit N t b) = b := by
  by_cases hb : b.val / sat3D N < sat3M N
  · have hvpos : 0 < sat3V N + 1 := by omega
    have hs : b.val % sat3D N / (sat3V N + 1) < 3 := by
      apply Nat.div_lt_of_lt_mul
      have := Nat.mod_lt b.val (sat3D_pos N)
      have hD : sat3D N = 3 * (sat3V N + 1) := rfl
      omega
    have hrep : b = sat3Bit N ⟨b.val / sat3D N, hb⟩
        ⟨b.val % sat3D N / (sat3V N + 1), hs⟩
        (b.val % sat3D N % (sat3V N + 1)) (Nat.mod_lt _ hvpos) := by
      apply Fin.ext
      show b.val = b.val / sat3D N * sat3D N
        + b.val % sat3D N / (sat3V N + 1) * (sat3V N + 1)
        + b.val % sat3D N % (sat3V N + 1)
      have h1 : sat3D N * (b.val / sat3D N) + b.val % sat3D N = b.val :=
        Nat.div_add_mod _ _
      have h2 : (sat3V N + 1) * (b.val % sat3D N / (sat3V N + 1))
          + b.val % sat3D N % (sat3V N + 1) = b.val % sat3D N :=
        Nat.div_add_mod _ _
      have h3 : sat3D N * (b.val / sat3D N) = b.val / sat3D N * sat3D N :=
        Nat.mul_comm _ _
      have h4 : (sat3V N + 1) * (b.val % sat3D N / (sat3V N + 1))
          = b.val % sat3D N / (sat3V N + 1) * (sat3V N + 1) := Nat.mul_comm _ _
      omega
    rw [hrep, slotSwapBit_bit, slotSwapBit_bit, swapSlotF_invol]
  · have h1 : slotSwapBit N t b = b := by
      unfold slotSwapBit
      rw [dif_neg hb]
    rw [h1, h1]

/-! ### Invariance of the family -/

/-- Boolean equality from a truth-value equivalence. -/
theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b
  · rfl
  · exact h.mpr rfl
  · exact (h.mp rfl).symm
  · rfl

theorem sat3Lit_slotSwap (N : ℕ) (t : Fin 3) (x : Fin N → Bool)
    (a : Fin (sat3V N) → Bool) (c : Fin (sat3M N)) (s : Fin 3) :
    sat3Lit N (fun i => x (slotSwapBit N t i)) a c s
      = sat3Lit N x a c (swapSlotF t s) := by
  unfold sat3Lit
  congr 1
  funext i
  show (x (slotSwapBit N t (sat3Bit N c s i.val (by have := i.isLt; omega)))
      && xor (a i) (x (slotSwapBit N t (sat3Bit N c s (sat3V N) (by omega)))))
    = (x (sat3Bit N c (swapSlotF t s) i.val (by have := i.isLt; omega))
      && xor (a i) (x (sat3Bit N c (swapSlotF t s) (sat3V N) (by omega))))
  rw [slotSwapBit_bit, slotSwapBit_bit]

theorem sat3Eval_slotSwap (N : ℕ) (t : Fin 3) (x : Fin N → Bool)
    (a : Fin (sat3V N) → Bool) :
    sat3Eval N (fun i => x (slotSwapBit N t i)) a = sat3Eval N x a := by
  unfold sat3Eval
  congr 1
  funext c
  apply bool_eq_of_iff
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨s, -, hs⟩
    refine ⟨swapSlotF t s, List.mem_finRange _, ?_⟩
    rw [sat3Lit_slotSwap] at hs
    exact hs
  · rintro ⟨s, -, hs⟩
    refine ⟨swapSlotF t s, List.mem_finRange _, ?_⟩
    rw [sat3Lit_slotSwap, swapSlotF_invol]
    exact hs

/-- **THE INVARIANCE (proved)**: the SAT family is fixed by every slot swap. -/
theorem sat3Family_slotSwap (N : ℕ) (t : Fin 3) (x : Fin N → Bool) :
    sat3Family N (fun i => x (slotSwapBit N t i)) = sat3Family N x := by
  unfold sat3Family
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← sat3Eval_slotSwap N t x a]
    exact ha
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [sat3Eval_slotSwap]
    exact ha

/-! ### Transport of cut factorizations -/

theorem mem_image_invol {n : ℕ} (σ : Fin n → Fin n) (hinv : ∀ b, σ (σ b) = b)
    (S : Finset (Fin n)) (b : Fin n) : b ∈ S.image σ ↔ σ b ∈ S := by
  constructor
  · intro hb
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hb
    rw [hinv]
    exact hs
  · intro hb
    exact Finset.mem_image.mpr ⟨σ b, hb, hinv b⟩

/-- **THE TRANSPORT (proved)**: an involutive input invariance of `f` carries a cut factorization
over `S` to one over `S.image σ` with the same trace. -/
theorem cut_transport {n : ℕ} (f : (Fin n → Bool) → Bool) (σ : Fin n → Fin n)
    (hinv : ∀ b, σ (σ b) = b)
    (hf : ∀ x : Fin n → Bool, f (fun i => x (σ i)) = f x)
    {S : Finset (Fin n)} {j : ℕ} (hcut : CutFactorization f S j) :
    CutFactorization f (S.image σ) j := by
  classical
  obtain ⟨φ, hφS, hφsep⟩ := hcut
  refine ⟨fun y => φ (fun i => y (σ i)), ?_, ?_⟩
  · intro x y hxy
    apply hφS
    intro i hi
    exact hxy (σ i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · intro x y y' hyy
    have hmix : ∀ z w : Fin n → Bool,
        (fun i => mixOn (S.image σ)ᶜ z w (σ i))
          = mixOn Sᶜ (fun i => z (σ i)) (fun i => w (σ i)) := by
      intro z w
      funext i
      show (if σ i ∈ (S.image σ)ᶜ then z (σ i) else w (σ i))
        = (if i ∈ Sᶜ then z (σ i) else w (σ i))
      by_cases hi : i ∈ S
      · rw [if_neg (fun hmem => (Finset.mem_compl.mp hmem)
            (Finset.mem_image.mpr ⟨i, hi, rfl⟩)),
          if_neg (fun hmem => (Finset.mem_compl.mp hmem) hi)]
      · rw [if_pos ?_, if_pos (Finset.mem_compl.mpr hi)]
        apply Finset.mem_compl.mpr
        intro hmem
        obtain ⟨s, hs, hsi⟩ := Finset.mem_image.mp hmem
        have hseq : s = i := by
          have h1 := congrArg σ hsi
          rw [hinv, hinv] at h1
          exact h1
        rw [hseq] at hs
        exact hi hs
    calc f (mixOn (S.image σ)ᶜ x y)
        = f (fun i => mixOn (S.image σ)ᶜ x y (σ i)) := (hf _).symm
      _ = f (mixOn Sᶜ (fun i => x (σ i)) (fun i => y (σ i))) := by rw [hmix]
      _ = f (mixOn Sᶜ (fun i => x (σ i)) (fun i => y' (σ i))) := hφsep _ _ _ hyy
      _ = f (fun i => mixOn (S.image σ)ᶜ x y' (σ i)) := by rw [hmix]
      _ = f (mixOn (S.image σ)ᶜ x y') := hf _

/-! ### The mirror min form at slot 0 -/

/-- **THE MIRROR MIN FORM (proved)**: per block, at most `j` slot-0 selectors inside `S` or at
most `j` pin signs outside `S` — the selector-data drag's per-block cash-out. -/
theorem sat3_seldata_min_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j) (c : Fin (sat3M N)) :
    ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ j
    ∨ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ S)).card ≤ j := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨hin, hout⟩ := hcon
  obtain ⟨P', hP'sub, hP'card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ S)) (n := j + 1) (by omega)
  obtain ⟨V', hV'sub, hV'card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
    (n := j + 1) (by omega)
  obtain ⟨α, hαinj, hαmap, hαstrict⟩ := exists_injection_mapping_strict hkv P' V'
    (by rw [hP'card, hV'card])
  have himg : P'.image α = V' := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      exact hαmap p hp
    · rw [Finset.card_image_of_injective _ hαinj, hP'card, hV'card]
  have hdrag := sat3_selector_data_drag N hv hk hcut c α hαinj V'
    (fun w hw => (Finset.mem_filter.mp (hV'sub hw)).2)
    (fun w hw => by
      have hmem : w ∈ P'.image α := by
        rw [himg]
        exact hw
      obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hmem
      exact ⟨p, hp⟩)
    (fun p hp => by
      have hpP' : p ∈ P' := by
        by_contra hnp
        exact hαstrict p hnp hp
      exact (Finset.mem_filter.mp (hP'sub hpP')).2)
  omega

/-! ### The all-slot drags -/

/-- **THE ALL-SLOT MIN FORM (proved)**: per block and per slot `t`, at most `j` slot-`t` pin
signs inside `S` or at most `j` slot-`t` selectors outside `S`. -/
theorem sat3_min_bound_slot (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (c : Fin (sat3M N)) (t : Fin 3) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N (sat3PinClause N c hk p) t (sat3V N) (by omega) ∈ S)).card ≤ j
    ∨ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c t w.val (by have := w.isLt; omega) ∉ S)).card ≤ j := by
  classical
  have hcut' : CutFactorization (sat3Family N) (S.image (slotSwapBit N t)) j :=
    cut_transport (sat3Family N) (slotSwapBit N t) (slotSwapBit_invol N t)
      (sat3Family_slotSwap N t) hcut
  rcases sat3_pin_selector_min_bound N hv hk hcut' c with h | h
  · left
    have heq : ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
        sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∈ S.image (slotSwapBit N t)))
        = ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
        sat3Bit N (sat3PinClause N c hk p) t (sat3V N) (by omega) ∈ S)) := by
      apply Finset.filter_congr
      intro p _
      rw [mem_image_invol _ (slotSwapBit_invol N t), slotSwapBit_bit, swapSlotF_zero]
    rw [heq] at h
    exact h
  · right
    have heq : ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)
          ∉ S.image (slotSwapBit N t)))
        = ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c t w.val (by have := w.isLt; omega) ∉ S)) := by
      apply Finset.filter_congr
      intro w _
      apply not_congr
      rw [mem_image_invol _ (slotSwapBit_invol N t), slotSwapBit_bit, swapSlotF_zero]
    rw [heq] at h
    exact h

/-- **THE ALL-SLOT MIRROR MIN FORM (proved)**: per block and per slot `t`, at most `j` slot-`t`
selectors inside `S` or at most `j` slot-`t` pin signs outside `S`. -/
theorem sat3_seldata_bound_slot (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (c : Fin (sat3M N)) (t : Fin 3) :
    ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)).card ≤ j
    ∨ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N (sat3PinClause N c hk p) t (sat3V N) (by omega) ∉ S)).card ≤ j := by
  classical
  have hcut' : CutFactorization (sat3Family N) (S.image (slotSwapBit N t)) j :=
    cut_transport (sat3Family N) (slotSwapBit N t) (slotSwapBit_invol N t)
      (sat3Family_slotSwap N t) hcut
  rcases sat3_seldata_min_bound N hv hk hcut' c with h | h
  · left
    have heq : ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega)
          ∈ S.image (slotSwapBit N t)))
        = ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
        sat3Bit N c t w.val (by have := w.isLt; omega) ∈ S)) := by
      apply Finset.filter_congr
      intro w _
      rw [mem_image_invol _ (slotSwapBit_invol N t), slotSwapBit_bit, swapSlotF_zero]
    rw [heq] at h
    exact h
  · right
    have heq : ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
        sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∉ S.image (slotSwapBit N t)))
        = ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
        sat3Bit N (sat3PinClause N c hk p) t (sat3V N) (by omega) ∉ S)) := by
      apply Finset.filter_congr
      intro p _
      apply not_congr
      rw [mem_image_invol _ (slotSwapBit_invol N t), slotSwapBit_bit, swapSlotF_zero]
    rw [heq] at h
    exact h

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Family_slotSwap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cut_transport
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_min_bound_slot
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_seldata_bound_slot
