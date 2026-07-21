import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKhrCeiling

/-!
# K3a of the multiplicative-recurrence engine: the block lift

Block composition and the lifted witness sets:

* `emb`/`blkOf`/`offOf` — the `Fin (m·b) ≃ Fin m × Fin b` codec (div/mod);
* `comp` — block composition `f ∘ g^m`;
* `blkSet` — the lift of an outer witness set `Y`: every `y ∈ Y` expanded by
  choosing a block vector from `Ag` (where `y j` is true) or `Bg` (false);
* **`blkSet_eval` (proved)** — lifted vectors evaluate through the gadget to
  exactly `f y`;
* **`blkSet_card` (proved)** — with balanced gadget witnesses
  (`|Ag| = |Bg| = s`, disjoint): `|blkSet Y| = |Y| · s^m`.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### The block codec -/

def emb {m b : ℕ} (hb : 0 < b) (j : Fin m) (i : Fin b) : Fin (m * b) :=
  ⟨b * j.val + i.val, by
    have hj := j.isLt
    have hi := i.isLt
    have h1 : b * (j.val + 1) ≤ b * m := Nat.mul_le_mul_left b hj
    have h2 : b * (j.val + 1) = b * j.val + b := by ring
    have h3 : b * m = m * b := Nat.mul_comm b m
    omega⟩

def blkOf {m b : ℕ} (hb : 0 < b) (i : Fin (m * b)) : Fin m :=
  ⟨i.val / b, by
    have h := i.isLt
    exact (Nat.div_lt_iff_lt_mul hb).mpr h⟩

def offOf {m b : ℕ} (hb : 0 < b) (i : Fin (m * b)) : Fin b :=
  ⟨i.val % b, Nat.mod_lt _ hb⟩

theorem blk_emb {m b : ℕ} (hb : 0 < b) (j : Fin m) (i : Fin b) :
    blkOf hb (emb hb j i) = j := by
  refine Fin.ext ?_
  show (b * j.val + i.val) / b = j.val
  rw [Nat.mul_add_div hb, Nat.div_eq_of_lt i.isLt]
  omega

theorem off_emb {m b : ℕ} (hb : 0 < b) (j : Fin m) (i : Fin b) :
    offOf hb (emb hb j i) = i := by
  refine Fin.ext ?_
  show (b * j.val + i.val) % b = i.val
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]

theorem emb_blk_off {m b : ℕ} (hb : 0 < b) (i : Fin (m * b)) :
    emb hb (blkOf hb i) (offOf hb i) = i := by
  refine Fin.ext ?_
  show b * (i.val / b) + i.val % b = i.val
  exact Nat.div_add_mod i.val b

/-- Block composition `f ∘ g^m`. -/
def comp {m b : ℕ} (hb : 0 < b) (f : (Fin m → Bool) → Bool)
    (g : (Fin b → Bool) → Bool) (z : Fin (m * b) → Bool) : Bool :=
  f (fun j => g (fun i => z (emb hb j i)))

/-! ### The lifted witness sets -/

/-- The lift of the outer witness set `Y` through gadget witnesses `Ag`/`Bg`. -/
noncomputable def blkSet {m b : ℕ} (hb : 0 < b) (Y : Finset (Fin m → Bool))
    (Ag Bg : Finset (Fin b → Bool)) : Finset (Fin (m * b) → Bool) :=
  (Y.sigma (fun y => Fintype.piFinset
      (fun j : Fin m => if y j = true then Ag else Bg))).image
    (fun p => fun i => p.2 (blkOf hb i) (offOf hb i))

theorem mem_blkSet_of {m b : ℕ} (hb : 0 < b) {Y : Finset (Fin m → Bool)}
    {Ag Bg : Finset (Fin b → Bool)} {y : Fin m → Bool}
    {w : Fin m → Fin b → Bool} (hy : y ∈ Y)
    (hw : ∀ j, w j ∈ (if y j = true then Ag else Bg)) :
    (fun i => w (blkOf hb i) (offOf hb i)) ∈ blkSet hb Y Ag Bg := by
  refine Finset.mem_image.mpr ⟨⟨y, w⟩, ?_, rfl⟩
  refine Finset.mem_sigma.mpr ⟨hy, ?_⟩
  exact Fintype.mem_piFinset.mpr hw

theorem blkSet_extract {m b : ℕ} (hb : 0 < b) {Y : Finset (Fin m → Bool)}
    {Ag Bg : Finset (Fin b → Bool)} {z : Fin (m * b) → Bool}
    (hz : z ∈ blkSet hb Y Ag Bg) :
    ∃ (y : Fin m → Bool) (w : Fin m → Fin b → Bool), y ∈ Y
      ∧ (∀ j, w j ∈ (if y j = true then Ag else Bg))
      ∧ (fun i => w (blkOf hb i) (offOf hb i)) = z := by
  obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hz
  obtain ⟨hp1, hp2⟩ := Finset.mem_sigma.mp hp
  exact ⟨p.1, p.2, hp1, Fintype.mem_piFinset.mp hp2, he⟩

/-- **The lift evaluates through the gadget (proved).** -/
theorem blkSet_eval {m b : ℕ} (hb : 0 < b) (f : (Fin m → Bool) → Bool)
    (g : (Fin b → Bool) → Bool) {Y : Finset (Fin m → Bool)}
    {Ag Bg : Finset (Fin b → Bool)} (c : Bool)
    (hAg : ∀ u ∈ Ag, g u = true) (hBg : ∀ u ∈ Bg, g u = false)
    (hY : ∀ y ∈ Y, f y = c) :
    ∀ z ∈ blkSet hb Y Ag Bg, comp hb f g z = c := by
  intro z hz
  obtain ⟨y, w, hy, hw, he⟩ := blkSet_extract hb hz
  subst he
  show f (fun j => g (fun i =>
    w (blkOf hb (emb hb j i)) (offOf hb (emb hb j i)))) = c
  have hbl : (fun j => g (fun i =>
      w (blkOf hb (emb hb j i)) (offOf hb (emb hb j i)))) = y := by
    funext j
    have hwi : (fun i => w (blkOf hb (emb hb j i)) (offOf hb (emb hb j i)))
        = w j := by
      funext i
      rw [blk_emb, off_emb]
    rw [hwi]
    have hj := hw j
    by_cases hyj : y j = true
    · rw [if_pos hyj] at hj
      rw [hAg _ hj, hyj]
    · rw [if_neg hyj] at hj
      rw [hBg _ hj]
      cases h : y j
      · rfl
      · exact absurd h hyj
  rw [hbl]
  exact hY y hy

/-- **The lift multiplies the cardinality (proved)**: `|Y| · s^m`. -/
theorem blkSet_card {m b : ℕ} (hb : 0 < b) (Y : Finset (Fin m → Bool))
    (Ag Bg : Finset (Fin b → Bool)) (hdisj : Disjoint Ag Bg)
    (s : ℕ) (hAgs : Ag.card = s) (hBgs : Bg.card = s) :
    (blkSet hb Y Ag Bg).card = Y.card * s ^ m := by
  classical
  rw [blkSet, Finset.card_image_of_injOn, Finset.card_sigma]
  · have hpi : ∀ y ∈ Y, (Fintype.piFinset
        (fun j : Fin m => if y j = true then Ag else Bg)).card = s ^ m := by
      intro y _
      rw [Fintype.card_piFinset]
      have hfac : ∀ j : Fin m, ((if y j = true then Ag else Bg)).card = s := by
        intro j
        by_cases h : y j = true
        · rw [if_pos h]
          exact hAgs
        · rw [if_neg h]
          exact hBgs
      rw [Finset.prod_congr rfl (fun j _ => hfac j), Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_congr rfl hpi, Finset.sum_const, smul_eq_mul]
  · rintro ⟨y, w⟩ hp ⟨y', w'⟩ hq he
    have hp' := Finset.mem_sigma.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_sigma.mp (Finset.mem_coe.mp hq)
    have hwmem : ∀ j, w j ∈ (if y j = true then Ag else Bg) :=
      Fintype.mem_piFinset.mp hp'.2
    have hwmem' : ∀ j, w' j ∈ (if y' j = true then Ag else Bg) :=
      Fintype.mem_piFinset.mp hq'.2
    have hww : w = w' := by
      funext j i
      have h1 := congrFun he (emb hb j i)
      have h2 : w (blkOf hb (emb hb j i)) (offOf hb (emb hb j i))
          = w' (blkOf hb (emb hb j i)) (offOf hb (emb hb j i)) := h1
      rw [blk_emb, off_emb] at h2
      exact h2
    have hyy : y = y' := by
      funext j
      by_cases h1 : y j = true
      · by_cases h2 : y' j = true
        · rw [h1, h2]
        · exfalso
          have ha := hwmem j
          have hb' := hwmem' j
          rw [if_pos h1] at ha
          rw [if_neg h2, ← hww] at hb'
          exact Finset.disjoint_left.mp hdisj ha hb'
      · by_cases h2 : y' j = true
        · exfalso
          have ha := hwmem j
          have hb' := hwmem' j
          rw [if_neg h1] at ha
          rw [if_pos h2, ← hww] at hb'
          exact Finset.disjoint_left.mp hdisj hb' ha
        · cases hv1 : y j
          · cases hv2 : y' j
            · rfl
            · exact absurd hv2 h2
          · exact absurd hv1 h1
    subst hww
    subst hyy
    rfl

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.blkSet_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.blkSet_card
