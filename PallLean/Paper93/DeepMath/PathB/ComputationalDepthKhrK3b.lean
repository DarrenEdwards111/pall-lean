import PallLean.Paper93.DeepMath.PathB.ComputationalDepthKhrK3a

/-!
# K3b of the multiplicative-recurrence engine: THE MULTIPLICATIVE STEP

The edge lift and the recurrence.  An outer Hamming edge and a gadget Hamming
edge compose, with free choices on the agreeing blocks, into a lifted Hamming
edge — injectively:

* `zblk`/`zblk'` — the lifted pair's block families;
* **`zblk_edge` (proved)** — the lifted pair IS a Hamming edge (the flip sits
  at `emb j₀ i₀`; the reversed direction uses the flip involution);
* **`edge_lift_card` (proved)** — `|E_f| · |E_g| · s^(m−1) ≤ |E_h|`;
* **`khr_comp_mul` (proved, K3)** — THE MULTIPLICATIVE RECURRENCE:
  for every DeMorgan tree computing `f ∘ g^m` and balanced gadget witnesses,
  `|E_f|² · |E_g|² ≤ lsize · (|A_f||B_f|) · (|A_g||B_g|)` —
  cross-multiplied `Q(f)·Q(g) ≤ L(f∘g^m)`.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

/-! ### Helpers -/

theorem update_flip_symm {n : ℕ} {u u' : Fin n → Bool} {i : Fin n}
    (h : u' = Function.update u i (!(u i))) :
    u = Function.update u' i (!(u' i)) := by
  rw [h]
  exact (flip_flip u i).symm

theorem assembled_at {m b : ℕ} (hb : 0 < b) (W : Fin m → Fin b → Bool)
    (j₀ : Fin m) (i₀ : Fin b) :
    (fun i => W (blkOf hb i) (offOf hb i)) (emb hb j₀ i₀) = W j₀ i₀ := by
  show W (blkOf hb (emb hb j₀ i₀)) (offOf hb (emb hb j₀ i₀)) = W j₀ i₀
  rw [blk_emb, off_emb]

theorem update_flip_ne {n : ℕ} (y : Fin n → Bool) (j₀ : Fin n) :
    y j₀ ≠ Function.update y j₀ (!(y j₀)) j₀ := by
  rw [Function.update_self]
  cases h : y j₀ <;> simp

theorem disagree_singleton {n : ℕ} (y : Fin n → Bool) (j₀ : Fin n) :
    Finset.univ.filter
        (fun j => ¬ (y j = Function.update y j₀ (!(y j₀)) j)) = {j₀} := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hne
    by_contra hj
    exact hne (by rw [Function.update_of_ne hj])
  · intro hj
    subst hj
    exact update_flip_ne y j

theorem agree_card {n : ℕ} (y : Fin n → Bool) (j₀ : Fin n) :
    (Finset.univ.filter
        (fun j => y j = Function.update y j₀ (!(y j₀)) j)).card = n - 1 := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)))
    (fun j => y j = Function.update y j₀ (!(y j₀)) j)
  rw [disagree_singleton, Finset.card_singleton, Finset.card_univ,
    Fintype.card_fin] at h1
  have h0 : (0 : ℕ) < n := Fin.pos_iff_nonempty.mpr ⟨j₀⟩
  omega

/-! ### The lifted pair -/

def zblk {m b : ℕ} (e : (Fin m → Bool) × (Fin m → Bool))
    (eg : (Fin b → Bool) × (Fin b → Bool)) (w : Fin m → Fin b → Bool)
    (j : Fin m) : Fin b → Bool :=
  if e.1 j = e.2 j then w j else (if e.1 j = true then eg.1 else eg.2)

def zblk' {m b : ℕ} (e : (Fin m → Bool) × (Fin m → Bool))
    (eg : (Fin b → Bool) × (Fin b → Bool)) (w : Fin m → Fin b → Bool)
    (j : Fin m) : Fin b → Bool :=
  if e.1 j = e.2 j then w j else (if e.2 j = true then eg.1 else eg.2)

/-- **The lifted pair is a Hamming edge (proved).** -/
theorem zblk_edge {m b : ℕ} (hb : 0 < b)
    (e : (Fin m → Bool) × (Fin m → Bool))
    (eg : (Fin b → Bool) × (Fin b → Bool)) (w : Fin m → Fin b → Bool)
    (j₀ : Fin m) (i₀ : Fin b)
    (he : e.2 = Function.update e.1 j₀ (!(e.1 j₀)))
    (hg : eg.2 = Function.update eg.1 i₀ (!(eg.1 i₀))) :
    (fun i => zblk' e eg w (blkOf hb i) (offOf hb i))
      = Function.update (fun i => zblk e eg w (blkOf hb i) (offOf hb i))
          (emb hb j₀ i₀) (!(zblk e eg w j₀ i₀)) := by
  have hne : ¬ (e.1 j₀ = e.2 j₀) := by
    intro h
    exact update_flip_ne e.1 j₀ (by rw [← he]; exact h)
  have hv2 : e.2 j₀ = !(e.1 j₀) := by rw [he, Function.update_self]
  funext i
  by_cases hbi : i = emb hb j₀ i₀
  · subst hbi
    rw [Function.update_self]
    show zblk' e eg w (blkOf hb (emb hb j₀ i₀)) (offOf hb (emb hb j₀ i₀))
      = !(zblk e eg w j₀ i₀)
    rw [blk_emb, off_emb]
    simp only [zblk, zblk']
    rw [if_neg hne, if_neg hne]
    by_cases h1 : e.1 j₀ = true
    · have h2 : e.2 j₀ = false := by rw [hv2, h1]; rfl
      rw [if_pos h1, if_neg (by rw [h2]; exact Bool.false_ne_true)]
      show eg.2 i₀ = !(eg.1 i₀)
      rw [hg, Function.update_self]
    · have h1' : e.1 j₀ = false := by
        cases h : e.1 j₀
        · rfl
        · exact absurd h h1
      have h2 : e.2 j₀ = true := by rw [hv2, h1']; rfl
      rw [if_neg h1, if_pos h2]
      show eg.1 i₀ = !(eg.2 i₀)
      rw [hg, Function.update_self, Bool.not_not]
  · rw [Function.update_of_ne hbi]
    show zblk' e eg w (blkOf hb i) (offOf hb i)
      = zblk e eg w (blkOf hb i) (offOf hb i)
    by_cases hjj : blkOf hb i = j₀
    · have hoff : offOf hb i ≠ i₀ := by
        intro h
        exact hbi (by rw [← emb_blk_off hb i, hjj, h])
      simp only [zblk, zblk']
      rw [hjj, if_neg hne, if_neg hne]
      by_cases h1 : e.1 j₀ = true
      · have h2 : e.2 j₀ = false := by rw [hv2, h1]; rfl
        rw [if_pos h1, if_neg (by rw [h2]; exact Bool.false_ne_true)]
        show eg.2 (offOf hb i) = eg.1 (offOf hb i)
        rw [hg, Function.update_of_ne hoff]
      · have h1' : e.1 j₀ = false := by
          cases h : e.1 j₀
          · rfl
          · exact absurd h h1
        have h2 : e.2 j₀ = true := by rw [hv2, h1']; rfl
        rw [if_neg h1, if_pos h2]
        show eg.1 (offOf hb i) = eg.2 (offOf hb i)
        rw [hg, Function.update_of_ne hoff]
    · have hag : e.1 (blkOf hb i) = e.2 (blkOf hb i) := by
        rw [he, Function.update_of_ne hjj]
      simp only [zblk, zblk']
      rw [if_pos hag, if_pos hag]

/-- Membership of the lifted first component. -/
theorem zblk_mem {m b : ℕ} {Ag Bg : Finset (Fin b → Bool)}
    (e : (Fin m → Bool) × (Fin m → Bool))
    (eg : (Fin b → Bool) × (Fin b → Bool)) (w : Fin m → Fin b → Bool)
    (heg1 : eg.1 ∈ Ag) (heg2 : eg.2 ∈ Bg)
    (hw : ∀ j, w j ∈ (if e.1 j = e.2 j
      then (if e.1 j = true then Ag else Bg)
      else ({fun _ => false} : Finset (Fin b → Bool)))) :
    ∀ j, zblk e eg w j ∈ (if e.1 j = true then Ag else Bg) := by
  intro j
  simp only [zblk]
  by_cases hag : e.1 j = e.2 j
  · rw [if_pos hag]
    have h := hw j
    rw [if_pos hag] at h
    exact h
  · rw [if_neg hag]
    by_cases h1 : e.1 j = true
    · rw [if_pos h1, if_pos h1]
      exact heg1
    · rw [if_neg h1, if_neg h1]
      exact heg2

/-- Membership of the lifted second component (against the flipped outer). -/
theorem zblk'_mem {m b : ℕ} {Ag Bg : Finset (Fin b → Bool)}
    (e : (Fin m → Bool) × (Fin m → Bool))
    (eg : (Fin b → Bool) × (Fin b → Bool)) (w : Fin m → Fin b → Bool)
    (heg1 : eg.1 ∈ Ag) (heg2 : eg.2 ∈ Bg)
    (hw : ∀ j, w j ∈ (if e.1 j = e.2 j
      then (if e.1 j = true then Ag else Bg)
      else ({fun _ => false} : Finset (Fin b → Bool)))) :
    ∀ j, zblk' e eg w j ∈ (if e.2 j = true then Ag else Bg) := by
  intro j
  simp only [zblk']
  by_cases hag : e.1 j = e.2 j
  · rw [if_pos hag]
    have h := hw j
    rw [if_pos hag, hag] at h
    exact h
  · rw [if_neg hag]
    by_cases h2 : e.2 j = true
    · rw [if_pos h2, if_pos h2]
      exact heg1
    · rw [if_neg h2, if_neg h2]
      exact heg2

/-- **The edge lift is injective and counts (proved)**:
`|E_f| · (|E_g| · s^(m−1)) ≤ |E_h|`. -/
theorem edge_lift_card {m b : ℕ} (hb : 0 < b)
    (Af Bf : Finset (Fin m → Bool)) (Ag Bg : Finset (Fin b → Bool))
    (hdisj : Disjoint Ag Bg) (s : ℕ) (hAgs : Ag.card = s) (hBgs : Bg.card = s) :
    (hamEdges m Af Bf).card * ((hamEdges b Ag Bg).card * s ^ (m - 1))
      ≤ (hamEdges (m * b) (blkSet hb Af Ag Bg) (blkSet hb Bf Ag Bg)).card := by
  classical
  set D := (hamEdges m Af Bf).sigma (fun e =>
    (hamEdges b Ag Bg) ×ˢ Fintype.piFinset (fun j : Fin m =>
      if e.1 j = e.2 j then (if e.1 j = true then Ag else Bg)
      else ({fun _ => false} : Finset (Fin b → Bool)))) with hD
  have hcard : D.card
      = (hamEdges m Af Bf).card * ((hamEdges b Ag Bg).card * s ^ (m - 1)) := by
    rw [hD, Finset.card_sigma]
    have hper : ∀ e ∈ hamEdges m Af Bf,
        ((hamEdges b Ag Bg) ×ˢ Fintype.piFinset (fun j : Fin m =>
          if e.1 j = e.2 j then (if e.1 j = true then Ag else Bg)
          else ({fun _ => false} : Finset (Fin b → Bool)))).card
        = (hamEdges b Ag Bg).card * s ^ (m - 1) := by
      intro e he
      obtain ⟨-, -, j₀, hj₀⟩ := mem_hamEdges.mp he
      rw [Finset.card_product, Fintype.card_piFinset]
      congr 1
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun j => e.1 j = e.2 j)]
      have hfac1 : ∀ j ∈ Finset.univ.filter (fun j => e.1 j = e.2 j),
          ((if e.1 j = e.2 j then (if e.1 j = true then Ag else Bg)
            else ({fun _ => false} : Finset (Fin b → Bool)))).card = s := by
        intro j hj
        have hag := (Finset.mem_filter.mp hj).2
        rw [if_pos hag]
        by_cases h1 : e.1 j = true
        · rw [if_pos h1]
          exact hAgs
        · rw [if_neg h1]
          exact hBgs
      have hfac2 : ∀ j ∈ Finset.univ.filter (fun j => ¬ e.1 j = e.2 j),
          ((if e.1 j = e.2 j then (if e.1 j = true then Ag else Bg)
            else ({fun _ => false} : Finset (Fin b → Bool)))).card = 1 := by
        intro j hj
        have hag := (Finset.mem_filter.mp hj).2
        rw [if_neg hag]
        exact Finset.card_singleton _
      rw [Finset.prod_congr rfl hfac1, Finset.prod_congr rfl hfac2,
        Finset.prod_const, Finset.prod_const, one_pow, mul_one]
      congr 1
      have := agree_card e.1 j₀
      have hcongr : Finset.univ.filter (fun j => e.1 j = e.2 j)
          = Finset.univ.filter
            (fun j => e.1 j = Function.update e.1 j₀ (!(e.1 j₀)) j) := by
        rw [← hj₀]
      rw [hcongr, this]
    rw [Finset.sum_congr rfl hper, Finset.sum_const, smul_eq_mul]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun p => ((fun i => zblk p.1 p.2.1 p.2.2 (blkOf hb i) (offOf hb i)),
      (fun i => zblk' p.1 p.2.1 p.2.2 (blkOf hb i) (offOf hb i)))) ?_ ?_
  · rintro ⟨e, eg, w⟩ hp
    have hp' := Finset.mem_sigma.mp hp
    obtain ⟨heg, hwpi⟩ := Finset.mem_product.mp hp'.2
    obtain ⟨heAf, heBf, j₀, hj₀⟩ := mem_hamEdges.mp hp'.1
    obtain ⟨heg1, heg2, i₀, hi₀⟩ := mem_hamEdges.mp heg
    have hw := Fintype.mem_piFinset.mp hwpi
    refine mem_hamEdges.mpr ⟨?_, ?_, emb hb j₀ i₀, ?_⟩
    · exact mem_blkSet_of hb heAf (zblk_mem e eg w heg1 heg2 hw)
    · exact mem_blkSet_of hb heBf (zblk'_mem e eg w heg1 heg2 hw)
    · have hcond : (fun i => zblk' e eg w (blkOf hb i) (offOf hb i))
          = Function.update (fun i => zblk e eg w (blkOf hb i) (offOf hb i))
              (emb hb j₀ i₀)
              (!((fun i => zblk e eg w (blkOf hb i) (offOf hb i))
                (emb hb j₀ i₀))) := by
        show (fun i => zblk' e eg w (blkOf hb i) (offOf hb i))
          = Function.update (fun i => zblk e eg w (blkOf hb i) (offOf hb i))
              (emb hb j₀ i₀)
              (!(zblk e eg w (blkOf hb (emb hb j₀ i₀))
                (offOf hb (emb hb j₀ i₀))))
        rw [blk_emb, off_emb]
        exact zblk_edge hb e eg w j₀ i₀ hj₀ hi₀
      exact hcond
  · rintro ⟨e, eg, w⟩ hp ⟨e', eg', w'⟩ hq hpq
    have hp' := Finset.mem_sigma.mp (Finset.mem_coe.mp hp)
    have hq' := Finset.mem_sigma.mp (Finset.mem_coe.mp hq)
    obtain ⟨heg, hwpi⟩ := Finset.mem_product.mp hp'.2
    obtain ⟨heg', hwpi'⟩ := Finset.mem_product.mp hq'.2
    obtain ⟨heAf, heBf, j₀, hj₀⟩ := mem_hamEdges.mp hp'.1
    obtain ⟨heg1, heg2, i₀, hi₀⟩ := mem_hamEdges.mp heg
    obtain ⟨heg1', heg2', i₀', hi₀'⟩ := mem_hamEdges.mp heg'
    have hw0 := Fintype.mem_piFinset.mp hwpi
    have hw0' := Fintype.mem_piFinset.mp hwpi'
    have hw : ∀ j, w j ∈ (if e.1 j = e.2 j
        then (if e.1 j = true then Ag else Bg)
        else ({fun _ => false} : Finset (Fin b → Bool))) := hw0
    have hw' : ∀ j, w' j ∈ (if e'.1 j = e'.2 j
        then (if e'.1 j = true then Ag else Bg)
        else ({fun _ => false} : Finset (Fin b → Bool))) := hw0'
    have hE : ((fun i => zblk e eg w (blkOf hb i) (offOf hb i)),
        (fun i => zblk' e eg w (blkOf hb i) (offOf hb i)))
        = ((fun i => zblk e' eg' w' (blkOf hb i) (offOf hb i)),
          (fun i => zblk' e' eg' w' (blkOf hb i) (offOf hb i))) := hpq
    have h1u := congrArg Prod.fst hE
    have h2u := congrArg Prod.snd hE
    have h1 : (fun i => zblk e eg w (blkOf hb i) (offOf hb i))
        = (fun i => zblk e' eg' w' (blkOf hb i) (offOf hb i)) := h1u
    have h2 : (fun i => zblk' e eg w (blkOf hb i) (offOf hb i))
        = (fun i => zblk' e' eg' w' (blkOf hb i) (offOf hb i)) := h2u
    have hblk : ∀ j i, zblk e eg w j i = zblk e' eg' w' j i := by
      intro j i
      have h := congrFun h1 (emb hb j i)
      rw [blk_emb, off_emb] at h
      exact h
    have hblk' : ∀ j i, zblk' e eg w j i = zblk' e' eg' w' j i := by
      intro j i
      have h := congrFun h2 (emb hb j i)
      rw [blk_emb, off_emb] at h
      exact h
    have hblkv : ∀ j, zblk e eg w j = zblk e' eg' w' j :=
      fun j => funext (hblk j)
    have hblkv' : ∀ j, zblk' e eg w j = zblk' e' eg' w' j :=
      fun j => funext (hblk' j)
    have hm1 := zblk_mem e eg w heg1 heg2 hw
    have hm1' := zblk_mem e' eg' w' heg1' heg2' hw'
    have hm2 := zblk'_mem e eg w heg1 heg2 hw
    have hm2' := zblk'_mem e' eg' w' heg1' heg2' hw'
    have he1 : e.1 = e'.1 := by
      funext j
      by_cases hA : e.1 j = true
      · by_cases hB : e'.1 j = true
        · rw [hA, hB]
        · exfalso
          have ha := hm1 j
          have hb' := hm1' j
          rw [if_pos hA] at ha
          rw [if_neg hB, ← hblkv j] at hb'
          exact Finset.disjoint_left.mp hdisj ha hb'
      · by_cases hB : e'.1 j = true
        · exfalso
          have ha := hm1 j
          have hb' := hm1' j
          rw [if_neg hA] at ha
          rw [if_pos hB, ← hblkv j] at hb'
          exact Finset.disjoint_left.mp hdisj hb' ha
        · cases hv1 : e.1 j
          · cases hv2 : e'.1 j
            · rfl
            · exact absurd hv2 hB
          · exact absurd hv1 hA
    have he2 : e.2 = e'.2 := by
      funext j
      by_cases hA : e.2 j = true
      · by_cases hB : e'.2 j = true
        · rw [hA, hB]
        · exfalso
          have ha := hm2 j
          have hb' := hm2' j
          rw [if_pos hA] at ha
          rw [if_neg hB, ← hblkv' j] at hb'
          exact Finset.disjoint_left.mp hdisj ha hb'
      · by_cases hB : e'.2 j = true
        · exfalso
          have ha := hm2 j
          have hb' := hm2' j
          rw [if_neg hA] at ha
          rw [if_pos hB, ← hblkv' j] at hb'
          exact Finset.disjoint_left.mp hdisj hb' ha
        · cases hv1 : e.2 j
          · cases hv2 : e'.2 j
            · rfl
            · exact absurd hv2 hB
          · exact absurd hv1 hA
    have hee : e = e' := Prod.ext_iff.mpr ⟨he1, he2⟩
    subst hee
    have hne : ¬ (e.1 j₀ = e.2 j₀) := by
      intro h
      exact update_flip_ne e.1 j₀ (by rw [← hj₀]; exact h)
    have hww : w = w' := by
      funext j
      by_cases hag : e.1 j = e.2 j
      · have ha := hblkv j
        simp only [zblk] at ha
        rw [if_pos hag, if_pos hag] at ha
        exact ha
      · have ha := hw j
        have hb' := hw' j
        rw [if_neg hag] at ha hb'
        have ha' : w j = (fun _ => false : Fin b → Bool) :=
          Finset.mem_singleton.mp ha
        have hb'' : w' j = (fun _ => false : Fin b → Bool) :=
          Finset.mem_singleton.mp hb'
        rw [ha', hb'']
    have hgg : eg = eg' := by
      have hz := hblkv j₀
      have hz' := hblkv' j₀
      simp only [zblk] at hz
      simp only [zblk'] at hz'
      rw [if_neg hne, if_neg hne] at hz
      rw [if_neg hne, if_neg hne] at hz'
      have hv2 : e.2 j₀ = !(e.1 j₀) := by rw [hj₀, Function.update_self]
      by_cases h1 : e.1 j₀ = true
      · have h2 : e.2 j₀ = false := by rw [hv2, h1]; rfl
        rw [if_pos h1, if_pos h1] at hz
        rw [if_neg (by rw [h2]; exact Bool.false_ne_true),
          if_neg (by rw [h2]; exact Bool.false_ne_true)] at hz'
        exact Prod.ext_iff.mpr ⟨hz, hz'⟩
      · have h2 : e.2 j₀ = true := by
          have h1' : e.1 j₀ = false := by
            cases h : e.1 j₀
            · rfl
            · exact absurd h h1
          rw [hv2, h1']; rfl
        rw [if_neg h1, if_neg h1] at hz
        rw [if_pos h2, if_pos h2] at hz'
        exact Prod.ext_iff.mpr ⟨hz', hz⟩
    subst hww
    subst hgg
    rfl

/-- **THE MULTIPLICATIVE RECURRENCE (proved, K3)**:
`Q(f) · Q(g) ≤ L(f ∘ g^m)`, cross-multiplied. -/
theorem khr_comp_mul {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (f : (Fin m → Bool) → Bool) (g : (Fin b → Bool) → Bool)
    (Af Bf : Finset (Fin m → Bool)) (Ag Bg : Finset (Fin b → Bool))
    (hAf : ∀ y ∈ Af, f y = true) (hBf : ∀ y ∈ Bf, f y = false)
    (hAg : ∀ u ∈ Ag, g u = true) (hBg : ∀ u ∈ Bg, g u = false)
    (s : ℕ) (hAgs : Ag.card = s) (hBgs : Bg.card = s)
    (t : DMTree (m * b)) (ht : ∀ z, t.eval z = comp hb f g z) :
    (hamEdges m Af Bf).card ^ 2 * (hamEdges b Ag Bg).card ^ 2
      ≤ t.lsize * (Af.card * Bf.card) * (Ag.card * Bg.card) := by
  classical
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0
    have hAg0 : Ag = ∅ := Finset.card_eq_zero.mp hAgs
    have hEg : hamEdges b Ag Bg = ∅ := by
      rw [hamEdges, hAg0]
      simp
    rw [hEg]
    simp
  · have hdisj : Disjoint Ag Bg := Finset.disjoint_left.mpr (fun u h1 h2 => by
      have hg1 := hAg u h1
      have hg2 := hBg u h2
      rw [hg1] at hg2
      exact Bool.noConfusion hg2)
    have hK1 := khrapchenko t (blkSet hb Af Ag Bg) (blkSet hb Bf Ag Bg)
      (fun z hz => by rw [ht]; exact blkSet_eval hb f g true hAg hBg hAf z hz)
      (fun z hz => by rw [ht]; exact blkSet_eval hb f g false hAg hBg hBf z hz)
    rw [blkSet_card hb Af Ag Bg hdisj s hAgs hBgs,
      blkSet_card hb Bf Ag Bg hdisj s hAgs hBgs] at hK1
    have hlift := edge_lift_card hb Af Bf Ag Bg hdisj s hAgs hBgs
    have hE2 : ((hamEdges m Af Bf).card
        * ((hamEdges b Ag Bg).card * s ^ (m - 1))) ^ 2
        ≤ (hamEdges (m * b) (blkSet hb Af Ag Bg) (blkSet hb Bf Ag Bg)).card ^ 2 :=
      Nat.pow_le_pow_left hlift 2
    have hchain := le_trans hE2 hK1
    have hsm : s ^ m = s ^ (m - 1) * s := by
      rw [← pow_succ]
      congr 1
      omega
    have e1 : ((hamEdges m Af Bf).card
        * ((hamEdges b Ag Bg).card * s ^ (m - 1))) ^ 2
        = ((hamEdges m Af Bf).card ^ 2 * (hamEdges b Ag Bg).card ^ 2)
          * (s ^ (m - 1) * s ^ (m - 1)) := by ring
    have e2 : t.lsize * (Af.card * s ^ m) * (Bf.card * s ^ m)
        = (t.lsize * (Af.card * Bf.card) * (Ag.card * Bg.card))
          * (s ^ (m - 1) * s ^ (m - 1)) := by
      rw [hsm, hAgs, hBgs]
      ring
    rw [e1, e2] at hchain
    exact Nat.le_of_mul_le_mul_right hchain
      (Nat.mul_pos (pow_pos hspos _) (pow_pos hspos _))

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.edge_lift_card
#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.khr_comp_mul
