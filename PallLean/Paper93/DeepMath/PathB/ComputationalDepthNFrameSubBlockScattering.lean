import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameEscapeDensity

/-!
# N-Frame: sub-block scattering — a two-bit pattern drags its pin signs

The propagation law refined below block granularity.  Full-block ownership was never what the row
family used: the probe behind the `2^k` distinct rows is live at exactly **two** coordinates of the
designated block — the slot-0 selector of the differing pin and the slot-0 sign.  So ownership of
that two-bit pattern already propagates.

  `sat3Bit_div` / `sat3Context_designated` — layout helpers: every `sat3Bit` knows its block; the pin
        context vanishes identically on the designated block.
  `sat3_subblock_pin_propagation_left/right` — **PROVED, the two-bit propagation**: if the slot-0
        sign of block `c` lies in `A \ B`, then among pins `j` whose slot-0 selector `(c, j)` also
        lies in `A \ B`, at most `|A ∩ B| + 1` have their pin sign outside `A \ B`.  Ownership of
        `{sign₀(c), sel₀(c,j)}` drags `π(c,j)` — the row family runs on explicit probes
        (`sat3Context_probe_eval`), and the mixOn/patch transfer needs only the two live probe bits
        plus the vanishing of context and probe on the rest of the block.
  `sat3_pin_propagation_left_of_subblock` — **PROVED, subsumption**: the full-block propagation of
        `EscapeDensity` is the special case where the whole block is owned.

## Honest scope

In the sign-aligned branch the slot-0 machinery is already saturated (slot-0 signs are captured, so
the fused statement adds nothing there); the sub-block law's new power is as a **local, per-pattern
constraint on arbitrary interfaced cuts** — the raw material for the `GlobalPACInterfaceBound`
counting.  The aligned branch's remaining freedom lives in slot-1/2 signs and slot-0/1 selectors,
whose mixed/pinned-style eval workhorses are not yet built — named, not claimed.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Every `sat3Bit` knows its block. -/
theorem sat3Bit_div (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (f : ℕ)
    (hf : f < sat3V N + 1) :
    (sat3Bit N c t f hf).val / sat3D N = c.val := by
  show (c.val * sat3D N + t.val * (sat3V N + 1) + f) / sat3D N = c.val
  rw [Nat.add_assoc, Nat.add_comm (c.val * sat3D N) _,
    Nat.add_mul_div_right _ _ (sat3D_pos N),
    Nat.div_eq_of_lt (show t.val * (sat3V N + 1) + f < sat3D N by
      have ht2 : t.val * (sat3V N + 1) ≤ 2 * (sat3V N + 1) :=
        Nat.mul_le_mul_right _ (by have := t.isLt; omega)
      have hD : sat3D N = 3 * (sat3V N + 1) := rfl
      omega),
    Nat.zero_add]

/-- The pin context vanishes identically on the designated block. -/
theorem sat3Context_designated (N : ℕ) (c : Fin (sat3M N)) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (b : Fin k → Bool) (i : Fin N)
    (hdiv : i.val / sat3D N = c.val) :
    sat3Context N c hk b i = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨j, hj1, -⟩ | ⟨-, hne, -, -⟩)
  · exact sat3PinClause_ne N c hk j (hj1.symm.trans hdiv)
  · exact hne hdiv

/-- XOR is left-cancellative — the tiny Bool core, kept out of the big context. -/
theorem xor_left_inj (a b c : Bool) (h : xor a c = xor b c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

set_option maxHeartbeats 1600000 in
/-- **THE TWO-BIT PROPAGATION, LEFT (proved)**: owning `{sign₀(c), sel₀(c,j)}` in `A \ B` drags the
pin sign `π(c,j)` into `A \ B`, with at most `|A ∩ B| + 1` exceptions over `j`. -/
theorem sat3_subblock_pin_propagation_left (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (hσ₀ : sat3SignBit N c ∈ A \ B) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c ⟨0, by omega⟩ j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A \ B ∧
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ A \ B)).card ≤ (A ∩ B).card + 1 := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set Jf := (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
    sat3Bit N c ⟨0, by omega⟩ j.val
      (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A \ B ∧
    sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
      (by omega) ∉ A \ B) with hJf
  set e : (↥Jf → Bool) → (Fin (sat3M N - 2) → Bool) :=
    fun bb j => if hmem : j ∈ Jf then bb ⟨j, hmem⟩ else false with he
  have heval : ∀ (bb : ↥Jf → Bool) (w : ↥Jf), e bb w.val = bb w := by
    intro bb w
    show (if hmem : w.val ∈ Jf then bb ⟨w.val, hmem⟩ else false) = bb w
    rw [dif_pos w.prop, Subtype.coe_eta]
  have heinj : Function.Injective e := by
    intro bb bb' heq
    funext w
    rw [← heval bb w, ← heval bb' w, heq]
  set Y : Finset (Fin N → Bool) :=
    Finset.univ.image (fun bb : ↥Jf → Bool => sat3Context N c hk (e bb)) with hY
  have hYcard : Y.card = 2 ^ Jf.card := by
    rw [hY, Finset.card_image_of_injective _
        (fun bb bb' heq => heinj (sat3Context_injective N hv hk hkv c heq)),
      Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool]
  have hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, sat3Family N (mixOn (A \ B) x y)
        ≠ sat3Family N (mixOn (A \ B) x y') := by
    intro y hy y' hy' hne
    rw [hY] at hy hy'
    obtain ⟨bb, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨bb', -, rfl⟩ := Finset.mem_image.mp hy'
    have hbne : e bb ≠ e bb' := fun hh' => hne (by rw [hh'])
    obtain ⟨j₀, hj₀ne⟩ := Function.ne_iff.mp hbne
    have hj₀J : j₀ ∈ Jf := by
      by_contra hmem
      apply hj₀ne
      show (if hm : j₀ ∈ Jf then bb ⟨j₀, hm⟩ else false)
        = (if hm : j₀ ∈ Jf then bb' ⟨j₀, hm⟩ else false)
      rw [dif_neg hmem, dif_neg hmem]
    have hj₀mem := Finset.mem_filter.mp (hJf ▸ hj₀J)
    have hselJ := hj₀mem.2.1
    have hjv : j₀.val < sat3V N := by
      have := j₀.isLt
      omega
    set uu := sat3Probe N ⟨j₀.val, hjv⟩ (!(e bb j₀)) with huudef
    -- distinctness: the probe reads the pin apart
    have huu : sat3Family N (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        ≠ sat3Family N (sat3Patch N c (sat3Context N c hk (e bb')) uu) := by
      rw [huudef,
        sat3Context_probe_eval N hv hk hkv c (e bb) j₀ ⟨j₀.val, hjv⟩ rfl
          (!(e bb j₀)),
        sat3Context_probe_eval N hv hk hkv c (e bb') j₀ ⟨j₀.val, hjv⟩ rfl
          (!(e bb j₀))]
      intro heq
      exact hj₀ne (xor_left_inj _ _ _ heq)
    -- the probe vanishes on the designated block outside the two owned bits
    have hprobe0 : ∀ i : Fin N, i.val / sat3D N = c.val → i ∉ A \ B →
        uu i = false := by
      intro i hdiv hi
      rw [huudef]
      show decide _ = false
      rw [decide_eq_false_iff_not]
      have hred : (⟨j₀.val, hjv⟩ : Fin (sat3V N)).val = j₀.val := rfl
      rintro (hsel | ⟨hsg, -⟩)
      · apply hi
        have hiπ : sat3Bit N c ⟨0, by omega⟩ j₀.val (by omega) = i := by
          apply Fin.ext
          show c.val * sat3D N + 0 * (sat3V N + 1) + j₀.val = i.val
          have hdm := Nat.div_add_mod i.val (sat3D N)
          rw [hdiv, hsel] at hdm
          have hcm : sat3D N * c.val = c.val * sat3D N := Nat.mul_comm _ _
          omega
        rw [← hiπ]
        exact hselJ
      · apply hi
        have hiσ : sat3SignBit N c = i := by
          apply Fin.ext
          show c.val * sat3D N + 0 * (sat3V N + 1) + sat3V N = i.val
          have hdm := Nat.div_add_mod i.val (sat3D N)
          rw [hdiv, hsg] at hdm
          have hcm : sat3D N * c.val = c.val * sat3D N := Nat.mul_comm _ _
          omega
        rw [← hiσ]
        exact hσ₀
    -- contexts agree on all of A \ B
    have hagree : ∀ i : Fin N, i ∈ A \ B →
        sat3Context N c hk (e bb) i = sat3Context N c hk (e bb') i := by
      intro i hi
      apply sat3Context_agree
      intro j hj1 hj2
      by_cases hmem : j ∈ Jf
      · exfalso
        have hπ := (Finset.mem_filter.mp (hJf ▸ hmem)).2.2
        apply hπ
        have hiπ : sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
            (by omega) = i := by
          apply Fin.ext
          show (sat3PinClause N c hk j).val * sat3D N + 0 * (sat3V N + 1)
            + sat3V N = i.val
          have hdm := Nat.div_add_mod i.val (sat3D N)
          rw [hj1, hj2] at hdm
          have hcm : sat3D N * (sat3PinClause N c hk j).val
              = (sat3PinClause N c hk j).val * sat3D N := Nat.mul_comm _ _
          omega
        rw [hiπ]
        exact hi
      · show (if hm : j ∈ Jf then bb ⟨j, hm⟩ else false)
          = (if hm : j ∈ Jf then bb' ⟨j, hm⟩ else false)
        rw [dif_neg hmem, dif_neg hmem]
    refine ⟨sat3Patch N c (sat3Context N c hk (e bb)) uu, ?_⟩
    have hmix1 : mixOn (A \ B) (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        (sat3Context N c hk (e bb))
        = sat3Patch N c (sat3Context N c hk (e bb)) uu := by
      funext i
      show (if i ∈ A \ B then sat3Patch N c (sat3Context N c hk (e bb)) uu i
        else sat3Context N c hk (e bb) i)
        = sat3Patch N c (sat3Context N c hk (e bb)) uu i
      by_cases hi : i ∈ A \ B
      · rw [if_pos hi]
      · rw [if_neg hi]
        show sat3Context N c hk (e bb) i
          = (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb) i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, sat3Context_designated N c hk (e bb) i hdiv,
            hprobe0 i hdiv hi]
        · rw [if_neg hdiv]
    have hmix2 : mixOn (A \ B) (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        (sat3Context N c hk (e bb'))
        = sat3Patch N c (sat3Context N c hk (e bb')) uu := by
      funext i
      show (if i ∈ A \ B then sat3Patch N c (sat3Context N c hk (e bb)) uu i
        else sat3Context N c hk (e bb') i)
        = sat3Patch N c (sat3Context N c hk (e bb')) uu i
      by_cases hi : i ∈ A \ B
      · rw [if_pos hi]
        show (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb) i)
          = (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb') i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, if_pos hdiv]
        · rw [if_neg hdiv, if_neg hdiv]
          exact hagree i hi
      · rw [if_neg hi]
        show sat3Context N c hk (e bb') i
          = (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb') i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, sat3Context_designated N c hk (e bb') i hdiv,
            hprobe0 i hdiv hi]
        · rw [if_neg hdiv]
    rw [hmix1, hmix2]
    exact huu
  have hcap := shared_split_row_capacity (sat3Family N) A B op g h hg hh hf Y hdist
  rw [hYcard] at hcap
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ ((A ∩ B).card + 1) < 2 ^ Jf.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- **THE TWO-BIT PROPAGATION, RIGHT (proved)**: the mirror, by swapping the factor roles. -/
theorem sat3_subblock_pin_propagation_right (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (hσ₀ : sat3SignBit N c ∈ B \ A) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c ⟨0, by omega⟩ j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ B \ A ∧
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ B \ A)).card ≤ (A ∩ B).card + 1 := by
  have hswap := sat3_subblock_pin_propagation_left N hv hk (fun a b => op b a)
    h g B A hh hg hf c hσ₀
  have hint : (B ∩ A).card = (A ∩ B).card := by
    rw [Finset.inter_comm]
  omega

/-- **SUBSUMPTION (proved)**: full-block ownership is the special case of the two-bit law — the
`EscapeDensity` propagation follows. -/
theorem sat3_pin_propagation_left_of_subblock (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (hsub : blockCoords N c ⊆ A \ B) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ A \ B)).card ≤ (A ∩ B).card + 1 := by
  have hσ₀ : sat3SignBit N c ∈ A \ B :=
    hsub (show sat3SignBit N c ∈ blockCoords N c from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        sat3Bit_div N c ⟨0, by omega⟩ (sat3V N) (by omega)⟩)
  have hmain := sat3_subblock_pin_propagation_left N hv hk op g h A B hg hh hf
    c hσ₀
  have hmono : ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ A \ B)).card
      ≤ ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun j =>
      sat3Bit N c ⟨0, by omega⟩ j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega) ∈ A \ B ∧
      sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ A \ B)).card := by
    apply Finset.card_le_card
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨hj.1, ?_, hj.2⟩
    exact hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      sat3Bit_div N c ⟨0, by omega⟩ j.val
        (by have := sat3M_pred_le_sat3V N; have := j.isLt; omega)⟩)
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_subblock_pin_propagation_left
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_subblock_pin_propagation_right
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pin_propagation_left_of_subblock
