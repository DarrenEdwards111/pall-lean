import PallLean.Paper93.DeepMath.PathB.ComputationalDepthROTExtraction

/-!
# Cone-relative floor extraction: brick 1 of the `SlackComposes` m = 2 attack

The floor ⟹ read-once-tree theorem holds **cone-relative**: everything the census,
fanout, wiring, and extraction arguments count lives inside the cone, so the
hypothesis `length + 1 = 2·deps` can be weakened to `|cone| + 1 = 2·deps`.  This
per-circuit sharpening is what the m = 2 case analysis needs (a 12-gate circuit
for `AEm 2` has `|cone| ∈ {11, 12}`, and the 11 case dies here):

* **`cone_card_ge` (proved)** — per circuit: `2·deps ≤ |cone| + 1`;
* **`cone_census` / `cone_fanout_le_one` / `cone_wiring` (proved)** — the floor
  structure theory with `|cone| + 1 = 2·deps` in place of the length hypothesis;
* **`cone_realizes_ROT` (proved)** — a circuit whose cone attains the floor
  computes a read-once tree (strictly stronger than `floor_realizes_ROT`, which
  is the special case `cone = whole circuit`);
* **`cone_lb_of_unsplittable` (proved)** — per circuit: one unsplittable triple
  restriction forces `2·deps ≤ |cone|`;
* **`AEm_cone_ge` (proved)** — every circuit computing `AEm m` has
  `6m ≤ |cone|`: in particular a 12-gate circuit for `AEm 2` has cone = the
  whole circuit.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- A floor-attaining cone is nonempty, so the circuit is nonempty. -/
theorem cone_floor_pos {n : ℕ} {f : (Fin n → Bool) → Bool} {c : List (CGate n)}
    (hclen : (cone c).card + 1 = 2 * (depSet f).card) : 0 < c.length := by
  have hpos : 0 < (cone c).card := by omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have := (mem_cone.mp hw).1
  omega

/-- **The per-circuit cone bound (proved)**: `2·deps ≤ |cone| + 1` for every
circuit computing `f` — the cone-relative form of `cone_bound`. -/
theorem cone_card_ge {n : ℕ} {f : (Fin n → Bool) → Bool} {c : List (CGate n)}
    (hcomp : computes c f) (hs : 0 < c.length) :
    2 * (depSet f).card ≤ (cone c).card + 1 := by
  classical
  have hA := cone_card_le c hs
  have h2 := depSet_card_le_coneVars f c hcomp hs
  have hsplit : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false))
      + ∑ w ∈ (cone c).filter
          (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
          inSlots (c.getD w (.cst false))
      = ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    rw [coneVars]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hvar0 : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [coneVars, Finset.mem_filter] at hw
    obtain ⟨-, i', hi'⟩ := hw
    rw [hi']
    rfl
  have hrest : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      ≤ 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 2 (fun w _ => inSlots_le_two _)) ?_
    rw [smul_eq_mul]
    omega
  have hpart : (coneVars c).card
      + ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card
      = (cone c).card := by
    rw [coneVars]
    exact Finset.card_filter_add_card_filter_not (s := cone c)
      (p := fun w => ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')
  omega

/-- **The cone-relative census (proved)**: `|cone| + 1 = 2·deps` forces exactly
`deps` cone var gates and all other cone gates binary. -/
theorem cone_census {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f)
    (hclen : (cone c).card + 1 = 2 * (depSet f).card) :
    (coneVars c).card = (depSet f).card ∧
    ∀ w ∈ cone c, (¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i') →
      inSlots (c.getD w (.cst false)) = 2 := by
  classical
  have hs : 0 < c.length := cone_floor_pos hclen
  have hA := cone_card_le c hs
  have h2 := depSet_card_le_coneVars f c hcomp hs
  have hsplit : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false))
      + ∑ w ∈ (cone c).filter
          (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
          inSlots (c.getD w (.cst false))
      = ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    rw [coneVars]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hvar0 : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [coneVars, Finset.mem_filter] at hw
    obtain ⟨-, i', hi'⟩ := hw
    rw [hi']
    rfl
  have hrest : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      ≤ 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 2 (fun w _ => inSlots_le_two _)) ?_
    rw [smul_eq_mul]
    omega
  have hpart : (coneVars c).card
      + ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card
      = (cone c).card := by
    rw [coneVars]
    exact Finset.card_filter_add_card_filter_not (s := cone c)
      (p := fun w => ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')
  have hvarsEq : (coneVars c).card = (depSet f).card := by omega
  refine ⟨hvarsEq, ?_⟩
  have hsumEq : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      = 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    omega
  intro w hw hnv
  have hwmem : w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i') :=
    Finset.mem_filter.mpr ⟨hw, hnv⟩
  by_contra hne2
  have hlt : inSlots (c.getD w (.cst false)) < 2 :=
    lt_of_le_of_ne (inSlots_le_two _) hne2
  have hstrict : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      < ∑ _w ∈ (cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'), 2 :=
    Finset.sum_lt_sum (fun i _ => inSlots_le_two _) ⟨w, hwmem, hlt⟩
  rw [Finset.sum_const, smul_eq_mul] at hstrict
  omega

/-- **Cone-relative fanout (proved)**: at the cone floor, a non-output cone wire
has at most one cone reader. -/
theorem cone_fanout_le_one {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hclen : (cone c).card + 1 = 2 * (depSet f).card)
    (j : ℕ) (hj : j ∈ cone c) (hjr : j ≠ c.length - 1)
    (w₁ w₂ : ℕ) (h₁ : w₁ ∈ cone c) (h₂ : w₂ ∈ cone c)
    (hr₁ : j ∈ gateReads (c.getD w₁ (.cst false)))
    (hr₂ : j ∈ gateReads (c.getD w₂ (.cst false))) : w₁ = w₂ := by
  classical
  by_contra hne
  have hs : 0 < c.length := cone_floor_pos hclen
  obtain ⟨hvarsEq, -⟩ := cone_census f c hcomp hclen
  have h1 := cone_card_le c hs
  have hsplit : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false))
      + ∑ w ∈ (cone c).filter
          (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
          inSlots (c.getD w (.cst false))
      = ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    rw [coneVars]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hvar0 : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [coneVars, Finset.mem_filter] at hw
    obtain ⟨-, i', hi'⟩ := hw
    rw [hi']
    rfl
  have hrest : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      ≤ 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    refine le_trans (Finset.sum_le_card_nsmul _ _ 2 (fun w _ => inSlots_le_two _)) ?_
    rw [smul_eq_mul]
    omega
  have hpart : (coneVars c).card
      + ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card
      = (cone c).card := by
    rw [coneVars]
    exact Finset.card_filter_add_card_filter_not (s := cone c)
      (p := fun w => ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')
  -- injection scaffold
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hex : ∀ x ∈ (cone c).erase (c.length - 1),
      ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w := by
    intro x hx
    obtain ⟨hxne, hxc⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxlt, hxcone⟩ := mem_cone.mp hxc
    cases hxcone with
    | root => exact absurd rfl hxne
    | step hw hjm hjw => exact ⟨_, hw, hjm, hjw⟩
  have hjmem : j ∈ (cone c).erase (c.length - 1) := Finset.mem_erase.mpr ⟨hjr, hj⟩
  have hjd : ∃ w, InCone c w ∧ j ∈ gateReads (c.getD w (.cst false)) ∧ j < w :=
    hex j hjmem
  have himg_sub : ((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))
      ⊆ (cone c).biUnion
        (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) := by
    intro pr hpr
    obtain ⟨x, hx, hφ⟩ := Finset.mem_image.mp hpr
    obtain ⟨w, hw⟩ := hex x hx
    rw [← hφ, dif_pos ⟨w, hw⟩]
    have hspec := Classical.choose_spec
      (⟨w, hw⟩ : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w)
    rw [Finset.mem_biUnion]
    exact ⟨_, mem_cone.mpr ⟨inCone_lt hs hspec.1, hspec.1⟩,
      Finset.mem_image.mpr ⟨x, hspec.2.1, rfl⟩⟩
  have hinj : Set.InjOn
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))
      ((cone c).erase (c.length - 1)) := by
    intro a _ b _ hab
    exact congrArg Prod.snd hab
  have himg_card : (((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))).card
      = (cone c).card - 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hroot]
  -- the bad reader distinct from the chosen consumer
  have hbad : ∃ wb, wb ∈ cone c ∧ j ∈ gateReads (c.getD wb (.cst false)) ∧
      wb ≠ Classical.choose hjd := by
    by_cases h1c : w₁ = Classical.choose hjd
    · exact ⟨w₂, h₂, hr₂, fun h => hne (h1c.trans h.symm)⟩
    · exact ⟨w₁, h₁, hr₁, h1c⟩
  obtain ⟨wb, hwbc, hwbr, hwbne⟩ := hbad
  have hextra_mem : (wb, j) ∈ (cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) := by
    rw [Finset.mem_biUnion]
    exact ⟨wb, hwbc, Finset.mem_image.mpr ⟨j, hwbr, rfl⟩⟩
  have hextra_not : (wb, j) ∉ ((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x)) := by
    intro hmem
    obtain ⟨x, hx, hφ⟩ := Finset.mem_image.mp hmem
    have hxj : x = j := congrArg Prod.snd hφ
    subst hxj
    have hφ1 : (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0) = wb := congrArg Prod.fst hφ
    rw [dif_pos hjd] at hφ1
    exact hwbne hφ1.symm
  have hcard2 : (cone c).card - 1 + 1 ≤ ((cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t)))).card := by
    rw [← himg_card, ← Finset.card_insert_of_notMem hextra_not]
    exact Finset.card_le_card (Finset.insert_subset hextra_mem himg_sub)
  have hEle : ((cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t)))).card
      ≤ ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_)
    intro w _
    exact le_trans Finset.card_image_le (gateReads_card_le _)
  omega

/-- **Cone-relative wiring (proved)**: at the cone floor every read of every cone
gate is in-range, in the cone, not the root, and no binary cone gate reads the
same wire twice. -/
theorem cone_wiring {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hclen : (cone c).card + 1 = 2 * (depSet f).card) :
    (∀ w ∈ cone c, ∀ t ∈ gateReads (c.getD w (.cst false)),
      t < w ∧ t ∈ cone c ∧ t ≠ c.length - 1)
    ∧ ∀ w ∈ cone c, ∀ (op : Bool → Bool → Bool) (j : ℕ),
        c.getD w (.cst false) ≠ CGate.bin op j j := by
  classical
  have hs : 0 < c.length := cone_floor_pos hclen
  obtain ⟨hvarCard, hbin⟩ := cone_census f c hcomp hclen
  have hsplit : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false))
      + ∑ w ∈ (cone c).filter
          (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
          inSlots (c.getD w (.cst false))
      = ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := by
    rw [coneVars]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hvar0 : ∑ w ∈ coneVars c, inSlots (c.getD w (.cst false)) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [coneVars, Finset.mem_filter] at hw
    obtain ⟨-, i', hi'⟩ := hw
    rw [hi']
    rfl
  have hterms : ∀ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false)) = 2 := by
    intro w hw
    rw [Finset.mem_filter] at hw
    exact hbin w hw.1 hw.2
  have hrest2 : ∑ w ∈ (cone c).filter
      (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i'),
      inSlots (c.getD w (.cst false))
      = 2 * ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card := by
    rw [Finset.sum_congr rfl hterms, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hpart : (coneVars c).card
      + ((cone c).filter
        (fun w => ¬ ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')).card
      = (cone c).card := by
    rw [coneVars]
    exact Finset.card_filter_add_card_filter_not (s := cone c)
      (p := fun w => ∃ i' : Fin n, c.getD w (.cst false) = CGate.var i')
  have hsum : ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) = (cone c).card - 1 := by
    omega
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  have hex : ∀ x ∈ (cone c).erase (c.length - 1),
      ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w := by
    intro x hx
    obtain ⟨hxne, hxc⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxlt, hxcone⟩ := mem_cone.mp hxc
    cases hxcone with
    | root => exact absurd rfl hxne
    | step hw hjm hjw => exact ⟨_, hw, hjm, hjw⟩
  have himg_sub : ((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))
      ⊆ (cone c).biUnion
        (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) := by
    intro pr hpr
    obtain ⟨x, hx, hφ⟩ := Finset.mem_image.mp hpr
    obtain ⟨w, hw⟩ := hex x hx
    rw [← hφ, dif_pos ⟨w, hw⟩]
    have hspec := Classical.choose_spec
      (⟨w, hw⟩ : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w)
    rw [Finset.mem_biUnion]
    exact ⟨_, mem_cone.mpr ⟨inCone_lt hs hspec.1, hspec.1⟩,
      Finset.mem_image.mpr ⟨x, hspec.2.1, rfl⟩⟩
  have hinj : Set.InjOn
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))
      ((cone c).erase (c.length - 1)) := by
    intro a _ b _ hab
    exact congrArg Prod.snd hab
  have himg_card : (((cone c).erase (c.length - 1)).image
      (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
        then Classical.choose h else 0, x))).card
      = (cone c).card - 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hroot]
  have hEle : ((cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t)))).card
      ≤ ∑ w ∈ cone c, (gateReads (c.getD w (.cst false))).card := by
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_)
    intro w _
    exact Finset.card_image_le
  have hcards : ∀ w' ∈ cone c,
      (gateReads (c.getD w' (.cst false))).card ≤ inSlots (c.getD w' (.cst false)) :=
    fun w' _ => gateReads_card_le _
  have hEsl : ∑ w ∈ cone c, (gateReads (c.getD w (.cst false))).card
      ≤ ∑ w ∈ cone c, inSlots (c.getD w (.cst false)) := Finset.sum_le_sum hcards
  have hElo : (cone c).card - 1 ≤ ((cone c).biUnion
      (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t)))).card := by
    rw [← himg_card]
    exact Finset.card_le_card himg_sub
  have hcpos : 1 ≤ (cone c).card := Finset.card_pos.mpr ⟨_, hroot⟩
  constructor
  · intro w hwc t ht
    have hEmem : (w, t) ∈ (cone c).biUnion
        (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) :=
      Finset.mem_biUnion.mpr ⟨w, hwc, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
    have hEeq : ((cone c).erase (c.length - 1)).image
        (fun x => (if h : ∃ w, InCone c w ∧ x ∈ gateReads (c.getD w (.cst false)) ∧ x < w
          then Classical.choose h else 0, x))
        = (cone c).biUnion
          (fun w => (gateReads (c.getD w (.cst false))).image (fun t => (w, t))) :=
      Finset.eq_of_subset_of_card_le himg_sub (by omega)
    rw [← hEeq] at hEmem
    obtain ⟨x, hx, hφ⟩ := Finset.mem_image.mp hEmem
    have hxt : x = t := congrArg Prod.snd hφ
    subst hxt
    obtain ⟨htne, htc⟩ := Finset.mem_erase.mp hx
    have hφ1 : (if h : ∃ w', InCone c w' ∧ x ∈ gateReads (c.getD w' (.cst false)) ∧ x < w'
        then Classical.choose h else 0) = w := congrArg Prod.fst hφ
    have hxe := hex x hx
    rw [dif_pos hxe] at hφ1
    have hspec := Classical.choose_spec hxe
    rw [hφ1] at hspec
    exact ⟨hspec.2.2, htc, htne⟩
  · intro w hwc op j hg
    have hstrict : ∑ w' ∈ cone c, (gateReads (c.getD w' (.cst false))).card
        < ∑ w' ∈ cone c, inSlots (c.getD w' (.cst false)) := by
      refine Finset.sum_lt_sum hcards ⟨w, hwc, ?_⟩
      rw [hg]
      show ({j, j} : Finset ℕ).card < 2
      rw [Finset.insert_eq_self.mpr (Finset.mem_singleton_self j)]
      rw [Finset.card_singleton]
      omega
    omega

/-- **Cone-relative var injectivity (proved)**. -/
theorem cone_var_injective {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hclen : (cone c).card + 1 = 2 * (depSet f).card)
    {w₁ w₂ : ℕ} {i : Fin n} (h₁ : w₁ ∈ cone c) (h₂ : w₂ ∈ cone c)
    (hg₁ : c.getD w₁ (.cst false) = CGate.var i)
    (hg₂ : c.getD w₂ (.cst false) = CGate.var i) : w₁ = w₂ := by
  classical
  have hs : 0 < c.length := cone_floor_pos hclen
  have hex : ∀ i' ∈ depSet f, ∃ p, p ∈ cone c ∧ c.getD p (.cst false) = CGate.var i' :=
    fun i' hi' => var_position_exists f c hcomp hs i' hi'
  set S : Finset ℕ := (depSet f).attach.image
    (fun x => Classical.choose (hex x.1 x.2)) with hSdef
  have hSsub : S ⊆ coneVars c := by
    intro p hp
    rw [hSdef, Finset.mem_image] at hp
    obtain ⟨x, -, hpx⟩ := hp
    obtain ⟨hpc, hpg⟩ := Classical.choose_spec (hex x.1 x.2)
    rw [← hpx, coneVars, Finset.mem_filter]
    exact ⟨hpc, ⟨x.1, hpg⟩⟩
  have hinjOn : Set.InjOn
      (fun x : {i' // i' ∈ depSet f} => Classical.choose (hex x.1 x.2))
      ((depSet f).attach : Finset {i' // i' ∈ depSet f}) := by
    intro x _ y _ hxy
    have hxy' : Classical.choose (hex x.1 x.2) = Classical.choose (hex y.1 y.2) := hxy
    obtain ⟨-, hgx⟩ := Classical.choose_spec (hex x.1 x.2)
    obtain ⟨-, hgy⟩ := Classical.choose_spec (hex y.1 y.2)
    rw [hxy'] at hgx
    have hv : CGate.var (n := n) x.1 = CGate.var y.1 := hgx.symm.trans hgy
    exact Subtype.ext (CGate.var.inj hv)
  have hScard : S.card = (depSet f).card := by
    rw [hSdef, Finset.card_image_of_injOn hinjOn, Finset.card_attach]
  have hSeq : S = coneVars c := by
    refine Finset.eq_of_subset_of_card_le hSsub ?_
    rw [hScard]
    exact le_of_eq (cone_census f c hcomp hclen).1
  have hw₁ : w₁ ∈ S := by
    rw [hSeq, coneVars, Finset.mem_filter]
    exact ⟨h₁, ⟨i, hg₁⟩⟩
  have hw₂ : w₂ ∈ S := by
    rw [hSeq, coneVars, Finset.mem_filter]
    exact ⟨h₂, ⟨i, hg₂⟩⟩
  rw [hSdef, Finset.mem_image] at hw₁ hw₂
  obtain ⟨x, -, hx⟩ := hw₁
  obtain ⟨y, -, hy⟩ := hw₂
  obtain ⟨-, hgx⟩ := Classical.choose_spec (hex x.1 x.2)
  obtain ⟨-, hgy⟩ := Classical.choose_spec (hex y.1 y.2)
  rw [hx, hg₁] at hgx
  rw [hy, hg₂] at hgy
  have hxy : x = y := Subtype.ext ((CGate.var.inj hgx).symm.trans (CGate.var.inj hgy))
  rw [← hx, ← hy, hxy]

/-- **Cone-relative reader-chain disjointness (proved)**. -/
theorem cone_reach_not_both {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hclen : (cone c).card + 1 = 2 * (depSet f).card)
    {w j k : ℕ} (hwc : w ∈ cone c)
    (hj : j ∈ gateReads (c.getD w (.cst false))) (hjw : j < w)
    (hk : k ∈ gateReads (c.getD w (.cst false))) (hkw : k < w)
    (hjk : j ≠ k) :
    ∀ (m q : ℕ), c.length - q ≤ m → Reach c j q → Reach c k q → False := by
  have hs : 0 < c.length := cone_floor_pos hclen
  have hwlt : w < c.length := (mem_cone.mp hwc).1
  have hwic : InCone c w := (mem_cone.mp hwc).2
  have hjc : j ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hj hjw⟩
  have hkc : k ∈ cone c := mem_cone.mpr ⟨by omega, InCone.step hwic hk hkw⟩
  intro m
  induction m with
  | zero =>
    intro q hq hrj _
    have hql := reach_le hrj
    have hjlt : j < c.length := (mem_cone.mp hjc).1
    omega
  | succ m ih =>
    intro q hq hrj hrk
    by_cases hqj : q = j
    · subst hqj
      obtain ⟨p, hpk, hqp, hqlt⟩ := reach_last hrk hjk
      have hpic : InCone c p := reach_inCone (mem_cone.mp hkc).2 hpk
      have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
      have hqroot : q ≠ c.length - 1 := by omega
      have hpw : p = w :=
        cone_fanout_le_one f c hcomp hclen q hjc hqroot p w hpc hwc hqp hj
      subst hpw
      have := reach_le hpk
      omega
    · by_cases hqk : q = k
      · subst hqk
        obtain ⟨p, hpj, hqp, hqlt⟩ := reach_last hrj (Ne.symm hjk)
        have hpic : InCone c p := reach_inCone (mem_cone.mp hjc).2 hpj
        have hpc : p ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hpic, hpic⟩
        have hqroot : q ≠ c.length - 1 := by omega
        have hpw : p = w :=
          cone_fanout_le_one f c hcomp hclen q hkc hqroot p w hpc hwc hqp hk
        subst hpw
        have := reach_le hpj
        omega
      · obtain ⟨p₁, hp₁, hqr₁, hql₁⟩ := reach_last hrj hqj
        obtain ⟨p₂, hp₂, hqr₂, hql₂⟩ := reach_last hrk hqk
        have hp₁ic : InCone c p₁ := reach_inCone (mem_cone.mp hjc).2 hp₁
        have hp₂ic : InCone c p₂ := reach_inCone (mem_cone.mp hkc).2 hp₂
        have hp₁c : p₁ ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hp₁ic, hp₁ic⟩
        have hp₂c : p₂ ∈ cone c := mem_cone.mpr ⟨inCone_lt hs hp₂ic, hp₂ic⟩
        have hp₁le := reach_le hp₁
        have hqc : q ∈ cone c :=
          mem_cone.mpr ⟨by omega, InCone.step hp₁ic hqr₁ hql₁⟩
        have hqroot : q ≠ c.length - 1 := by omega
        have h12 : p₁ = p₂ :=
          cone_fanout_le_one f c hcomp hclen q hqc hqroot p₁ p₂ hp₁c hp₂c hqr₁ hqr₂
        subst h12
        exact ih p₁ (by omega) hp₁ hp₂

/-- **Cone-relative extraction (proved)**. -/
theorem cone_extractT_spec {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hclen : (cone c).card + 1 = 2 * (depSet f).card)
    (i₀ : Fin n) :
    ∀ (fuel w : ℕ), w < fuel → w ∈ cone c →
      ROT.ReadOnce (extractT c i₀ fuel w)
      ∧ (∀ x, (extractT c i₀ fuel w).eval x = wire c x w)
      ∧ (∀ i, i ∈ (extractT c i₀ fuel w).leaves →
          ∃ p, Reach c w p ∧ c.getD p (.cst false) = CGate.var i) := by
  obtain ⟨hedge, hnoself⟩ := cone_wiring f c hcomp hclen
  intro fuel
  induction fuel with
  | zero => intro w hw _; exact absurd hw (Nat.not_lt_zero w)
  | succ fuel ih =>
    intro w hw hwc
    have hwlt : w < c.length := (mem_cone.mp hwc).1
    cases hg : c.getD w (.cst false) with
    | cst b =>
      exfalso
      have hslots := (cone_census f c hcomp hclen).2 w hwc
        (by rintro ⟨i', hi'⟩; rw [hg] at hi'; simp at hi')
      rw [hg] at hslots
      simp [inSlots] at hslots
    | un op j =>
      exfalso
      have hslots := (cone_census f c hcomp hclen).2 w hwc
        (by rintro ⟨i', hi'⟩; rw [hg] at hi'; simp at hi')
      rw [hg] at hslots
      simp [inSlots] at hslots
    | var i =>
      rw [extractT_var hg]
      refine ⟨trivial, ?_, ?_⟩
      · intro x
        rw [wire_eq c x hwlt, hg]
        rfl
      · intro i' hi'
        have hii : i' = i := Finset.mem_singleton.mp hi'
        subst hii
        exact ⟨w, Reach.refl w, hg⟩
    | bin op j k =>
      have hjm : j ∈ gateReads (c.getD w (.cst false)) := by
        rw [hg]
        exact Finset.mem_insert_self j {k}
      have hkm : k ∈ gateReads (c.getD w (.cst false)) := by
        rw [hg]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self k)
      obtain ⟨hjw, hjc, -⟩ := hedge w hwc j hjm
      obtain ⟨hkw, hkc, -⟩ := hedge w hwc k hkm
      have hjk : j ≠ k := by
        intro he
        rw [he] at hg
        exact hnoself w hwc op k hg
      rw [extractT_bin hg]
      obtain ⟨hROj, hevj, hlvj⟩ := ih j (by omega) hjc
      obtain ⟨hROk, hevk, hlvk⟩ := ih k (by omega) hkc
      refine ⟨⟨?_, hROj, hROk⟩, ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro i hij hik
        obtain ⟨p₁, hrp₁, hgp₁⟩ := hlvj i hij
        obtain ⟨p₂, hrp₂, hgp₂⟩ := hlvk i hik
        have hp₁ic : InCone c p₁ := reach_inCone (mem_cone.mp hjc).2 hrp₁
        have hp₂ic : InCone c p₂ := reach_inCone (mem_cone.mp hkc).2 hrp₂
        have hp₁c : p₁ ∈ cone c :=
          mem_cone.mpr ⟨inCone_lt (by omega) hp₁ic, hp₁ic⟩
        have hp₂c : p₂ ∈ cone c :=
          mem_cone.mpr ⟨inCone_lt (by omega) hp₂ic, hp₂ic⟩
        have hpp : p₁ = p₂ :=
          cone_var_injective f c hcomp hclen hp₁c hp₂c hgp₁ hgp₂
        subst hpp
        exact cone_reach_not_both f c hcomp hclen hwc hjm hjw hkm hkw hjk
          c.length p₁ (by omega) hrp₁ hrp₂
      · intro x
        show op ((extractT c i₀ fuel j).eval x) ((extractT c i₀ fuel k).eval x)
          = wire c x w
        rw [wire_eq c x hwlt, hg]
        show op ((extractT c i₀ fuel j).eval x) ((extractT c i₀ fuel k).eval x)
          = op ((runFrom x [] (c.take w)).getD j false)
            ((runFrom x [] (c.take w)).getD k false)
        rw [wire_prefix c x hjw (le_of_lt hwlt),
          wire_prefix c x hkw (le_of_lt hwlt), hevj x, hevk x]
      · intro i hi
        rcases Finset.mem_union.mp hi with hij | hik
        · obtain ⟨p, hrp, hgp⟩ := hlvj i hij
          exact ⟨p, reach_trans (Reach.step (Reach.refl w) hjm hjw) hrp, hgp⟩
        · obtain ⟨p, hrp, hgp⟩ := hlvk i hik
          exact ⟨p, reach_trans (Reach.step (Reach.refl w) hkm hkw) hrp, hgp⟩

/-- **CONE-RELATIVE FLOOR REALIZATION (proved)**: a circuit whose cone attains the
floor computes a read-once tree.  Strictly stronger than `floor_realizes_ROT`. -/
theorem cone_realizes_ROT {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hclen : (cone c).card + 1 = 2 * (depSet f).card) :
    ∃ t : ROT n, ROT.ReadOnce t ∧ t.eval = f := by
  have hd : 1 ≤ (depSet f).card := by omega
  have hs : 0 < c.length := cone_floor_pos hclen
  obtain ⟨i₀, -⟩ := Finset.card_pos.mp hd
  have hroot : c.length - 1 ∈ cone c := mem_cone.mpr ⟨by omega, InCone.root⟩
  obtain ⟨hro, hev, -⟩ :=
    cone_extractT_spec f c hcomp hclen i₀ c.length (c.length - 1) (by omega) hroot
  refine ⟨extractT c i₀ c.length (c.length - 1), hro, ?_⟩
  funext x
  rw [hev x, ← output_eq_wire]
  exact hcomp x

/-- **The per-circuit unsplittable bound (proved)**: one unsplittable triple
restriction forces `2·deps ≤ |cone|` for every circuit computing `f`. -/
theorem cone_lb_of_unsplittable {n : ℕ} (f : (Fin n → Bool) → Bool)
    (i₁ i₂ i₃ : Fin n) (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃)
    (z : Fin n → Bool)
    (h1 : ¬ Split1 (fun a b c => f
      (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)))
    (h2 : ¬ Split2 (fun a b c => f
      (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)))
    (h3 : ¬ Split3 (fun a b c => f
      (Function.update (Function.update (Function.update z i₁ a) i₂ b) i₃ c)))
    {c : List (CGate n)} (hcomp : computes c f) (hs : 0 < c.length) :
    2 * (depSet f).card ≤ (cone c).card := by
  have hge := cone_card_ge hcomp hs
  rcases Nat.lt_or_ge ((cone c).card) (2 * (depSet f).card) with h | h
  · exfalso
    have hclen : (cone c).card + 1 = 2 * (depSet f).card := by omega
    obtain ⟨t, hro, hev⟩ := cone_realizes_ROT f c hcomp hclen
    have hsp := rot_split t hro i₁ i₂ i₃ h12 h13 h23 z
    rw [hev] at hsp
    rcases hsp with hs' | hs' | hs'
    · exact h1 hs'
    · exact h2 hs'
    · exact h3 hs'
  · exact h

/-- **The `AEm` cone bound (proved)**: every circuit computing `AEm m` has
`6m ≤ |cone|`.  In particular a 12-gate circuit for `AEm 2` has cone = the whole
circuit. -/
theorem AEm_cone_ge (m : ℕ) (hm : 1 ≤ m) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length) :
    6 * m ≤ (cone c).card := by
  have h0 : (0:ℕ) < 3 * m := by omega
  have h1 : (1:ℕ) < 3 * m := by omega
  have h2 : (2:ℕ) < 3 * m := by omega
  have hd : (depSet (AEm m)).card = 3 * m := by
    rw [depSet_AEm, Finset.card_univ, Fintype.card_fin]
  have hlb := cone_lb_of_unsplittable (AEm m) ⟨0, h0⟩ ⟨1, h1⟩ ⟨2, h2⟩
    (by intro he; simp at he) (by intro he; simp at he) (by intro he; simp at he)
    (fun _ => true)
    (by rw [AEm_gadget_allEq3 m h0 h1 h2]; exact allEq3_no_split_a)
    (by rw [AEm_gadget_allEq3 m h0 h1 h2]; exact allEq3_no_split_b)
    (by rw [AEm_gadget_allEq3 m h0 h1 h2]; exact allEq3_no_split_c)
    hcomp hs
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cone_realizes_ROT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cone_lb_of_unsplittable
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.AEm_cone_ge
