import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameKhrapchenko

/-!
# N-Frame: the witness-coherence measure — candidate, calibration, and the exact point of failure

The frontier needs a protocol measure that charges for witness coherence.  This file builds the natural candidate
and runs it into the ground *honestly* — locating precisely where it fails, which is the specification any working
measure must escape.

**The candidate.**  `satWitnesses x` = the set of satisfying assignments of the encoding `x`;
`witness diversity` of an Alice-side family `X` = the number of *distinct witness sets* over `X`.

**What works (proved).**
  `alice_measure_bound` — the abstract framework: any Alice-side measure that is split-subadditive and bounded by
        `D` on aligned rectangles satisfies `μ(X) ≤ 2^cost·D`.  (Bob's questions never increase an Alice-side
        measure — the witness-coherence intuition made formal.)
  `witnessDiv_split_le` — the candidate is split-subadditive.
  `witnessDiv_global` — over the pin family the candidate is exponential: `2^(m−2)` distinct witness sets.
        If aligned rectangles had small diversity, this would give `cost ≥ m − O(1)` — vastly superlogarithmic.

**Where it dies (proved).**
  `witness_coherence_leaf_blowup` — an **aligned rectangle** (all pairs differ at one common sign bit) whose
        Alice side carries `2^(m−3)` distinct witness sets.  A single one-bit answer serves exponentially many
        coherent witness states, so the leaf bound `D` must itself be `2^(m−3)`: the framework yields
        `cost ≥ log(2^(m−2)/2^(m−3)) = 1`.  **Formalized futility.**

## Honest scope — the specification extracted

The failure is structural, not accidental: the game only demands a *differing bit*, and a differing bit certifies
nothing about the witness.  Any working coherence measure must therefore charge Bob's side too — it must measure
what the protocol's rectangle *fails to determine about the witness jointly with the unsatisfiability witness on
Bob's side* — and must do so in a way that one bit of communication cannot halve.  Building such a measure is the
open research wall (it must also escape Razborov's convexity cap); it is named, specified by this file's no-go, and
not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The abstract Alice-side measure framework -/

/-- **The framework (proved)**: any split-subadditive Alice-side measure bounded by `D` on aligned rectangles has
`μ(X) ≤ 2^cost·D`.  Bob's questions never increase it. -/
theorem alice_measure_bound {n : ℕ} (p : KWProt n)
    (μ : Finset (Fin n → Bool) → ℕ)
    (hsub : ∀ (X : Finset (Fin n → Bool)) (q : (Fin n → Bool) → Bool),
      μ X ≤ μ (X.filter (fun x => q x = true)) + μ (X.filter (fun x => ¬(q x = true)))) :
    ∀ (X Y : Finset (Fin n → Bool)),
      (∀ x ∈ X, ∀ y ∈ Y, x (p.run x y) ≠ y (p.run x y)) →
      Y.Nonempty →
      ∀ D : ℕ,
      (∀ (i : Fin n) (A B : Finset (Fin n → Bool)), A ⊆ X → B ⊆ Y → B.Nonempty →
        (∀ x ∈ A, ∀ y ∈ B, x i ≠ y i) → μ A ≤ D) →
      μ X ≤ 2 ^ p.cost * D := by
  induction p with
  | out i =>
    intro X Y hsolve hY D hleaf
    have h := hleaf i X Y (Finset.Subset.refl _) (Finset.Subset.refl _) hY
      (fun x hx y hy => hsolve x hx y hy)
    show μ X ≤ 2 ^ 0 * D
    rw [pow_zero, one_mul]
    exact h
  | askA q l r ihl ihr =>
    intro X Y hsolve hY D hleaf
    have h1 := ihl (X.filter (fun x => q x = true)) Y (by
        intro x hx y hy
        have hxX := (Finset.mem_filter.mp hx).1
        have hxq := (Finset.mem_filter.mp hx).2
        have h := hsolve x hxX y hy
        rw [KWProt.run_askA, if_pos hxq] at h
        exact h) hY D
      (fun i A B hA hB hBne hal =>
        hleaf i A B (Finset.Subset.trans hA (Finset.filter_subset _ _)) hB hBne hal)
    have h2 := ihr (X.filter (fun x => ¬(q x = true))) Y (by
        intro x hx y hy
        have hxX := (Finset.mem_filter.mp hx).1
        have hxq := (Finset.mem_filter.mp hx).2
        have h := hsolve x hxX y hy
        rw [KWProt.run_askA, if_neg hxq] at h
        exact h) hY D
      (fun i A B hA hB hBne hal =>
        hleaf i A B (Finset.Subset.trans hA (Finset.filter_subset _ _)) hB hBne hal)
    have hs := hsub X q
    have hp1 : (2 : ℕ) ^ l.cost * D ≤ 2 ^ max l.cost r.cost * D :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
    have hp2 : (2 : ℕ) ^ r.cost * D ≤ 2 ^ max l.cost r.cost * D :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
    have hpow : (2 : ℕ) ^ (max l.cost r.cost + 1) * D
        = 2 ^ max l.cost r.cost * D + 2 ^ max l.cost r.cost * D := by
      rw [pow_succ]
      ring
    show μ X ≤ 2 ^ (max l.cost r.cost + 1) * D
    omega
  | askB q l r ihl ihr =>
    intro X Y hsolve hY D hleaf
    obtain ⟨y0, hy0⟩ := hY
    by_cases hq : q y0 = true
    · have h1 := ihl X (Y.filter (fun y => q y = true)) (by
          intro x hx y hy
          have hyY := (Finset.mem_filter.mp hy).1
          have hyq := (Finset.mem_filter.mp hy).2
          have h := hsolve x hx y hyY
          rw [KWProt.run_askB, if_pos hyq] at h
          exact h) ⟨y0, Finset.mem_filter.mpr ⟨hy0, hq⟩⟩ D
        (fun i A B hA hB hBne hal =>
          hleaf i A B hA (Finset.Subset.trans hB (Finset.filter_subset _ _)) hBne hal)
      have hp1 : (2 : ℕ) ^ l.cost * D ≤ 2 ^ (max l.cost r.cost + 1) * D :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
          (by have := Nat.le_max_left l.cost r.cost; omega))
      show μ X ≤ 2 ^ (max l.cost r.cost + 1) * D
      omega
    · have h2 := ihr X (Y.filter (fun y => ¬(q y = true))) (by
          intro x hx y hy
          have hyY := (Finset.mem_filter.mp hy).1
          have hyq := (Finset.mem_filter.mp hy).2
          have h := hsolve x hx y hyY
          rw [KWProt.run_askB, if_neg hyq] at h
          exact h) ⟨y0, Finset.mem_filter.mpr ⟨hy0, hq⟩⟩ D
        (fun i A B hA hB hBne hal =>
          hleaf i A B hA (Finset.Subset.trans hB (Finset.filter_subset _ _)) hBne hal)
      have hp2 : (2 : ℕ) ^ r.cost * D ≤ 2 ^ (max l.cost r.cost + 1) * D :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega)
          (by have := Nat.le_max_right l.cost r.cost; omega))
      show μ X ≤ 2 ^ (max l.cost r.cost + 1) * D
      omega

/-! ### The candidate: witness-set diversity -/

/-- The witness set of an encoding. -/
def satWitnesses (N : ℕ) (x : Fin N → Bool) : Finset (Fin (sat3V N) → Bool) :=
  Finset.univ.filter (fun a => sat3Eval N x a = true)

/-- **Split-subadditivity (proved)**: the candidate satisfies the framework's Alice-side axiom. -/
theorem witnessDiv_split_le (N : ℕ) (X : Finset (Fin N → Bool))
    (q : (Fin N → Bool) → Bool) :
    (X.image (satWitnesses N)).card
      ≤ ((X.filter (fun x => q x = true)).image (satWitnesses N)).card
        + ((X.filter (fun x => ¬(q x = true))).image (satWitnesses N)).card := by
  have h1 : X.image (satWitnesses N)
      = (X.filter (fun x => q x = true)).image (satWitnesses N)
        ∪ (X.filter (fun x => ¬(q x = true))).image (satWitnesses N) := by
    rw [← Finset.image_union, Finset.filter_union_filter_neg_eq]
  rw [h1]
  exact Finset.card_union_le _ _

/-! ### The pin reads and witness forcing -/

theorem pin_read_sel (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (hkv : k ≤ sat3V N) (bvec : Fin k → Bool) (u : Fin N → Bool) (j : Fin k) :
    sat3Patch N c (sat3Context N c hk bvec) u
      (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ j.val
        (by have := j.isLt; omega)) = true := by
  rw [sat3Patch_out N c _ u _
    (fun h => sat3PinClause_ne N c hk j (congrArg Fin.val h))]
  show decide _ = true
  rw [decide_eq_true_eq]
  left
  refine ⟨j, sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ j.val
    (by have := j.isLt; omega), Or.inl ?_⟩
  rw [sat3Bit_rem]
  show (0 : ℕ) * (sat3V N + 1) + j.val = j.val
  omega

theorem pin_read_miss (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (hkv : k ≤ sat3V N) (bvec : Fin k → Bool) (u : Fin N → Bool) (j : Fin k)
    (i : Fin (sat3V N)) (hij : i ≠ (⟨j.val, by have := j.isLt; omega⟩ : Fin (sat3V N))) :
    sat3Patch N c (sat3Context N c hk bvec) u
      (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ i.val
        (by have := i.isLt; omega)) = false := by
  rw [sat3Patch_out N c _ u _
    (fun h => sat3PinClause_ne N c hk j (congrArg Fin.val h))]
  have hd := sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ i.val
    (by have := i.isLt; omega)
  have hr : (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ i.val
      (by have := i.isLt; omega)).val % sat3D N = i.val := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
  · rw [hd] at hdiv
    have hjj' := sat3PinClause_val_inj N c hk hdiv
    subst hjj'
    rcases hrem with h | ⟨h, -⟩
    · rw [hr] at h
      exact hij (Fin.ext h)
    · rw [hr] at h
      have := i.isLt
      omega
  · exact hnot j hd

theorem pin_read_sign (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (hkv : k ≤ sat3V N) (bvec : Fin k → Bool) (u : Fin N → Bool) (j : Fin k) :
    sat3Patch N c (sat3Context N c hk bvec) u
      (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N) (by omega))
      = decide (bvec j = false) := by
  rw [sat3Patch_out N c _ u _
    (fun h => sat3PinClause_ne N c hk j (congrArg Fin.val h))]
  have hd := sat3Bit_clause N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N) (by omega)
  have hr : (sat3Bit N (sat3PinClause N c hk j) ⟨0, by omega⟩ (sat3V N)
      (by omega)).val % sat3D N = sat3V N := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
    omega
  cases hbj : bvec j
  · show decide _ = true
    rw [decide_eq_true_eq]
    left
    exact ⟨j, hd, Or.inr ⟨hr, hbj⟩⟩
  · show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
    · rw [hd] at hdiv
      have hjj' := sat3PinClause_val_inj N c hk hdiv
      subst hjj'
      rcases hrem with h | ⟨-, hbf⟩
      · rw [hr] at h
        have := j.isLt
        omega
      · rw [hbj] at hbf
        exact Bool.noConfusion hbf
    · exact hnot j hd

theorem pin_read_dead (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (hkv : k ≤ sat3V N) (bvec : Fin k → Bool) (u : Fin N → Bool) (j : Fin k)
    (t : Fin 3) (ht : 1 ≤ t.val) (i : Fin (sat3V N)) :
    sat3Patch N c (sat3Context N c hk bvec) u
      (sat3Bit N (sat3PinClause N c hk j) t i.val (by have := i.isLt; omega)) = false := by
  rw [sat3Patch_out N c _ u _
    (fun h => sat3PinClause_ne N c hk j (congrArg Fin.val h))]
  have hd := sat3Bit_clause N (sat3PinClause N c hk j) t i.val (by have := i.isLt; omega)
  have hr := sat3Bit_rem N (sat3PinClause N c hk j) t i.val (by have := i.isLt; omega)
  have hbound : sat3V N + 1 ≤ t.val * (sat3V N + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (⟨j', hdiv, hrem⟩ | ⟨-, -, hnot, -⟩)
  · have hj' := j'.isLt
    rcases hrem with h | ⟨h, -⟩ <;> rw [hr] at h <;> omega
  · exact hnot j hd

/-- **Witness forcing (proved)**: any satisfying assignment of a pin-context instance agrees with the pin vector —
regardless of the block-`c` probe. -/
theorem pin_forces (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (hkv : k ≤ sat3V N) (bvec : Fin k → Bool) (u : Fin N → Bool)
    (a : Fin (sat3V N) → Bool)
    (ha : sat3Eval N (sat3Patch N c (sat3Context N c hk bvec) u) a = true)
    (j : Fin k) :
    a ⟨j.val, by have := j.isLt; omega⟩ = bvec j := by
  have hlit := sat3Eval_clause_true N _ a ha (sat3PinClause N c hk j)
  have hiff := sat3Clause_single_iff N
    (sat3Patch N c (sat3Context N c hk bvec) u) a (sat3PinClause N c hk j)
    ⟨j.val, by have := j.isLt; omega⟩
    (pin_read_sel N c hk hkv bvec u j)
    (pin_read_miss N c hk hkv bvec u j)
    (pin_read_dead N c hk hkv bvec u j ⟨1, by omega⟩ (by show (1 : ℕ) ≤ 1; omega))
    (pin_read_dead N c hk hkv bvec u j ⟨2, by omega⟩ (by show (1 : ℕ) ≤ 2; omega))
  rw [pin_read_sign N c hk hkv bvec u j] at hiff
  exact xor_decide_eq _ _ (hiff.mp hlit)

/-- The probe's sign bit reads back the probe sign — for any context. -/
theorem probe_sign_read (N : ℕ) (c : Fin (sat3M N)) (ctx : Fin N → Bool)
    (vj : Fin (sat3V N)) (sgn : Bool) :
    sat3Patch N c ctx (sat3Probe N vj sgn) (sat3SignBit N c) = sgn := by
  show sat3Patch N c ctx (sat3Probe N vj sgn)
      (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)) = sgn
  rw [sat3Patch_own N c ctx _]
  have hr : (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
      = sat3V N := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
    omega
  cases sgn
  · show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (h | ⟨-, h⟩)
    · rw [hr] at h
      have := vj.isLt
      omega
    · exact Bool.noConfusion h
  · show decide _ = true
    rw [decide_eq_true_eq]
    right
    exact ⟨hr, rfl⟩

/-! ### The global diversity and the leaf blowup -/

/-- **Global witness diversity (proved)**: `2^(m−2)` distinct witness sets over the pin family — the candidate is
exponential globally. -/
theorem witnessDiv_global (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) :
    ∃ X : Finset (Fin N → Bool), (∀ x ∈ X, sat3Family N x = true) ∧
      2 ^ (sat3M N - 2) ≤ (X.image (satWitnesses N)).card := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvj
  set F : (Fin (sat3M N - 2) → Bool) → (Fin N → Bool) := fun b =>
    sat3Patch N c (sat3Context N c hk b) (sat3Probe N vj (!(b j₀))) with hF
  have hsat : ∀ b, sat3Family N (F b) = true := by
    intro b
    have h := sat3Context_probe_eval N hv hk hkv c b j₀ vj rfl (!(b j₀))
    rw [hF]
    show sat3Family N (sat3Patch N c (sat3Context N c hk b)
      (sat3Probe N vj (!(b j₀)))) = true
    rw [h]
    cases b j₀ <;> rfl
  have hforce : ∀ (b : Fin (sat3M N - 2) → Bool) (a : Fin (sat3V N) → Bool),
      a ∈ satWitnesses N (F b) → ∀ j : Fin (sat3M N - 2),
      a ⟨j.val, by have := j.isLt; omega⟩ = b j := by
    intro b a ha j
    have haE := (Finset.mem_filter.mp ha).2
    exact pin_forces N c hk hkv b _ a haE j
  have hinj : Set.InjOn (fun b => satWitnesses N (F b))
      (Finset.univ : Finset (Fin (sat3M N - 2) → Bool)) := by
    intro b hb b' hb' hW
    have hW' : satWitnesses N (F b) = satWitnesses N (F b') := hW
    -- the witness set is nonempty
    obtain ⟨a, haE⟩ := (sat3Family_iff N (F b)).mp (hsat b)
    have haW : a ∈ satWitnesses N (F b) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, haE⟩
    have haW' : a ∈ satWitnesses N (F b') := by
      rw [← hW']
      exact haW
    funext j
    rw [← hforce b a haW j, ← hforce b' a haW' j]
  refine ⟨Finset.univ.image F, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
    exact hsat b
  · rw [Finset.image_image]
    have h2 : (Finset.univ.image (satWitnesses N ∘ F)).card
        = (Finset.univ : Finset (Fin (sat3M N - 2) → Bool)).card :=
      Finset.card_image_of_injOn hinj
    rw [h2, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **THE LEAF BLOWUP (proved)**: an aligned rectangle — all pairs differ at one common sign bit — whose Alice side
carries `2^(m−3)` distinct witness sets.  One answer bit serves exponentially many coherent witness states: the
witness-diversity measure cannot be leaf-normalized, and the framework bound is vacuous for it. -/
theorem witness_coherence_leaf_blowup (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) :
    ∃ (X : Finset (Fin N → Bool)) (y : Fin N → Bool),
      (∀ x ∈ X, sat3Family N x = true) ∧ sat3Family N y = false ∧
      (∀ x ∈ X, x (sat3SignBit N c) ≠ y (sat3SignBit N c)) ∧
      2 ^ (sat3M N - 3) ≤ (X.image (satWitnesses N)).card := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvj
  set F : (Fin (sat3M N - 2) → Bool) → (Fin N → Bool) := fun b =>
    sat3Patch N c (sat3Context N c hk b) (sat3Probe N vj true) with hF
  set S : Finset (Fin (sat3M N - 2) → Bool) :=
    Finset.univ.filter (fun b => b j₀ = false) with hS
  -- |S| = 2^(m−3) via the flip involution
  set φ : (Fin (sat3M N - 2) → Bool) → (Fin (sat3M N - 2) → Bool) :=
    fun b => Function.update b j₀ (!(b j₀)) with hφ
  have hφφ : ∀ b, φ (φ b) = b := by
    intro b
    show Function.update (Function.update b j₀ (!(b j₀))) j₀
        (!(Function.update b j₀ (!(b j₀)) j₀)) = b
    rw [Function.update_self, Bool.not_not, Function.update_idem,
      Function.update_eq_self]
  have hφinj : Function.Injective φ := by
    intro a b h
    have := congrArg φ h
    rw [hφφ, hφφ] at this
    exact this
  have hScard : S.card = 2 ^ (sat3M N - 3) := by
    set T : Finset (Fin (sat3M N - 2) → Bool) :=
      Finset.univ.filter (fun b => ¬(b j₀ = false)) with hT
    have hsum : S.card + T.card = 2 ^ (sat3M N - 2) := by
      have h := Finset.filter_card_add_filter_neg_card_eq_card
        (s := (Finset.univ : Finset (Fin (sat3M N - 2) → Bool)))
        (p := fun b => b j₀ = false)
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
      exact h
    have hST : S.card = T.card := by
      have h1 : S.image φ ⊆ T := by
        intro b hb
        obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
        have hb0v := (Finset.mem_filter.mp hb0).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        show ¬(Function.update b0 j₀ (!(b0 j₀)) j₀ = false)
        rw [Function.update_self, hb0v]
        decide
      have h2 : T.image φ ⊆ S := by
        intro b hb
        obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
        have hb0v : b0 j₀ = true := by
          have := (Finset.mem_filter.mp hb0).2
          cases hcc : b0 j₀
          · exact absurd hcc this
          · rfl
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        show Function.update b0 j₀ (!(b0 j₀)) j₀ = false
        rw [Function.update_self, hb0v]
        rfl
      have hc1 : S.card ≤ T.card := by
        rw [← Finset.card_image_of_injective S hφinj]
        exact Finset.card_le_card h1
      have hc2 : T.card ≤ S.card := by
        rw [← Finset.card_image_of_injective T hφinj]
        exact Finset.card_le_card h2
      omega
    have hpow : (2 : ℕ) ^ (sat3M N - 2) = 2 * 2 ^ (sat3M N - 3) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  -- satisfiability on S, the unsatisfiable partner, alignment
  have hsat : ∀ b ∈ S, sat3Family N (F b) = true := by
    intro b hb
    have hb0 := (Finset.mem_filter.mp hb).2
    have h := sat3Context_probe_eval N hv hk hkv c b j₀ vj rfl true
    rw [hF]
    show sat3Family N (sat3Patch N c (sat3Context N c hk b) (sat3Probe N vj true)) = true
    rw [h, hb0]
    rfl
  set y : Fin N → Bool :=
    sat3Patch N c (sat3Context N c hk (fun _ : Fin (sat3M N - 2) => false))
      (sat3Probe N vj false) with hy
  have hyuns : sat3Family N y = false := by
    have h := sat3Context_probe_eval N hv hk hkv c
      (fun _ : Fin (sat3M N - 2) => false) j₀ vj rfl false
    rw [hy]
    exact h
  have halign : ∀ b : Fin (sat3M N - 2) → Bool,
      F b (sat3SignBit N c) ≠ y (sat3SignBit N c) := by
    intro b
    rw [hF, hy]
    show sat3Patch N c (sat3Context N c hk b) (sat3Probe N vj true) (sat3SignBit N c)
        ≠ sat3Patch N c (sat3Context N c hk (fun _ => false)) (sat3Probe N vj false)
          (sat3SignBit N c)
    rw [probe_sign_read, probe_sign_read]
    decide
  -- witness-set diversity on S
  have hforce : ∀ (b : Fin (sat3M N - 2) → Bool) (a : Fin (sat3V N) → Bool),
      a ∈ satWitnesses N (F b) → ∀ j : Fin (sat3M N - 2),
      a ⟨j.val, by have := j.isLt; omega⟩ = b j := by
    intro b a ha j
    have haE := (Finset.mem_filter.mp ha).2
    exact pin_forces N c hk hkv b _ a haE j
  have hinj : Set.InjOn (fun b => satWitnesses N (F b)) S := by
    intro b hb b' hb' hW
    have hW' : satWitnesses N (F b) = satWitnesses N (F b') := hW
    obtain ⟨a, haE⟩ := (sat3Family_iff N (F b)).mp (hsat b hb)
    have haW : a ∈ satWitnesses N (F b) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, haE⟩
    have haW' : a ∈ satWitnesses N (F b') := by
      rw [← hW']
      exact haW
    funext j
    rw [← hforce b a haW j, ← hforce b' a haW' j]
  refine ⟨S.image F, y, ?_, hyuns, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact hsat b hb
  · intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
    exact halign b
  · rw [Finset.image_image]
    have h2 : (S.image (satWitnesses N ∘ F)).card = S.card :=
      Finset.card_image_of_injOn hinj
    rw [h2, hScard]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.alice_measure_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.witnessDiv_split_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.pin_forces
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.witnessDiv_global
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.witness_coherence_leaf_blowup
