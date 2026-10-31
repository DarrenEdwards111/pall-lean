import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameAlignedCover

/-!
# N-Frame: the joint witness–refutation coherence candidate — built, calibrated, and broken on schedule

HAL's spec: a measure tracking how Alice's satisfying-witness structure remains entangled with Bob's refutation
structure across `X × Y`, tested immediately against the known no-go patterns.

**The candidate.**  Alice's structure: `satWitnesses x` (witness sets).  Bob's structure: `nearWitnesses y` — the
assignments failing **at most one clause** of the unsat encoding `y`: its coherent almost-witnesses, the genuine
refutation skeleton (for the pin families, `y`'s near-witnesses are exactly the pin-coherent assignments).
`jointCoherence X Y := min(#distinct witness sets over X, #distinct near-witness sets over Y)` — two-sided by
construction: trivial on either side kills it, so the Alice-only blowup (singleton `Y`) no longer applies.

**Calibration, positive (proved).**  `sat3_joint_coherence_large`: on the sat/unsat pin families both sides carry
`2^(m−3)` distinct structures — near-witness sets are forced (`near_forces`: an assignment failing at most one
clause must match the pin vector off the probe variable, else two distinct clauses fail) and nonempty
(`Fx`-witnesses fail only clause `c` under `Gy`).

**The break (proved).**  `joint_coherence_leaf_break`: the *same* two families form an **aligned rectangle** — every
cross pair differs at the block-`c` sign bit — with `jointCoherence ≥ 2^(m−3)`.  The hoped-for decisive theorem
(`aligned rectangle ⇒ jointCoherence small`) is **false for this candidate**: one answer bit serves exponentially
many entangled witness/refutation states on *both* sides simultaneously.

## Honest scope — what the break teaches

The two-sided diversity paradigm dies at the same leaf as the one-sided one: alignment constrains a single
coordinate and is compatible with maximal coherence on both sides.  Any surviving measure must be *relative* — it
must measure the residual game difficulty inside the rectangle, not the structure present in it — which is exactly
the KRW-style inductive frontier.  The universal object remains the aligned-cover number (previous file); its
superpolynomial bounding for sat3 via multi-bit fooling families is the open wall, named and not claimed.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Bob's refutation structure: near-witnesses -/

/-- The clauses an assignment fails. -/
def failedClauses (N : ℕ) (y : Fin N → Bool) (a : Fin (sat3V N) → Bool) :
    Finset (Fin (sat3M N)) :=
  Finset.univ.filter (fun cl => ¬∃ t, sat3Lit N y a cl t = true)

/-- The near-witnesses of an encoding: assignments failing at most one clause — the coherent almost-witnesses. -/
def nearWitnesses (N : ℕ) (y : Fin N → Bool) : Finset (Fin (sat3V N) → Bool) :=
  Finset.univ.filter (fun a => (failedClauses N y a).card ≤ 1)

theorem mem_failedClauses (N : ℕ) (y : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (cl : Fin (sat3M N)) :
    cl ∈ failedClauses N y a ↔ ¬∃ t, sat3Lit N y a cl t = true :=
  Finset.mem_filter.trans (and_iff_right (Finset.mem_univ cl))

/-- **The joint witness–refutation coherence candidate.** -/
def jointCoherence (N : ℕ) (X Y : Finset (Fin N → Bool)) : ℕ :=
  min ((X.image (satWitnesses N)).card) ((Y.image (nearWitnesses N)).card)

/-! ### Clause-local evaluation tools -/

theorem xor_decide_iff (u w : Bool) : (xor u (decide (w = false)) = true) ↔ u = w := by
  cases u <;> cases w <;> decide

/-- A clause's evaluation depends only on its own block's bits. -/
theorem sat3Lit_congr (N : ℕ) (x x' : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (cl : Fin (sat3M N)) (t : Fin 3)
    (h : ∀ (f : ℕ) (hf : f < sat3V N + 1), x (sat3Bit N cl t f hf) = x' (sat3Bit N cl t f hf)) :
    sat3Lit N x a cl t = sat3Lit N x' a cl t := by
  unfold sat3Lit
  congr 1
  funext i
  rw [h i.val (by have := i.isLt; omega), h (sat3V N) (by omega)]

/-- Off the probed block, two probes leave the patch identical. -/
theorem patch_probe_agree_offc (N : ℕ) (c : Fin (sat3M N)) (ctx : Fin N → Bool)
    (vj : Fin (sat3V N)) (sgn sgn' : Bool) (cl : Fin (sat3M N)) (hcl : cl ≠ c)
    (t : Fin 3) (f : ℕ) (hf : f < sat3V N + 1) :
    sat3Patch N c ctx (sat3Probe N vj sgn) (sat3Bit N cl t f hf)
      = sat3Patch N c ctx (sat3Probe N vj sgn') (sat3Bit N cl t f hf) := by
  rw [sat3Patch_out N c ctx _ cl hcl, sat3Patch_out N c ctx _ cl hcl]

/-! ### Probe-block reads (sign-generic) -/

theorem probe_read_sel_hit (N : ℕ) (c : Fin (sat3M N)) (ctx : Fin N → Bool)
    (vj : Fin (sat3V N)) (sgn : Bool) :
    sat3Patch N c ctx (sat3Probe N vj sgn)
      (sat3Bit N c ⟨0, by omega⟩ vj.val (by have := vj.isLt; omega)) = true := by
  rw [sat3Patch_own N c ctx _]
  show decide _ = true
  rw [decide_eq_true_eq]
  left
  rw [sat3Bit_rem]
  show (0 : ℕ) * (sat3V N + 1) + vj.val = vj.val
  omega

theorem probe_read_miss (N : ℕ) (c : Fin (sat3M N)) (ctx : Fin N → Bool)
    (vj : Fin (sat3V N)) (sgn : Bool) (i : Fin (sat3V N)) (hi : i ≠ vj) :
    sat3Patch N c ctx (sat3Probe N vj sgn)
      (sat3Bit N c ⟨0, by omega⟩ i.val (by have := i.isLt; omega)) = false := by
  rw [sat3Patch_own N c ctx _]
  have hr : (sat3Bit N c ⟨0, by omega⟩ i.val (by have := i.isLt; omega)).val % sat3D N
      = i.val := by
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + i.val = i.val
    omega
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (h | ⟨h, -⟩)
  · rw [hr] at h
    exact hi (Fin.ext h)
  · rw [hr] at h
    have := i.isLt
    omega

theorem probe_read_dead (N : ℕ) (c : Fin (sat3M N)) (ctx : Fin N → Bool)
    (vj : Fin (sat3V N)) (sgn : Bool) (t : Fin 3) (ht : 1 ≤ t.val) (i : Fin (sat3V N)) :
    sat3Patch N c ctx (sat3Probe N vj sgn)
      (sat3Bit N c t i.val (by have := i.isLt; omega)) = false := by
  rw [sat3Patch_own N c ctx _]
  have hr := sat3Bit_rem N c t i.val (by have := i.isLt; omega)
  have hbound : sat3V N + 1 ≤ t.val * (sat3V N + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hvjlt := vj.isLt
  have hilt := i.isLt
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro (h | ⟨h, -⟩) <;> rw [hr] at h <;> omega

/-- The probed clause holds iff the probe literal does. -/
theorem probe_clause_iff (N : ℕ) (c : Fin (sat3M N)) (ctx : Fin N → Bool)
    (vj : Fin (sat3V N)) (sgn : Bool) (a : Fin (sat3V N) → Bool) :
    (∃ t, sat3Lit N (sat3Patch N c ctx (sat3Probe N vj sgn)) a c t = true)
      ↔ xor (a vj) sgn = true := by
  have hiff := sat3Clause_single_iff N (sat3Patch N c ctx (sat3Probe N vj sgn)) a c vj
    (probe_read_sel_hit N c ctx vj sgn) (probe_read_miss N c ctx vj sgn)
    (probe_read_dead N c ctx vj sgn ⟨1, by omega⟩ (by show (1 : ℕ) ≤ 1; omega))
    (probe_read_dead N c ctx vj sgn ⟨2, by omega⟩ (by show (1 : ℕ) ≤ 2; omega))
  rw [show sat3Patch N c ctx (sat3Probe N vj sgn)
      (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)) = sgn
    from probe_sign_read N c ctx vj sgn] at hiff
  exact hiff

/-- A pin clause holds iff the assignment matches the pin. -/
theorem pin_clause_iff (N : ℕ) (c : Fin (sat3M N)) {k : ℕ} (hk : k + 1 ≤ sat3M N)
    (hkv : k ≤ sat3V N) (bvec : Fin k → Bool) (u : Fin N → Bool)
    (a : Fin (sat3V N) → Bool) (j : Fin k) :
    (∃ t, sat3Lit N (sat3Patch N c (sat3Context N c hk bvec) u) a
        (sat3PinClause N c hk j) t = true)
      ↔ a ⟨j.val, by have := j.isLt; omega⟩ = bvec j := by
  have hiff := sat3Clause_single_iff N
    (sat3Patch N c (sat3Context N c hk bvec) u) a (sat3PinClause N c hk j)
    ⟨j.val, by have := j.isLt; omega⟩
    (pin_read_sel N c hk hkv bvec u j)
    (pin_read_miss N c hk hkv bvec u j)
    (pin_read_dead N c hk hkv bvec u j ⟨1, by omega⟩ (by show (1 : ℕ) ≤ 1; omega))
    (pin_read_dead N c hk hkv bvec u j ⟨2, by omega⟩ (by show (1 : ℕ) ≤ 2; omega))
  rw [pin_read_sign N c hk hkv bvec u j] at hiff
  rw [hiff]
  exact xor_decide_iff _ _

/-! ### The joint theorem: large coherence on an aligned rectangle -/

/-- **The candidate built and immediately broken (proved)**: sat/unsat pin families forming an **aligned
rectangle** (every cross pair differs at the block-`c` sign bit) with joint witness–refutation coherence
`≥ 2^(m−3)` on **both** sides.  The decisive hoped-for bound `aligned ⇒ jointCoherence small` is false. -/
theorem joint_coherence_leaf_break (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) :
    ∃ X Y : Finset (Fin N → Bool),
      (∀ x ∈ X, sat3Family N x = true) ∧ (∀ y ∈ Y, sat3Family N y = false) ∧
      (∀ x ∈ X, ∀ y ∈ Y, x (sat3SignBit N c) ≠ y (sat3SignBit N c)) ∧
      2 ^ (sat3M N - 3) ≤ jointCoherence N X Y := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvj
  set Fx : (Fin (sat3M N - 2) → Bool) → (Fin N → Bool) := fun b =>
    sat3Patch N c (sat3Context N c hk b) (sat3Probe N vj true) with hFx
  set Gy : (Fin (sat3M N - 2) → Bool) → (Fin N → Bool) := fun b =>
    sat3Patch N c (sat3Context N c hk b) (sat3Probe N vj false) with hGy
  set S : Finset (Fin (sat3M N - 2) → Bool) :=
    Finset.univ.filter (fun b => b j₀ = false) with hS
  -- |S| = 2^(m−3), by the flip involution (as in the one-sided blowup)
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
  -- values of the two families
  have hxsat : ∀ b ∈ S, sat3Family N (Fx b) = true := by
    intro b hb
    have hb0 := (Finset.mem_filter.mp hb).2
    have h := sat3Context_probe_eval N hv hk hkv c b j₀ vj rfl true
    rw [hFx]
    show sat3Family N (sat3Patch N c (sat3Context N c hk b) (sat3Probe N vj true)) = true
    rw [h, hb0]
    rfl
  have hyuns : ∀ b ∈ S, sat3Family N (Gy b) = false := by
    intro b hb
    have hb0 := (Finset.mem_filter.mp hb).2
    have h := sat3Context_probe_eval N hv hk hkv c b j₀ vj rfl false
    rw [hGy]
    show sat3Family N (sat3Patch N c (sat3Context N c hk b) (sat3Probe N vj false)) = false
    rw [h, hb0]
    rfl
  -- Alice-side diversity: witness sets are pin-forced (as in the one-sided blowup)
  have hAforce : ∀ (b : Fin (sat3M N - 2) → Bool) (a : Fin (sat3V N) → Bool),
      a ∈ satWitnesses N (Fx b) → ∀ j : Fin (sat3M N - 2),
      a ⟨j.val, by have := j.isLt; omega⟩ = b j := by
    intro b a ha j
    have haE := (Finset.mem_filter.mp ha).2
    exact pin_forces N c hk hkv b _ a haE j
  have hAinj : Set.InjOn (fun b => satWitnesses N (Fx b)) S := by
    intro b hb b' hb' hW
    have hW' : satWitnesses N (Fx b) = satWitnesses N (Fx b') := hW
    obtain ⟨a, haE⟩ := (sat3Family_iff N (Fx b)).mp (hxsat b hb)
    have haW : a ∈ satWitnesses N (Fx b) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, haE⟩
    have haW' : a ∈ satWitnesses N (Fx b') := by
      rw [← hW']
      exact haW
    funext j
    rw [← hAforce b a haW j, ← hAforce b' a haW' j]
  -- Bob-side structure: near-witness nonemptiness with full pins
  have hBnonempty : ∀ b ∈ S, ∃ a, a ∈ nearWitnesses N (Gy b) ∧
      ∀ j : Fin (sat3M N - 2), a ⟨j.val, by have := j.isLt; omega⟩ = b j := by
    intro b hb
    obtain ⟨a, haE⟩ := (sat3Family_iff N (Fx b)).mp (hxsat b hb)
    have hpins : ∀ j : Fin (sat3M N - 2),
        a ⟨j.val, by have := j.isLt; omega⟩ = b j :=
      fun j => pin_forces N c hk hkv b _ a haE j
    have hsub : failedClauses N (Gy b) a ⊆ {c} := by
      intro cl hcl
      rw [Finset.mem_singleton]
      by_contra hne
      rw [mem_failedClauses] at hcl
      apply hcl
      obtain ⟨t, ht⟩ := sat3Eval_clause_true N _ a haE cl
      refine ⟨t, ?_⟩
      rw [sat3Lit_congr N (Gy b) (Fx b) a cl t
        (fun f hf => patch_probe_agree_offc N c (sat3Context N c hk b) vj false true
          cl hne t f hf)]
      exact ht
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hpins⟩
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Finset.card_singleton]
  -- Bob-side forcing: a near-witness matches the pins off the probe variable
  have hBforce : ∀ b ∈ S, ∀ a, a ∈ nearWitnesses N (Gy b) →
      ∀ j : Fin (sat3M N - 2), j ≠ j₀ →
      a ⟨j.val, by have := j.isLt; omega⟩ = b j := by
    intro b hb a ha j hj
    have hb0 := (Finset.mem_filter.mp hb).2
    have hcard := (Finset.mem_filter.mp ha).2
    by_contra hja
    have hfail_j : sat3PinClause N c hk j ∈ failedClauses N (Gy b) a := by
      rw [mem_failedClauses]
      intro hex
      exact hja ((pin_clause_iff N c hk hkv b _ a j).mp hex)
    by_cases hva : a vj = true
    · have hfail_j0 : sat3PinClause N c hk j₀ ∈ failedClauses N (Gy b) a := by
        rw [mem_failedClauses]
        intro hex
        have h0 := (pin_clause_iff N c hk hkv b _ a j₀).mp hex
        rw [hb0] at h0
        have hvjeq : vj = (⟨j₀.val, by have := j₀.isLt; omega⟩ : Fin (sat3V N)) :=
          Fin.ext rfl
        rw [← hvjeq] at h0
        rw [hva] at h0
        exact Bool.noConfusion h0
      have heq := Finset.card_le_one.mp hcard _ hfail_j _ hfail_j0
      exact hj (sat3PinClause_val_inj N c hk (congrArg Fin.val heq))
    · have hva' : a vj = false := by
        cases hcc : a vj
        · rfl
        · exact absurd hcc hva
      have hfail_c : c ∈ failedClauses N (Gy b) a := by
        rw [mem_failedClauses]
        intro hex
        have h0 := (probe_clause_iff N c (sat3Context N c hk b) vj false a).mp hex
        rw [Bool.xor_false, hva'] at h0
        exact Bool.noConfusion h0
      have heq := Finset.card_le_one.mp hcard _ hfail_j _ hfail_c
      exact sat3PinClause_ne N c hk j (congrArg Fin.val heq)
  -- Bob-side diversity
  have hBinj : Set.InjOn (fun b => nearWitnesses N (Gy b)) S := by
    intro b hb b' hb' hW
    have hW' : nearWitnesses N (Gy b) = nearWitnesses N (Gy b') := hW
    obtain ⟨a, haN, hpins⟩ := hBnonempty b hb
    have haN' : a ∈ nearWitnesses N (Gy b') := by
      rw [← hW']
      exact haN
    funext j
    by_cases hj : j = j₀
    · subst hj
      have h1 := (Finset.mem_filter.mp hb).2
      have h2 := (Finset.mem_filter.mp hb').2
      rw [h1, h2]
    · rw [← hpins j, hBforce b' hb' a haN' j hj]
  -- alignment at the sign bit
  have halign : ∀ b ∈ S, ∀ b' ∈ S,
      Fx b (sat3SignBit N c) ≠ Gy b' (sat3SignBit N c) := by
    intro b hb b' hb'
    rw [hFx, hGy]
    show sat3Patch N c (sat3Context N c hk b) (sat3Probe N vj true) (sat3SignBit N c)
        ≠ sat3Patch N c (sat3Context N c hk b') (sat3Probe N vj false) (sat3SignBit N c)
    rw [probe_sign_read, probe_sign_read]
    decide
  -- assemble
  refine ⟨S.image Fx, S.image Gy, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact hxsat b hb
  · intro y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hyuns b hb
  · intro x hx y hy
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hy
    exact halign b hb b' hb'
  · have hA : ((S.image Fx).image (satWitnesses N)).card = 2 ^ (sat3M N - 3) := by
      rw [Finset.image_image]
      have h2 : (S.image (satWitnesses N ∘ Fx)).card = S.card :=
        Finset.card_image_of_injOn hAinj
      rw [h2, hScard]
    have hB : ((S.image Gy).image (nearWitnesses N)).card = 2 ^ (sat3M N - 3) := by
      rw [Finset.image_image]
      have h2 : (S.image (nearWitnesses N ∘ Gy)).card = S.card :=
        Finset.card_image_of_injOn hBinj
      rw [h2, hScard]
    show 2 ^ (sat3M N - 3) ≤ min _ _
    rw [hA, hB]
    omega

/-- **The positive calibration (proved)**: the pin families carry joint witness–refutation coherence `2^(m−3)` —
the candidate sees SAT's entangled structure at exponential scale. -/
theorem sat3_joint_coherence_large (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) :
    ∃ X Y : Finset (Fin N → Bool),
      (∀ x ∈ X, sat3Family N x = true) ∧ (∀ y ∈ Y, sat3Family N y = false) ∧
      2 ^ (sat3M N - 3) ≤ jointCoherence N X Y := by
  obtain ⟨X, Y, hX, hY, -, hcoh⟩ := joint_coherence_leaf_break N hv hm3 c
  exact ⟨X, Y, hX, hY, hcoh⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.pin_clause_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.probe_clause_iff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.joint_coherence_leaf_break
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_joint_coherence_large
