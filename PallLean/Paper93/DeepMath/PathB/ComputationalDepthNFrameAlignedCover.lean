import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameWitnessCoherence

/-!
# N-Frame: the universal measure — aligned covers, fooling sets, and the sharpened core

The extracted specification asked for a measure charging both sides, un-halvable per bit, beyond the convexity cap.
**The honest resolution, formalized: such a measure exists trivially — the aligned-cover number χ itself** (it is
split-subadditive with leaf value 1, and `log χ` is the *optimal* rectangle bound).  The wall was never the
measure's existence; it is *bounding* `χ(sat3)`.  This file completes that reframing with proofs.

  `IsAlignedCover` / `protocol_cover` — **PROVED**: a protocol of cost `c` yields an aligned cover of size `≤ 2^c`;
        hence any cover lower bound is a communication lower bound.
  `KWFooling` / `fooling_le_cover` — **PROVED, the χ tool**: a fooling family (no two pairs fit one aligned
        rectangle — the four cross-difference conditions fail at every coordinate) lower-bounds every cover.
  `sat3_fooling` / `sat3_cover_lb` — **PROVED, calibration**: the `m·v` selector pairs are a fooling family
        (their singleton difference-sets force distinct alignment bits), so every aligned cover of the SAT game has
        size `≥ m·v ≈ N/3` — matching the forcing bound, as it must.

## Honest scope — the sharpened core

Singleton-difference fooling families cap at `N` (there are only `N` bits to force).  Therefore a superpolynomial
`χ(sat3)` — the one remaining open question, now in its final combinatorial form — requires a fooling family of
pairs with **large difference sets**, where the work is done by the *cross* conditions: satisfiable/unsatisfiable
encoding pairs `(x_s, y_s)` such that for all `s ≠ t` and every coordinate `i`, one of the four differences
`x_s i ≠ y_s i`, `x_s i ≠ y_t i`, `x_t i ≠ y_s i`, `x_t i ≠ y_t i` fails.  Superpolynomially many mutually
non-corectangular SAT boundary pairs = superlogarithmic game communication = superpolynomial formula size for SAT.
Constructing them is the research wall — named, specified by `KWFooling`, and not claimed.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Aligned covers -/

/-- An aligned cover of the game on `X × Y`: every pair lies in some listed rectangle, and each rectangle is
aligned at its designated coordinate. -/
def IsAlignedCover {n : ℕ} (X Y : Finset (Fin n → Bool))
    (l : List (Finset (Fin n → Bool) × (Finset (Fin n → Bool) × Fin n))) : Prop :=
  (∀ x ∈ X, ∀ y ∈ Y, ∃ r ∈ l, x ∈ r.1 ∧ y ∈ r.2.1) ∧
  (∀ r ∈ l, ∀ x ∈ r.1, ∀ y ∈ r.2.1, x r.2.2 ≠ y r.2.2)

/-- **Protocol ⇒ cover (proved)**: a cost-`c` protocol yields an aligned cover of size `≤ 2^c`.  The cover number
is the universal rectangle measure: every lower bound on it is a communication lower bound. -/
theorem protocol_cover {n : ℕ} (p : KWProt n) :
    ∀ X Y : Finset (Fin n → Bool),
      (∀ x ∈ X, ∀ y ∈ Y, x (p.run x y) ≠ y (p.run x y)) →
      ∃ l, IsAlignedCover X Y l ∧ l.length ≤ 2 ^ p.cost := by
  induction p with
  | out i =>
    intro X Y hsolve
    refine ⟨[(X, (Y, i))], ⟨?_, ?_⟩, ?_⟩
    · intro x hx y hy
      exact ⟨(X, (Y, i)), List.mem_singleton.mpr rfl, hx, hy⟩
    · intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      exact fun x hx y hy => hsolve x hx y hy
    · show 1 ≤ 2 ^ 0
      rw [pow_zero]
  | askA q l r ihl ihr =>
    intro X Y hsolve
    obtain ⟨l₁, ⟨hcov₁, hal₁⟩, hlen₁⟩ := ihl (X.filter (fun x => q x = true)) Y (by
      intro x hx y hy
      have hxX := (Finset.mem_filter.mp hx).1
      have hxq := (Finset.mem_filter.mp hx).2
      have h := hsolve x hxX y hy
      rw [KWProt.run_askA, if_pos hxq] at h
      exact h)
    obtain ⟨l₂, ⟨hcov₂, hal₂⟩, hlen₂⟩ := ihr (X.filter (fun x => ¬(q x = true))) Y (by
      intro x hx y hy
      have hxX := (Finset.mem_filter.mp hx).1
      have hxq := (Finset.mem_filter.mp hx).2
      have h := hsolve x hxX y hy
      rw [KWProt.run_askA, if_neg hxq] at h
      exact h)
    refine ⟨l₁ ++ l₂, ⟨?_, ?_⟩, ?_⟩
    · intro x hx y hy
      by_cases hq : q x = true
      · obtain ⟨rr, hrr, hxr, hyr⟩ := hcov₁ x (Finset.mem_filter.mpr ⟨hx, hq⟩) y hy
        exact ⟨rr, List.mem_append_left _ hrr, hxr, hyr⟩
      · obtain ⟨rr, hrr, hxr, hyr⟩ := hcov₂ x (Finset.mem_filter.mpr ⟨hx, hq⟩) y hy
        exact ⟨rr, List.mem_append_right _ hrr, hxr, hyr⟩
    · intro rr hrr
      rcases List.mem_append.mp hrr with h | h
      · exact hal₁ rr h
      · exact hal₂ rr h
    · rw [List.length_append]
      have e1 : (2 : ℕ) ^ l.cost ≤ 2 ^ max l.cost r.cost :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
      have e2 : (2 : ℕ) ^ r.cost ≤ 2 ^ max l.cost r.cost :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
      have e3 : (2 : ℕ) ^ (max l.cost r.cost + 1) = 2 * 2 ^ max l.cost r.cost := by
        rw [pow_succ]
        ring
      show l₁.length + l₂.length ≤ 2 ^ (max l.cost r.cost + 1)
      omega
  | askB q l r ihl ihr =>
    intro X Y hsolve
    obtain ⟨l₁, ⟨hcov₁, hal₁⟩, hlen₁⟩ := ihl X (Y.filter (fun y => q y = true)) (by
      intro x hx y hy
      have hyY := (Finset.mem_filter.mp hy).1
      have hyq := (Finset.mem_filter.mp hy).2
      have h := hsolve x hx y hyY
      rw [KWProt.run_askB, if_pos hyq] at h
      exact h)
    obtain ⟨l₂, ⟨hcov₂, hal₂⟩, hlen₂⟩ := ihr X (Y.filter (fun y => ¬(q y = true))) (by
      intro x hx y hy
      have hyY := (Finset.mem_filter.mp hy).1
      have hyq := (Finset.mem_filter.mp hy).2
      have h := hsolve x hx y hyY
      rw [KWProt.run_askB, if_neg hyq] at h
      exact h)
    refine ⟨l₁ ++ l₂, ⟨?_, ?_⟩, ?_⟩
    · intro x hx y hy
      by_cases hq : q y = true
      · obtain ⟨rr, hrr, hxr, hyr⟩ := hcov₁ x hx y (Finset.mem_filter.mpr ⟨hy, hq⟩)
        exact ⟨rr, List.mem_append_left _ hrr, hxr, hyr⟩
      · obtain ⟨rr, hrr, hxr, hyr⟩ := hcov₂ x hx y (Finset.mem_filter.mpr ⟨hy, hq⟩)
        exact ⟨rr, List.mem_append_right _ hrr, hxr, hyr⟩
    · intro rr hrr
      rcases List.mem_append.mp hrr with h | h
      · exact hal₁ rr h
      · exact hal₂ rr h
    · rw [List.length_append]
      have e1 : (2 : ℕ) ^ l.cost ≤ 2 ^ max l.cost r.cost :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
      have e2 : (2 : ℕ) ^ r.cost ≤ 2 ^ max l.cost r.cost :=
        Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
      have e3 : (2 : ℕ) ^ (max l.cost r.cost + 1) = 2 * 2 ^ max l.cost r.cost := by
        rw [pow_succ]
        ring
      show l₁.length + l₂.length ≤ 2 ^ (max l.cost r.cost + 1)
      omega

/-! ### Fooling families -/

/-- A KW fooling family: no two of its pairs fit inside one aligned rectangle — at every coordinate, at least one
of the four cross-differences fails. -/
def KWFooling {n : ℕ} (T : Finset ((Fin n → Bool) × (Fin n → Bool))) : Prop :=
  ∀ e ∈ T, ∀ e' ∈ T, e ≠ e' → ∀ i : Fin n,
    ¬(e.1 i ≠ e.2 i ∧ e.1 i ≠ e'.2 i ∧ e'.1 i ≠ e.2 i ∧ e'.1 i ≠ e'.2 i)

/-- Pigeonhole helper: a family covered pointwise by a list of sets, each holding at most one member, is no larger
than the list. -/
theorem card_le_length_of_pointwise_cover {α : Type} [DecidableEq α]
    (T : Finset α) (l : List (Finset α))
    (hcov : ∀ e ∈ T, ∃ s ∈ l, e ∈ s)
    (hone : ∀ s ∈ l, (T.filter (fun e => e ∈ s)).card ≤ 1) :
    T.card ≤ l.length := by
  induction l generalizing T with
  | nil =>
    have hT : T = ∅ := Finset.eq_empty_of_forall_notMem (fun e he => by
      obtain ⟨s, hs, -⟩ := hcov e he
      exact absurd hs List.not_mem_nil)
    rw [hT, Finset.card_empty]
    exact Nat.zero_le _
  | cons s rest ih =>
    have hsplit : (T.filter (fun e => e ∈ s)).card
        + (T.filter (fun e => ¬(e ∈ s))).card = T.card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have h1 : (T.filter (fun e => e ∈ s)).card ≤ 1 := hone s List.mem_cons_self
    have h2 : (T.filter (fun e => ¬(e ∈ s))).card ≤ rest.length := by
      apply ih
      · intro e he
        have heT := (Finset.mem_filter.mp he).1
        have hens := (Finset.mem_filter.mp he).2
        obtain ⟨s', hs', hes'⟩ := hcov e heT
        rcases List.mem_cons.mp hs' with h | h
        · exact absurd (h ▸ hes') hens
        · exact ⟨s', h, hes'⟩
      · intro s' hs'
        refine le_trans (Finset.card_le_card ?_) (hone s' (List.mem_cons_of_mem s hs'))
        intro e he
        have h1' := Finset.mem_filter.mp he
        have h2' := Finset.mem_filter.mp h1'.1
        exact Finset.mem_filter.mpr ⟨h2'.1, h1'.2⟩
    show T.card ≤ rest.length + 1
    omega

/-- **The χ tool (proved)**: a fooling family lower-bounds every aligned cover. -/
theorem fooling_le_cover {n : ℕ} (X Y : Finset (Fin n → Bool))
    (T : Finset ((Fin n → Bool) × (Fin n → Bool)))
    (hT : ∀ e ∈ T, e.1 ∈ X ∧ e.2 ∈ Y) (hfool : KWFooling T)
    (l : List (Finset (Fin n → Bool) × (Finset (Fin n → Bool) × Fin n)))
    (hcov : IsAlignedCover X Y l) :
    T.card ≤ l.length := by
  have hlen : (l.map (fun rr => rr.1 ×ˢ rr.2.1)).length = l.length := List.length_map ..
  rw [← hlen]
  apply card_le_length_of_pointwise_cover
  · intro e he
    obtain ⟨rr, hrr, hxr, hyr⟩ := hcov.1 e.1 (hT e he).1 e.2 (hT e he).2
    exact ⟨rr.1 ×ˢ rr.2.1, List.mem_map_of_mem hrr,
      Finset.mem_product.mpr ⟨hxr, hyr⟩⟩
  · intro s hs
    obtain ⟨rr, hrr, rfl⟩ := List.mem_map.mp hs
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have haT := (Finset.mem_filter.mp ha).1
    have has := Finset.mem_product.mp (Finset.mem_filter.mp ha).2
    have hbT := (Finset.mem_filter.mp hb).1
    have hbs := Finset.mem_product.mp (Finset.mem_filter.mp hb).2
    by_contra hne
    exact hfool a haT b hbT hne rr.2.2
      ⟨hcov.2 rr hrr a.1 has.1 a.2 has.2,
        hcov.2 rr hrr a.1 has.1 b.2 hbs.2,
        hcov.2 rr hrr b.1 hbs.1 a.2 has.2,
        hcov.2 rr hrr b.1 hbs.1 b.2 hbs.2⟩

/-! ### The sat3 calibration -/

/-- **The sat3 fooling family (proved)**: the `m·v` selector pairs are mutually non-corectangular — their
singleton difference-sets force distinct alignment coordinates. -/
theorem sat3_fooling (N : ℕ) (hv : 1 ≤ sat3V N) :
    ∃ T : Finset ((Fin N → Bool) × (Fin N → Bool)),
      KWFooling T ∧
      (∀ e ∈ T, sat3Family N e.1 = true ∧ sat3Family N e.2 = false) ∧
      sat3M N * sat3V N ≤ T.card := by
  choose x₁ x₀ h1 h0 hforce using
    fun cj : Fin (sat3M N) × Fin (sat3V N) => sat3_selector_pair N hv cj.1 cj.2
  set F : Fin (sat3M N) × Fin (sat3V N) → (Fin N → Bool) × (Fin N → Bool) :=
    fun cj => (x₁ cj, x₀ cj) with hF
  -- each pair genuinely differs, and only at its own selector bit
  have hdiff : ∀ cj, x₁ cj ≠ x₀ cj := by
    intro cj hcc
    have := h1 cj
    rw [hcc, h0 cj] at this
    exact Bool.noConfusion this
  have hbit : ∀ cj (i : Fin N), x₁ cj i ≠ x₀ cj i →
      i = sat3Bit N cj.1 ⟨0, by omega⟩ cj.2.val (by have := cj.2.isLt; omega) :=
    fun cj i h => hforce cj i h
  -- the selector bits are distinct across (c, j)
  have hbits_inj : Function.Injective (fun cj : Fin (sat3M N) × Fin (sat3V N) =>
      sat3Bit N cj.1 ⟨0, by omega⟩ cj.2.val (by have := cj.2.isLt; omega)) := by
    intro a b h
    have hr1 : (sat3Bit N a.1 ⟨0, by omega⟩ a.2.val
        (by have := a.2.isLt; omega)).val % sat3D N = a.2.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + a.2.val = a.2.val
      omega
    have hr2 : (sat3Bit N b.1 ⟨0, by omega⟩ b.2.val
        (by have := b.2.isLt; omega)).val % sat3D N = b.2.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + b.2.val = b.2.val
      omega
    have hdiv : a.1.val = b.1.val := by
      rw [← sat3Bit_clause N a.1 ⟨0, by omega⟩ a.2.val (by have := a.2.isLt; omega),
        ← sat3Bit_clause N b.1 ⟨0, by omega⟩ b.2.val (by have := b.2.isLt; omega)]
      exact congrArg (fun bit : Fin N => bit.val / sat3D N) h
    have hrem : a.2.val = b.2.val := by
      rw [← hr1, ← hr2]
      exact congrArg (fun bit : Fin N => bit.val % sat3D N) h
    exact Prod.ext (Fin.ext hdiv) (Fin.ext hrem)
  -- F is injective: a pair's unique difference bit identifies it
  have hFinj : Function.Injective F := by
    intro a b h
    have h0' : (x₁ a, x₀ a) = (x₁ b, x₀ b) := h
    rw [Prod.mk.injEq] at h0'
    obtain ⟨hfst, hsnd⟩ := h0'
    -- the pair (x₁ a, x₀ a) differs somewhere; that bit is both a's and b's selector bit
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hdiff a)
    have hia := hbit a i hi
    have hib : i = sat3Bit N b.1 ⟨0, by omega⟩ b.2.val (by have := b.2.isLt; omega) := by
      apply hbit b i
      rw [← hfst, ← hsnd]
      exact hi
    exact hbits_inj (hia.symm.trans hib)
  refine ⟨Finset.univ.image F, ?_, ?_, ?_⟩
  · -- fooling: the diagonal conditions force equal selector bits
    intro e he e' he' hne i hcond
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp he'
    have hia := hbit a i hcond.1
    have hib := hbit b i hcond.2.2.2
    have hab : a = b := hbits_inj (hia.symm.trans hib)
    exact hne (by rw [hab])
  · intro e he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp he
    exact ⟨h1 a, h0 a⟩
  · rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin]

/-- **The cover lower bound for SAT (proved)**: every aligned cover of the SAT boundary game (on the fooling
family's sides) has size `≥ m·v ≈ N/3` — the universal measure, calibrated; consistent with `m·v ≤ 2^cost`. -/
theorem sat3_cover_lb (N : ℕ) (hv : 1 ≤ sat3V N) :
    ∃ X Y : Finset (Fin N → Bool),
      (∀ x ∈ X, sat3Family N x = true) ∧ (∀ y ∈ Y, sat3Family N y = false) ∧
      ∀ l, IsAlignedCover X Y l → sat3M N * sat3V N ≤ l.length := by
  obtain ⟨T, hfool, hval, hcard⟩ := sat3_fooling N hv
  refine ⟨T.image Prod.fst, T.image Prod.snd, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact (hval e he).1
  · intro y hy
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    exact (hval e he).2
  · intro l hcov
    refine le_trans hcard (fooling_le_cover _ _ T ?_ hfool l hcov)
    intro e he
    exact ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.protocol_cover
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.fooling_le_cover
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_fooling
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cover_lb
