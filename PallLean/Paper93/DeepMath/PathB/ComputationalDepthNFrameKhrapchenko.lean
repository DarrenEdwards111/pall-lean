import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATKWAttack
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATGlobalConsistency

/-!
# N-Frame: Khrapchenko's theorem — the cover method at its cap

The edge-counting refinement of the rectangle method, and its calibration at full power.

**The theorem (proved).**  For distance-1 edge sets `Ed ⊆ X × Y` (each pair differs in at most one coordinate),
`khrapchenko`: `|Ed|² ≤ 2^cost · |X|·|Y|`.  In an aligned rectangle every edge's endpoints determine each other
(both differ exactly at the alignment coordinate), so each piece holds at most `min(|A|,|B|)` edges; the induction
absorbs the squaring by `(a+b)² ≤ 2(a²+b²)` at every node — no Cauchy–Schwarz needed.

**Calibration at the cap (proved).**  `parity_khrapchenko`: with `X`/`Y` the odd/even inputs and all `2^{n−1}·n`
single-flip edges, **`n² ≤ 2^(kwCost (parityFn n))`** — communication `≥ 2·log₂ n`, the classical quadratic bound,
showing the machinery genuinely reaches its Khrapchenko cap.

## Honest scope — where sat3 stands, precisely

For `sat3Family` the same method cannot reach the quadratic cap: its **boundary degree product is thin**.  A
satisfiable encoding loses satisfiability only by killing a uniquely-live clause (X-side degree `≤ ~m`, since turning
selectors *on* only helps — the monotone direction), and an unsatisfiable one revives only through its empty clause
(Y-side degree `≤ ~3v`); so Khrapchenko's value for sat3 caps at `≈ deg_X·deg_Y ≈ 3mv ≈ N`, i.e. `cost ≳ log₂ N` —
which the selector forcing already achieves.  Conclusion, proved-and-calibrated: the product measure is exhausted
for this target; superlogarithmic needs a measure that sees **witness coherence** rather than boundary edges.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The Khrapchenko edge-counting theorem -/

/-- The recursion: distance-1 edge sets square-count against aligned-rectangle partitions. -/
theorem khrapchenko_rec {n : ℕ} (p : KWProt n) :
    ∀ (X Y : Finset (Fin n → Bool)),
      (∀ x ∈ X, ∀ y ∈ Y, x (p.run x y) ≠ y (p.run x y)) →
      ∀ Ed : Finset ((Fin n → Bool) × (Fin n → Bool)),
      (∀ e ∈ Ed, e.1 ∈ X ∧ e.2 ∈ Y) →
      (∀ e ∈ Ed, ∀ i j : Fin n, e.1 i ≠ e.2 i → e.1 j ≠ e.2 j → i = j) →
      Ed.card ^ 2 ≤ 2 ^ p.cost * (X.card * Y.card) := by
  induction p with
  | out i =>
    intro X Y hsolve Ed hEdXY hEd1
    -- off the alignment coordinate the endpoints agree
    have hoff : ∀ a ∈ Ed, ∀ b : Fin n, b ≠ i → a.1 b = a.2 b := by
      intro a ha b hb
      by_contra hne
      have hai : a.1 i ≠ a.2 i :=
        hsolve a.1 (hEdXY a ha).1 a.2 (hEdXY a ha).2
      exact hb (hEd1 a ha b i hne hai)
    -- at the alignment coordinate they are opposite
    have hat : ∀ a ∈ Ed, a.2 i = !(a.1 i) := by
      intro a ha
      have hai : a.1 i ≠ a.2 i :=
        hsolve a.1 (hEdXY a ha).1 a.2 (hEdXY a ha).2
      cases hcc : a.1 i <;> cases hdd : a.2 i <;>
        first
          | rfl
          | (exfalso; rw [hcc, hdd] at hai; exact hai rfl)
    -- first components are injective on Ed
    have hinj1 : Set.InjOn (fun e : (Fin n → Bool) × (Fin n → Bool) => e.1) Ed := by
      intro e he e' he' h
      have h' : e.1 = e'.1 := h
      apply Prod.ext h'
      funext b
      by_cases hb : b = i
      · subst hb
        rw [hat e he, hat e' he', h']
      · rw [← hoff e he b hb, ← hoff e' he' b hb, h']
    -- second components are injective on Ed
    have hinj2 : Set.InjOn (fun e : (Fin n → Bool) × (Fin n → Bool) => e.2) Ed := by
      intro e he e' he' h
      have h' : e.2 = e'.2 := h
      refine Prod.ext ?_ h'
      funext b
      by_cases hb : b = i
      · subst hb
        have h1 := hat e he
        have h1' := hat e' he'
        -- a.1 b = !(a.2 b)
        have h2 : e.1 b = !(e.2 b) := by
          rw [h1, Bool.not_not]
        have h2' : e'.1 b = !(e'.2 b) := by
          rw [h1', Bool.not_not]
        rw [h2, h2', h']
      · rw [hoff e he b hb, hoff e' he' b hb, h']
    have hc1 : Ed.card ≤ X.card := by
      have himg : Ed.image (fun e => e.1) ⊆ X := by
        intro a ha
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
        exact (hEdXY e he).1
      calc Ed.card = (Ed.image (fun e => e.1)).card :=
            (Finset.card_image_of_injOn hinj1).symm
        _ ≤ X.card := Finset.card_le_card himg
    have hc2 : Ed.card ≤ Y.card := by
      have himg : Ed.image (fun e => e.2) ⊆ Y := by
        intro a ha
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
        exact (hEdXY e he).2
      calc Ed.card = (Ed.image (fun e => e.2)).card :=
            (Finset.card_image_of_injOn hinj2).symm
        _ ≤ Y.card := Finset.card_le_card himg
    show Ed.card ^ 2 ≤ 2 ^ 0 * (X.card * Y.card)
    rw [pow_zero, one_mul, pow_two]
    exact Nat.mul_le_mul hc1 hc2
  | askA q l r ihl ihr =>
    intro X Y hsolve Ed hEdXY hEd1
    have h1 := ihl (X.filter (fun x => q x = true)) Y (by
        intro x hx y hy
        have hxX := (Finset.mem_filter.mp hx).1
        have hxq := (Finset.mem_filter.mp hx).2
        have h := hsolve x hxX y hy
        rw [KWProt.run_askA, if_pos hxq] at h
        exact h)
      (Ed.filter (fun e => q e.1 = true)) (by
        intro e he
        have heE := (Finset.mem_filter.mp he).1
        have heq := (Finset.mem_filter.mp he).2
        exact ⟨Finset.mem_filter.mpr ⟨(hEdXY e heE).1, heq⟩, (hEdXY e heE).2⟩)
      (fun e he => hEd1 e ((Finset.filter_subset _ _) he))
    have h2 := ihr (X.filter (fun x => ¬(q x = true))) Y (by
        intro x hx y hy
        have hxX := (Finset.mem_filter.mp hx).1
        have hxq := (Finset.mem_filter.mp hx).2
        have h := hsolve x hxX y hy
        rw [KWProt.run_askA, if_neg hxq] at h
        exact h)
      (Ed.filter (fun e => ¬(q e.1 = true))) (by
        intro e he
        have heE := (Finset.mem_filter.mp he).1
        have heq := (Finset.mem_filter.mp he).2
        exact ⟨Finset.mem_filter.mpr ⟨(hEdXY e heE).1, heq⟩, (hEdXY e heE).2⟩)
      (fun e he => hEd1 e ((Finset.filter_subset _ _) he))
    have hEsplit : (Ed.filter (fun e => q e.1 = true)).card
        + (Ed.filter (fun e => ¬(q e.1 = true))).card = Ed.card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hXsplit : (X.filter (fun x => q x = true)).card
        + (X.filter (fun x => ¬(q x = true))).card = X.card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hamgm : 2 * (Ed.filter (fun e => q e.1 = true)).card
        * (Ed.filter (fun e => ¬(q e.1 = true))).card
        ≤ (Ed.filter (fun e => q e.1 = true)).card ^ 2
          + (Ed.filter (fun e => ¬(q e.1 = true))).card ^ 2 :=
      two_mul_le_add_sq _ _
    have h1' : (Ed.filter (fun e => q e.1 = true)).card ^ 2
        ≤ 2 ^ max l.cost r.cost * ((X.filter (fun x => q x = true)).card * Y.card) :=
      le_trans h1 (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
    have h2' : (Ed.filter (fun e => ¬(q e.1 = true))).card ^ 2
        ≤ 2 ^ max l.cost r.cost * ((X.filter (fun x => ¬(q x = true))).card * Y.card) :=
      le_trans h2 (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)))
    show Ed.card ^ 2 ≤ 2 ^ (max l.cost r.cost + 1) * (X.card * Y.card)
    rw [← hEsplit, ← hXsplit]
    have hexp : ((Ed.filter (fun e => q e.1 = true)).card
        + (Ed.filter (fun e => ¬(q e.1 = true))).card) ^ 2
        = (Ed.filter (fun e => q e.1 = true)).card ^ 2
          + 2 * (Ed.filter (fun e => q e.1 = true)).card
            * (Ed.filter (fun e => ¬(q e.1 = true))).card
          + (Ed.filter (fun e => ¬(q e.1 = true))).card ^ 2 := by
      ring
    have hRHS : 2 ^ (max l.cost r.cost + 1)
        * (((X.filter (fun x => q x = true)).card
            + (X.filter (fun x => ¬(q x = true))).card) * Y.card)
        = 2 ^ max l.cost r.cost * ((X.filter (fun x => q x = true)).card * Y.card)
          + 2 ^ max l.cost r.cost * ((X.filter (fun x => q x = true)).card * Y.card)
          + (2 ^ max l.cost r.cost * ((X.filter (fun x => ¬(q x = true))).card * Y.card)
            + 2 ^ max l.cost r.cost
              * ((X.filter (fun x => ¬(q x = true))).card * Y.card)) := by
      rw [pow_succ]
      ring
    rw [hexp, hRHS]
    omega
  | askB q l r ihl ihr =>
    intro X Y hsolve Ed hEdXY hEd1
    have h1 := ihl X (Y.filter (fun y => q y = true)) (by
        intro x hx y hy
        have hyY := (Finset.mem_filter.mp hy).1
        have hyq := (Finset.mem_filter.mp hy).2
        have h := hsolve x hx y hyY
        rw [KWProt.run_askB, if_pos hyq] at h
        exact h)
      (Ed.filter (fun e => q e.2 = true)) (by
        intro e he
        have heE := (Finset.mem_filter.mp he).1
        have heq := (Finset.mem_filter.mp he).2
        exact ⟨(hEdXY e heE).1, Finset.mem_filter.mpr ⟨(hEdXY e heE).2, heq⟩⟩)
      (fun e he => hEd1 e ((Finset.filter_subset _ _) he))
    have h2 := ihr X (Y.filter (fun y => ¬(q y = true))) (by
        intro x hx y hy
        have hyY := (Finset.mem_filter.mp hy).1
        have hyq := (Finset.mem_filter.mp hy).2
        have h := hsolve x hx y hyY
        rw [KWProt.run_askB, if_neg hyq] at h
        exact h)
      (Ed.filter (fun e => ¬(q e.2 = true))) (by
        intro e he
        have heE := (Finset.mem_filter.mp he).1
        have heq := (Finset.mem_filter.mp he).2
        exact ⟨(hEdXY e heE).1, Finset.mem_filter.mpr ⟨(hEdXY e heE).2, heq⟩⟩)
      (fun e he => hEd1 e ((Finset.filter_subset _ _) he))
    have hEsplit : (Ed.filter (fun e => q e.2 = true)).card
        + (Ed.filter (fun e => ¬(q e.2 = true))).card = Ed.card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hYsplit : (Y.filter (fun y => q y = true)).card
        + (Y.filter (fun y => ¬(q y = true))).card = Y.card :=
      Finset.filter_card_add_filter_neg_card_eq_card _
    have hamgm : 2 * (Ed.filter (fun e => q e.2 = true)).card
        * (Ed.filter (fun e => ¬(q e.2 = true))).card
        ≤ (Ed.filter (fun e => q e.2 = true)).card ^ 2
          + (Ed.filter (fun e => ¬(q e.2 = true))).card ^ 2 :=
      two_mul_le_add_sq _ _
    have h1' : (Ed.filter (fun e => q e.2 = true)).card ^ 2
        ≤ 2 ^ max l.cost r.cost * (X.card * (Y.filter (fun y => q y = true)).card) :=
      le_trans h1 (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)))
    have h2' : (Ed.filter (fun e => ¬(q e.2 = true))).card ^ 2
        ≤ 2 ^ max l.cost r.cost * (X.card * (Y.filter (fun y => ¬(q y = true))).card) :=
      le_trans h2 (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)))
    show Ed.card ^ 2 ≤ 2 ^ (max l.cost r.cost + 1) * (X.card * Y.card)
    rw [← hEsplit, ← hYsplit]
    have hexp : ((Ed.filter (fun e => q e.2 = true)).card
        + (Ed.filter (fun e => ¬(q e.2 = true))).card) ^ 2
        = (Ed.filter (fun e => q e.2 = true)).card ^ 2
          + 2 * (Ed.filter (fun e => q e.2 = true)).card
            * (Ed.filter (fun e => ¬(q e.2 = true))).card
          + (Ed.filter (fun e => ¬(q e.2 = true))).card ^ 2 := by
      ring
    have hRHS : 2 ^ (max l.cost r.cost + 1)
        * (X.card * ((Y.filter (fun y => q y = true)).card
            + (Y.filter (fun y => ¬(q y = true))).card))
        = 2 ^ max l.cost r.cost * (X.card * (Y.filter (fun y => q y = true)).card)
          + 2 ^ max l.cost r.cost * (X.card * (Y.filter (fun y => q y = true)).card)
          + (2 ^ max l.cost r.cost
              * (X.card * (Y.filter (fun y => ¬(q y = true))).card)
            + 2 ^ max l.cost r.cost
              * (X.card * (Y.filter (fun y => ¬(q y = true))).card)) := by
      rw [pow_succ]
      ring
    rw [hexp, hRHS]
    omega

/-- **Khrapchenko's theorem (proved)**: for any distance-1 edge family between a 1-side and a 0-side of `f`,
`|Ed|² ≤ 2^cost · |X|·|Y|`. -/
theorem khrapchenko {n : ℕ} (f : (Fin n → Bool) → Bool) (p : KWProt n)
    (hs : Solves p f) (X Y : Finset (Fin n → Bool))
    (hX : ∀ x ∈ X, f x = true) (hY : ∀ y ∈ Y, f y = false)
    (Ed : Finset ((Fin n → Bool) × (Fin n → Bool)))
    (hEdXY : ∀ e ∈ Ed, e.1 ∈ X ∧ e.2 ∈ Y)
    (hEd1 : ∀ e ∈ Ed, ∀ i j : Fin n, e.1 i ≠ e.2 i → e.1 j ≠ e.2 j → i = j) :
    Ed.card ^ 2 ≤ 2 ^ p.cost * (X.card * Y.card) :=
  khrapchenko_rec p X Y (fun x hx y hy => hs x y (hX x hx) (hY y hy)) Ed hEdXY hEd1

/-! ### Parity flips -/

theorem foldr_xor_notmem {n : ℕ} (l : List (Fin n)) (i : Fin n) (hmem : i ∉ l) :
    l.foldr (fun j acc => xor (if j = i then true else false) acc) false = false := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hne : hd ≠ i := by
      intro h
      subst h
      exact hmem List.mem_cons_self
    have htl : i ∉ tl := fun h => hmem (List.mem_cons_of_mem hd h)
    show xor (if hd = i then true else false) _ = false
    rw [if_neg hne, Bool.false_xor]
    exact ih htl

theorem foldr_xor_indicator {n : ℕ} (l : List (Fin n)) (i : Fin n)
    (hnd : l.Nodup) (hmem : i ∈ l) :
    l.foldr (fun j acc => xor (if j = i then true else false) acc) false = true := by
  induction l with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨hhd, htl⟩ := List.nodup_cons.mp hnd
    show xor (if hd = i then true else false) _ = true
    by_cases hh : hd = i
    · rw [if_pos hh]
      subst hh
      rw [foldr_xor_notmem tl hd hhd]
      rfl
    · rw [if_neg hh, Bool.false_xor]
      exact ih htl (by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hh
        · exact h)

/-- Flipping one bit toggles parity. -/
theorem parity_flip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    parityFn n (Function.update x i (!(x i))) = !(parityFn n x) := by
  have hpoint : ∀ j, Function.update x i (!(x i)) j
      = xor (x j) (if j = i then true else false) := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, if_pos rfl]
      cases x j <;> rfl
    · rw [Function.update_of_ne hj, if_neg hj]
      cases x j <;> rfl
  have h1 := foldr_xor_pointwise (List.finRange n) (Function.update x i (!(x i))) x
    (fun j => if j = i then true else false) hpoint
  have h2 := foldr_xor_indicator (List.finRange n) i (List.nodup_finRange n)
    (List.mem_finRange i)
  show (List.finRange n).foldr
      (fun j acc => xor (Function.update x i (!(x i)) j) acc) false = !(parityFn n x)
  rw [h1, h2]
  cases hpx : parityFn n x
  · rw [show (List.finRange n).foldr (fun j acc => xor (x j) acc) false
        = parityFn n x from rfl, hpx]
    rfl
  · rw [show (List.finRange n).foldr (fun j acc => xor (x j) acc) false
        = parityFn n x from rfl, hpx]
    rfl

/-! ### Parity at the quadratic cap -/

/-- **Khrapchenko for parity (proved)**: `n² ≤ 2^cost` — the classical quadratic bound; the method genuinely
reaches its cap. -/
theorem parity_khrapchenko (n : ℕ) (hn : 0 < n) (p : KWProt n)
    (hs : Solves p (parityFn n)) : n ^ 2 ≤ 2 ^ p.cost := by
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set X : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun x => parityFn n x = true) with hX
  set Y : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun x => parityFn n x = false) with hY
  -- the flip involution matches the two sides
  set φ : (Fin n → Bool) → (Fin n → Bool) :=
    fun x => Function.update x i0 (!(x i0)) with hφ
  have hφφ : ∀ x, φ (φ x) = x := by
    intro x
    show Function.update (Function.update x i0 (!(x i0))) i0
        (!(Function.update x i0 (!(x i0)) i0)) = x
    rw [Function.update_self, Bool.not_not, Function.update_idem,
      Function.update_eq_self]
  have hφinj : Function.Injective φ := by
    intro a b h
    have := congrArg φ h
    rw [hφφ, hφφ] at this
    exact this
  have hXY : X.card = Y.card := by
    have h1 : X.image φ ⊆ Y := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hpx := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show parityFn n (Function.update x i0 (!(x i0))) = false
      rw [parity_flip, hpx]
      rfl
    have h2 : Y.image φ ⊆ X := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      have hpy := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show parityFn n (Function.update y i0 (!(y i0))) = true
      rw [parity_flip, hpy]
      rfl
    have hc1 : X.card ≤ Y.card := by
      rw [← Finset.card_image_of_injective X hφinj]
      exact Finset.card_le_card h1
    have hc2 : Y.card ≤ X.card := by
      rw [← Finset.card_image_of_injective Y hφinj]
      exact Finset.card_le_card h2
    omega
  -- X is nonempty: the single-true indicator has odd parity
  have hXpos : 0 < X.card := by
    have hmem : (fun j : Fin n => if j = i0 then true else false) ∈ X := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      exact foldr_xor_indicator (List.finRange n) i0 (List.nodup_finRange n)
        (List.mem_finRange i0)
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  -- the edge family: all single-bit flips from the odd side
  set Ed : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
    (X ×ˢ Finset.univ).image (fun pr : (Fin n → Bool) × Fin n =>
      (pr.1, Function.update pr.1 pr.2 (!(pr.1 pr.2)))) with hEd
  have hEdinj : Function.Injective (fun pr : (Fin n → Bool) × Fin n =>
      (pr.1, Function.update pr.1 pr.2 (!(pr.1 pr.2)))) := by
    intro a b h
    have h0 : (a.1, Function.update a.1 a.2 (!(a.1 a.2)))
        = (b.1, Function.update b.1 b.2 (!(b.1 b.2))) := h
    rw [Prod.mk.injEq] at h0
    obtain ⟨h1, h2⟩ := h0
    refine Prod.ext h1 ?_
    by_contra hne
    have h3 := congrFun h2 a.2
    rw [Function.update_self, ← h1, Function.update_of_ne hne] at h3
    revert h3
    cases a.1 a.2 <;> decide
  have hEdcard : Ed.card = X.card * n := by
    rw [hEd, Finset.card_image_of_injective _ hEdinj, Finset.card_product,
      Finset.card_univ, Fintype.card_fin]
  have hEdXY : ∀ e ∈ Ed, e.1 ∈ X ∧ e.2 ∈ Y := by
    intro e he
    obtain ⟨pr, hpr, rfl⟩ := Finset.mem_image.mp he
    have hx := (Finset.mem_product.mp hpr).1
    have hpx := (Finset.mem_filter.mp hx).2
    refine ⟨hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    show parityFn n (Function.update pr.1 pr.2 (!(pr.1 pr.2))) = false
    rw [parity_flip, hpx]
    rfl
  have hEd1 : ∀ e ∈ Ed, ∀ i j : Fin n, e.1 i ≠ e.2 i → e.1 j ≠ e.2 j → i = j := by
    intro e he i j hi hj
    obtain ⟨pr, -, rfl⟩ := Finset.mem_image.mp he
    have hii : i = pr.2 := by
      by_contra hcon
      exact hi (Function.update_of_ne hcon _ _).symm
    have hjj : j = pr.2 := by
      by_contra hcon
      exact hj (Function.update_of_ne hcon _ _).symm
    rw [hii, hjj]
  have hmain := khrapchenko (parityFn n) p hs X Y
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun y hy => (Finset.mem_filter.mp hy).2) Ed hEdXY hEd1
  rw [hEdcard, ← hXY] at hmain
  -- (Xc·n)² ≤ 2^c·Xc² ⇒ n² ≤ 2^c
  have hexp : (X.card * n) ^ 2 = X.card ^ 2 * n ^ 2 := by
    ring
  have hexp2 : 2 ^ p.cost * (X.card * X.card) = X.card ^ 2 * 2 ^ p.cost := by
    ring
  rw [hexp, hexp2] at hmain
  exact Nat.le_of_mul_le_mul_left hmain (by positivity)

/-- **The classical bound at the minimum (proved)**: `n² ≤ 2^(kwCost (parityFn n))` — parity's game communication
is at least `2·log₂ n`, the Khrapchenko cap. -/
theorem parity_kwCost_quadratic (n : ℕ) (hn : 0 < n) :
    n ^ 2 ≤ 2 ^ kwCost (parityFn n) := by
  have hne : {c | ∃ p : KWProt n, Solves p (parityFn n) ∧ p.cost = c}.Nonempty := by
    refine ⟨(kwProtOf hn (dnfFor (parityFn n))).cost,
      kwProtOf hn (dnfFor (parityFn n)), ?_, rfl⟩
    have := kwProtOf_solves hn (dnfFor (parityFn n))
    rw [eval_dnfFor] at this
    exact this
  obtain ⟨p, hp, hcost⟩ := Nat.sInf_mem hne
  have := parity_khrapchenko n hn p hp
  show n ^ 2 ≤ 2 ^ sInf {c | ∃ p : KWProt n, Solves p (parityFn n) ∧ p.cost = c}
  rw [← hcost]
  exact this

/-- **Parity depth (proved)**: `n² ≤ 4^(depthBudget (parityFn n))` — depth `≥ log₂ n`, matching the balanced xor
tree up to constants: the method is tight at its cap. -/
theorem parity_depthBudget_quadratic (n : ℕ) (hn : 0 < n) :
    n ^ 2 ≤ 4 ^ depthBudget (parityFn n) := by
  have h1 := parity_kwCost_quadratic n hn
  have h2 := kwCost_le_two_depthBudget hn (parityFn n)
  have h3 : (2 : ℕ) ^ kwCost (parityFn n) ≤ 2 ^ (2 * depthBudget (parityFn n)) :=
    Nat.pow_le_pow_right (by omega) h2
  have h4 : (2 : ℕ) ^ (2 * depthBudget (parityFn n)) = 4 ^ depthBudget (parityFn n) := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.khrapchenko
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.parity_flip
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.parity_khrapchenko
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.parity_kwCost_quadratic
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.parity_depthBudget_quadratic
