import Mathlib

/-!
# The structural growing‑algebraic‑immunity lower bound: `AI(Maj_n) ≥ ⌈n/2⌉`

`decide` caps algebraic immunity at a constant (the degree‑`<d` annihilator search is `2^{∑_{i<d}C(n,i)}`).
A predicate with **growing** algebraic immunity needs a *structural* argument that scales with arity.  The
canonical such family is **Majority**, with the optimal `AI(Maj_n) = ⌈n/2⌉` (Dalai–Maitra–Sarkar).

This file builds the structural lower bound from its genuine core: the **`F₂` Möbius / ANF inversion**.  Writing a
Boolean function as `g : Finset (Fin n) → ZMod 2` (value at the point with support `T`), the *subset‑sum
transform* `anf g S = ∑_{T ⊆ S} g T` recovers the algebraic‑normal‑form coefficients, and — the key fact — it is
**its own inverse over `F₂`**, because the number of sets between `U` and `S` is `2^{|S|-|U|}`, even unless
`U = S`.  From involutivity the immunity bound falls out directly.

## Proved (clean axioms, no `sorry`)

* `card_filter_subset_between` — `#{T : U ⊆ T ⊆ S} = 2^{|S|-|U|}` (the interval count, by the bijection
  `T ↦ T \ U`).
* `anf_involutive` — `anf (anf g) = g` over `ZMod 2`: the subset‑sum transform is an involution.  The `F₂`
  Möbius inversion, proved from the interval count (`2^{|S|-|U|}` even unless `U = S`).
* `low_weight_low_degree_zero` — **the structural core**: if `g` vanishes on every support of size `< t`
  (vanishes on low weight) and has ANF degree `< t` (`anf g` vanishes on sizes `≥ t`), then `g ≡ 0`.
  Equivalently: a low‑ANF‑degree function supported only on high weight is zero.
* `nonzero_low_degree_hits_low_weight` — the contrapositive: every nonzero degree‑`< t` function is nonzero at
  some weight‑`< t` point (the low‑weight slice is interpolating for degree‑`< t` `F₂` polynomials).
* `negMaj_no_low_degree_annihilator` — the `¬Maj` (low‑weight) side: no nonzero `g` of ANF degree `< t`
  annihilates `¬Maj` (`g · ¬Maj = 0`).
* `anf_compl_eq_superset_sum` / `degreeLt_compl` — **the complement‑symmetry rung**: complementing the argument
  sends the downset ANF transform to the upset sum of ANF coefficients (`anf (T↦g Tᶜ) U = ∑_{S⊇U} anf g S`),
  proved by a complement reindex + a dual swap‑and‑count; hence complement **preserves ANF degree**.  This is the
  ANF form of the symmetry `Maj(x̄) = ¬Maj(x)`.
* `maj_high_weight_annihilator_zero` — the `Maj` (high‑weight) side, via the complement conjugation.
* `majority_algebraic_immunity_two_sided` — **`AI(Maj_{2t-1}) ≥ t`, both sides (proved)**: for `2t ≤ n+1`, no
  nonzero ANF degree‑`< t` function annihilates `Maj` *or* `¬Maj`.  The immunity threshold `t` grows with the
  arity, by a purely structural `F₂`‑inversion + complement‑symmetry argument — no `decide`.

## Status

The full two‑sided structural growing‑algebraic‑immunity lower bound `AI(Maj_{2t-1}) ≥ t` is proved here from
scratch: the `F₂` Möbius inversion (absent from Mathlib), the low‑weight interpolation core, and the
degree‑preserving complement symmetry that closes the high‑weight side.  No `decide`, scaling with arity, clean
axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`.  (The matching *upper* bound `AI ≤ ⌈n/2⌉`, giving
optimality, is a separate dimension‑counting statement not needed for the lower bound.)
-/

namespace PallLean.Paper93.DeepMath.PathB.MajorityAI

open Finset

variable {n : ℕ}

/-- The **subset‑sum (ANF / Möbius) transform** of `g : Finset (Fin n) → ZMod 2`:
`anf g S = ∑_{T ⊆ S} g T`.  Over `F₂` this both computes the algebraic‑normal‑form coefficient at `S` and is
its own inverse (`anf_involutive`). -/
def anf (g : Finset (Fin n) → ZMod 2) (S : Finset (Fin n)) : ZMod 2 :=
  ∑ T ∈ S.powerset, g T

/-- **Interval count.**  For `U ⊆ S`, the number of `T` with `U ⊆ T ⊆ S` is `2^{|S|-|U|}` — via the bijection
`T ↦ T \ U` onto the powerset of `S \ U`. -/
theorem card_filter_subset_between {U S : Finset (Fin n)} (h : U ⊆ S) :
    (S.powerset.filter (fun T => U ⊆ T)).card = 2 ^ (S.card - U.card) := by
  classical
  have hbij : (S.powerset.filter (fun T => U ⊆ T)).card = (S \ U).powerset.card := by
    apply Finset.card_nbij' (fun T => T \ U) (fun V => V ∪ U)
    · intro T hT
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      intro a ha
      rw [Finset.mem_sdiff] at ha ⊢
      exact ⟨hT.1 ha.1, ha.2⟩
    · intro V hV
      simp only [Finset.mem_coe, Finset.mem_powerset, Finset.mem_filter] at hV ⊢
      exact ⟨Finset.union_subset (hV.trans Finset.sdiff_subset) h, Finset.subset_union_right⟩
    · intro T hT
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hT
      show (T \ U) ∪ U = T
      exact Finset.sdiff_union_of_subset hT.2
    · intro V hV
      simp only [Finset.mem_coe, Finset.mem_powerset] at hV
      have hdisj : Disjoint V U := Finset.disjoint_left.mpr fun a haV haU =>
        (Finset.mem_sdiff.mp (hV haV)).2 haU
      show (V ∪ U) \ U = V
      rw [Finset.union_sdiff_right, Finset.sdiff_eq_self_iff_disjoint.mpr hdisj]
  rw [hbij, Finset.card_powerset, Finset.card_sdiff_of_subset h]

/-- **The `F₂` Möbius inversion.**  The subset‑sum transform is an involution: `anf (anf g) = g`.  This is the
heart of the immunity bound — it lets low‑weight vanishing and low degree combine into a vanishing theorem. -/
theorem anf_involutive (g : Finset (Fin n) → ZMod 2) (S : Finset (Fin n)) :
    anf (anf g) S = g S := by
  classical
  -- rewrite the double powerset sum as an indicator sum over `S.powerset × S.powerset`
  have e1 : anf (anf g) S
      = ∑ T ∈ S.powerset, ∑ U ∈ S.powerset, (if U ⊆ T then g U else 0) := by
    show (∑ T ∈ S.powerset, ∑ U ∈ T.powerset, g U) = _
    apply Finset.sum_congr rfl
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext U
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun hUT => ⟨hUT.trans hT, hUT⟩, fun h => h.2⟩
  rw [e1, Finset.sum_comm]
  -- collapse the inner sum to a scalar multiple via the interval count
  have e2 : ∀ U ∈ S.powerset,
      (∑ T ∈ S.powerset, (if U ⊆ T then g U else 0))
        = (2 ^ (S.card - U.card) : ℕ) • g U := by
    intro U hU
    rw [Finset.mem_powerset] at hU
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_subset_between hU]
  rw [Finset.sum_congr rfl e2]
  -- only the U = S term survives mod 2
  have hsingle : (∑ U ∈ S.powerset, (2 ^ (S.card - U.card) : ℕ) • g U)
      = (2 ^ (S.card - S.card) : ℕ) • g S := by
    apply Finset.sum_eq_single
    · intro U hU hUS
      rw [Finset.mem_powerset] at hU
      have hlt : U.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hU, hUS⟩)
      have hpos : 0 < S.card - U.card := Nat.sub_pos_of_lt hlt
      have hz : ((2 ^ (S.card - U.card) : ℕ) : ZMod 2) = 0 := by
        have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
        rw [Nat.cast_pow, h2, zero_pow (Nat.pos_iff_ne_zero.mp hpos)]
      rw [nsmul_eq_mul, hz, zero_mul]
    · intro h
      exact absurd (Finset.mem_powerset.mpr (le_refl S)) h
  rw [hsingle, Nat.sub_self, pow_zero, one_smul]

/-- **The structural core (proved).**  If `g` vanishes on every support of size `< t` (vanishes on low weight)
and has ANF degree `< t` (`anf g` vanishes on every size `≥ t`), then `g ≡ 0`.  This is the `F₂`‑inversion
heart of the growing‑immunity bound: a function with low ANF degree that is supported only on high weight must
be identically zero. -/
theorem low_weight_low_degree_zero {t : ℕ} (g : Finset (Fin n) → ZMod 2)
    (hlow : ∀ T : Finset (Fin n), T.card < t → g T = 0)
    (hdeg : ∀ S : Finset (Fin n), t ≤ S.card → anf g S = 0) :
    ∀ S : Finset (Fin n), g S = 0 := by
  intro S
  have hexp : g S = ∑ T ∈ S.powerset, anf g T := (anf_involutive g S).symm
  rw [hexp]
  apply Finset.sum_eq_zero
  intro T hT
  rcases lt_or_ge T.card t with h | h
  · -- ANF coefficient at a small set is a sum of `g` over even smaller sets, all zero
    show (∑ U ∈ T.powerset, g U) = 0
    apply Finset.sum_eq_zero
    intro U hU
    exact hlow U (lt_of_le_of_lt (Finset.card_le_card (Finset.mem_powerset.mp hU)) h)
  · exact hdeg T h

/-- ANF degree `< t`: all ANF coefficients on sets of size `≥ t` vanish. -/
def DegreeLt (g : Finset (Fin n) → ZMod 2) (t : ℕ) : Prop :=
  ∀ S : Finset (Fin n), t ≤ S.card → anf g S = 0

/-- The **complementary majority** `¬Maj` on `n = 2t-1` variables, indexed by support: `¬Maj T = 1` iff the
weight `|T| < t`. -/
def negMaj (t : ℕ) (T : Finset (Fin n)) : ZMod 2 := if T.card < t then 1 else 0

/-- **Low‑weight interpolation (proved).**  The points of weight `< t` form an interpolating set for ANF
degree‑`< t` functions over `F₂`: the only such function vanishing on all of them is `0`.  Hence any nonzero
degree‑`< t` function is nonzero at some low‑weight point — it cannot vanish on the whole low‑weight slice. -/
theorem nonzero_low_degree_hits_low_weight {t : ℕ} (g : Finset (Fin n) → ZMod 2)
    (hg : g ≠ 0) (hdeg : DegreeLt g t) :
    ∃ T : Finset (Fin n), T.card < t ∧ g T ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hg (funext fun S => low_weight_low_degree_zero g (fun T hT => hc T hT) hdeg S)

/-- **`AI(Maj_{2t-1}) ≥ t`, the `¬Maj` (low‑weight) side (proved, structural, arity‑scaling).**  No nonzero ANF
degree‑`< t` function `g` annihilates `¬Maj` (`g · ¬Maj = 0`): such a `g` vanishes on every weight‑`< t` point,
so `g = 0` by the `F₂`‑Möbius interpolation `low_weight_low_degree_zero`.  The immunity threshold `t` grows with
the arity — the growing‑algebraic‑immunity lower bound, with no `decide`. -/
theorem negMaj_no_low_degree_annihilator {t : ℕ} (g : Finset (Fin n) → ZMod 2)
    (hg : g ≠ 0) (hdeg : DegreeLt g t)
    (hann : ∀ T : Finset (Fin n), g T * negMaj t T = 0) : False := by
  apply hg
  funext S
  refine low_weight_low_degree_zero g (fun T hT => ?_) hdeg S
  have h := hann T
  rw [negMaj, if_pos hT, mul_one] at h
  exact h

/-! ### The complement‑symmetry rung: closing the `Maj` (high‑weight) side -/

/-- **Degree identity under complement (proved).**  Complementing the argument turns the downset ANF transform
into the upset sum of the ANF coefficients:
`anf (T ↦ g Tᶜ) U = ∑_{S ⊇ U} anf g S`.  Proved by a complement reindex on the left and a swap‑and‑count on the
right (reusing `card_filter_subset_between` at `S = univ`); both sides equal `∑_{R ⊇ Uᶜ} g R`. -/
theorem anf_compl_eq_superset_sum (g : Finset (Fin n) → ZMod 2) (U : Finset (Fin n)) :
    anf (fun T => g Tᶜ) U
      = ∑ S ∈ (univ : Finset (Fin n)).powerset.filter (fun S => U ⊆ S), anf g S := by
  classical
  -- left side reindexes (T ↦ Tᶜ) to a sum over supersets of `Uᶜ`
  have hA : anf (fun T => g Tᶜ) U
      = ∑ R ∈ (univ : Finset (Fin n)).powerset.filter (fun R => Uᶜ ⊆ R), g R := by
    show (∑ T ∈ U.powerset, g Tᶜ) = _
    apply Finset.sum_nbij' (fun T => Tᶜ) (fun R => Rᶜ)
    · intro T hT
      rw [Finset.mem_powerset] at hT
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, Finset.compl_subset_compl.mpr hT⟩
    · intro R hR
      rw [Finset.mem_filter, Finset.mem_powerset] at hR
      rw [Finset.mem_powerset]
      have h := Finset.compl_subset_compl.mpr hR.2
      rwa [compl_compl] at h
    · intro T _; rw [compl_compl]
    · intro R _; rw [compl_compl]
    · intro T _; rfl
  -- right side swaps and counts, also landing on supersets of `Uᶜ`
  have hB : (∑ S ∈ (univ : Finset (Fin n)).powerset.filter (fun S => U ⊆ S), anf g S)
      = ∑ R ∈ (univ : Finset (Fin n)).powerset.filter (fun R => Uᶜ ⊆ R), g R := by
    calc ∑ S ∈ (univ : Finset (Fin n)).powerset.filter (fun S => U ⊆ S), anf g S
        = ∑ S ∈ (univ : Finset (Fin n)).powerset.filter (fun S => U ⊆ S),
            ∑ R ∈ (univ : Finset (Fin n)).powerset, (if R ⊆ S then g R else 0) := by
          apply Finset.sum_congr rfl
          intro S _
          show (∑ R ∈ S.powerset, g R) = _
          rw [← Finset.sum_filter]
          apply Finset.sum_congr _ (fun _ _ => rfl)
          ext R
          simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_univ, true_and]
      _ = ∑ R ∈ (univ : Finset (Fin n)).powerset,
            ∑ S ∈ (univ : Finset (Fin n)).powerset.filter (fun S => U ⊆ S),
              (if R ⊆ S then g R else 0) := Finset.sum_comm
      _ = ∑ R ∈ (univ : Finset (Fin n)).powerset,
            (2 ^ (Fintype.card (Fin n) - (U ∪ R).card) : ℕ) • g R := by
          apply Finset.sum_congr rfl
          intro R _
          rw [← Finset.sum_filter, Finset.filter_filter, Finset.sum_const]
          congr 1
          have hfeq : (univ : Finset (Fin n)).powerset.filter (fun S => U ⊆ S ∧ R ⊆ S)
              = (univ : Finset (Fin n)).powerset.filter (fun S => U ∪ R ⊆ S) := by
            apply Finset.filter_congr
            intro S _
            exact Finset.union_subset_iff.symm
          rw [hfeq, card_filter_subset_between (Finset.subset_univ (U ∪ R)), Finset.card_univ]
      _ = ∑ R ∈ (univ : Finset (Fin n)).powerset.filter (fun R => Uᶜ ⊆ R), g R := by
          rw [← Finset.sum_filter_add_sum_filter_not
                ((univ : Finset (Fin n)).powerset) (fun R => Uᶜ ⊆ R)]
          have hnot : (∑ R ∈ (univ : Finset (Fin n)).powerset.filter (fun R => ¬ Uᶜ ⊆ R),
              (2 ^ (Fintype.card (Fin n) - (U ∪ R).card) : ℕ) • g R) = 0 := by
            apply Finset.sum_eq_zero
            intro R hR
            rw [Finset.mem_filter] at hR
            have hne : U ∪ R ≠ univ := by
              intro h
              apply hR.2
              intro x hx
              rw [Finset.mem_compl] at hx
              have hmem : x ∈ U ∪ R := h ▸ Finset.mem_univ x
              rcases Finset.mem_union.mp hmem with h1 | h1
              · exact absurd h1 hx
              · exact h1
            have hss : U ∪ R ⊂ univ := Finset.ssubset_univ_iff.mpr hne
            have hcard_lt : (U ∪ R).card < Fintype.card (Fin n) := by
              rw [← Finset.card_univ]; exact Finset.card_lt_card hss
            have hpos : 0 < Fintype.card (Fin n) - (U ∪ R).card := Nat.sub_pos_of_lt hcard_lt
            have hz : ((2 ^ (Fintype.card (Fin n) - (U ∪ R).card) : ℕ) : ZMod 2) = 0 := by
              have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
              rw [Nat.cast_pow, h2, zero_pow (Nat.pos_iff_ne_zero.mp hpos)]
            rw [nsmul_eq_mul, hz, zero_mul]
          have hp : (∑ R ∈ (univ : Finset (Fin n)).powerset.filter (fun R => Uᶜ ⊆ R),
              (2 ^ (Fintype.card (Fin n) - (U ∪ R).card) : ℕ) • g R)
              = ∑ R ∈ (univ : Finset (Fin n)).powerset.filter (fun R => Uᶜ ⊆ R), g R := by
            apply Finset.sum_congr rfl
            intro R hR
            rw [Finset.mem_filter] at hR
            have huniv : U ∪ R = univ := by
              apply Finset.Subset.antisymm (Finset.subset_univ _)
              intro x _
              rw [Finset.mem_union]
              by_cases hxU : x ∈ U
              · exact Or.inl hxU
              · exact Or.inr (hR.2 (Finset.mem_compl.mpr hxU))
            rw [huniv, Finset.card_univ, Nat.sub_self, pow_zero, one_smul]
          rw [hnot, add_zero, hp]
  rw [hA, hB]

/-- **Complement preserves ANF degree (proved).**  If `g` has ANF degree `< t`, so does `T ↦ g Tᶜ`: each ANF
coefficient `anf (g ∘ ᶜ) U` for `|U| ≥ t` is a sum of `anf g S` over supersets `S ⊇ U`, all of size `≥ t`,
hence all zero.  This is the degree‑preserving complement symmetry `Maj(x̄) = ¬Maj(x)` at the ANF level. -/
theorem degreeLt_compl {t : ℕ} (g : Finset (Fin n) → ZMod 2) (hdeg : DegreeLt g t) :
    DegreeLt (fun T => g Tᶜ) t := by
  intro U hU
  rw [anf_compl_eq_superset_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact hdeg S (le_trans hU (Finset.card_le_card hS.2))

/-- **`AI(Maj_{2t-1}) ≥ t`, the `Maj` (high‑weight) side (proved).**  No nonzero ANF degree‑`< t` `g`
annihilates `Maj` (`g · Maj = 0`, i.e. `g` vanishes on weight `≥ t`).  Via the complement conjugation
`T ↦ g Tᶜ`: it vanishes on low weight (since `|Tᶜ| ≥ t` there, using `2t ≤ n+1`) and keeps degree `< t`
(`degreeLt_compl`), so it is `0` by `low_weight_low_degree_zero`, whence `g = 0`. -/
theorem maj_high_weight_annihilator_zero {t : ℕ} (hn : 2 * t ≤ n + 1)
    (g : Finset (Fin n) → ZMod 2) (hdeg : DegreeLt g t)
    (hhigh : ∀ T : Finset (Fin n), t ≤ T.card → g T = 0) :
    ∀ S : Finset (Fin n), g S = 0 := by
  have hg' : ∀ S : Finset (Fin n), (fun T => g Tᶜ) S = 0 := by
    apply low_weight_low_degree_zero (t := t) (fun T => g Tᶜ)
    · intro T hT
      show g Tᶜ = 0
      apply hhigh
      have hcard : Tᶜ.card = Fintype.card (Fin n) - T.card := Finset.card_compl T
      have hle : T.card ≤ Fintype.card (Fin n) := Finset.card_le_univ T
      rw [Fintype.card_fin] at hcard hle
      rw [hcard]
      omega
    · exact degreeLt_compl g hdeg
  intro S
  have h := hg' Sᶜ
  simp only [compl_compl] at h
  exact h

/-- Majority on `n` variables (indexed by support): `Maj t T = 1` iff weight `|T| ≥ t`.  For `n = 2t-1` this is
the usual majority function. -/
def Maj (t : ℕ) (T : Finset (Fin n)) : ZMod 2 := if t ≤ T.card then 1 else 0

/-- **`AI(Maj_{2t-1}) ≥ t`, both sides (proved).**  For `2t ≤ n+1` (i.e. `n ≥ 2t-1`), no nonzero ANF degree‑`< t`
function `g` annihilates `Maj` *or* `¬Maj`.  This is the full two‑sided algebraic‑immunity lower bound: the
immunity threshold `t` grows with the arity, by a purely structural `F₂`‑inversion + complement‑symmetry
argument — no `decide`. -/
theorem majority_algebraic_immunity_two_sided {t : ℕ} (hn : 2 * t ≤ n + 1)
    (g : Finset (Fin n) → ZMod 2) (hg : g ≠ 0) (hdeg : DegreeLt g t) :
    (∃ T : Finset (Fin n), g T * Maj t T ≠ 0) ∧ (∃ T : Finset (Fin n), g T * negMaj t T ≠ 0) := by
  constructor
  · by_contra hc
    push_neg at hc
    apply hg
    funext S
    refine maj_high_weight_annihilator_zero hn g hdeg (fun T hT => ?_) S
    have h := hc T
    rw [Maj, if_pos hT, mul_one] at h
    exact h
  · by_contra hc
    push_neg at hc
    exact negMaj_no_low_degree_annihilator g hg hdeg (fun T => hc T)

end PallLean.Paper93.DeepMath.PathB.MajorityAI

#print axioms PallLean.Paper93.DeepMath.PathB.MajorityAI.anf_involutive
#print axioms PallLean.Paper93.DeepMath.PathB.MajorityAI.low_weight_low_degree_zero

#print axioms PallLean.Paper93.DeepMath.PathB.MajorityAI.majority_algebraic_immunity_two_sided
