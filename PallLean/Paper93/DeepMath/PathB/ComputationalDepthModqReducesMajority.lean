import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4PadSubcircuits
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMajorityAC0pScope

/-!
# The `MOD_q ≤ Majority` reduction — COMPLETE ⇒ unconditional `Majority ∉ AC⁰[p]`

The full classical `MOD_q ≤_{AC⁰[p]} Majority` reduction circuit, formalized.  This **discharges**
`AC0pReduction (modqLang q) majorityLang p` (the previously‑assumed hypothesis of `…MajorityAC0pScope`),
turning `Majority ∉ AC⁰[p]` and the single‑predicate simultaneous‑resistance into **unconditional theorems**.

The construction: `thresholdCirc m k Maj := padInputs (selector m k) Maj` builds `[#ones ≥ k]` from a Majority
circuit on `2m+1` inputs (the `m` real inputs + `m+1-k` hardwired `true`s + `k` `false`s; Majority of that =
`[#ones(x)+(m+1-k) ≥ m+1] = [#ones(x) ≥ k]`); `modqCirc = ⋁_{k≤m, k≡0(q)}([#ones≥k] ∧ ¬[#ones≥k+1])` computes
`MOD_q`.

## Proved (clean axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`)

* **Threshold gadget:** `trueCount_padBits`, `thresholdCirc_eval` (`= [#ones ≥ k]`), `_isAC0p`, `_depth`.
* **`MOD_q` circuit:** `andTerm_eval_eq` (`= [#ones = k]`), `modqCirc_eval` (`= [#ones ≡ 0 (q)]`),
  `modqCirc_isAC0p`, `modqCirc_depth_le` (constant depth), `modqCirc_subcircuits_card_le` (polynomial size).
* **`IsPolyBounded` closure:** `ipb_const/linear/add/mul/comp_affine/succ/congr` (built from scratch).
* **`reductionFamily`** — the `AC⁰[p]` family computing `MOD_q` from a Majority family.
* **`modq_AC0pReduction`** — the reduction `MOD_q ≤_{AC⁰[p]} Majority`, **proved**.
* **`majority_not_in_AC0p`** — **unconditional `Majority ∉ AC⁰[p]`** (via `majority_not_AC0p_of_reduction`).
* **`majority_resists_AC0p`** / **`majority_simultaneous_resistance`** — `majorityF2` unconditionally resists the
  `AC⁰[p]` class, and (with the proved low‑degree resistance) witnesses `SimultaneousAlgAC0pResistance` —
  **the binding wall of the unified frontier, realized by one predicate, with no remaining hypothesis.**
-/

namespace PallLean.Paper93.DeepMath.PathB.ModqReducesMajority

open Finset
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.BoolCircuitSyntax
open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits subcircuitsList)

/-- The input selector: real inputs `0..m-1`, then `m+1-k` hardwired `true`s, then `k` hardwired `false`s. -/
def selector (m k : ℕ) : Fin (2 * m + 1) → BoolCircuitSyntax m :=
  fun i => if h : (i : ℕ) < m then .input ⟨i, h⟩
           else if (i : ℕ) < 2 * m + 1 - k then .const true else .const false

/-- The padded Boolean assignment that `selector` realizes. -/
def padBits (m k : ℕ) (x : Fin m → Bool) : Fin (2 * m + 1) → Bool :=
  fun i => if h : (i : ℕ) < m then x ⟨i, h⟩ else decide ((i : ℕ) < 2 * m + 1 - k)

theorem selector_eval (m k : ℕ) (x : Fin m → Bool) (i : Fin (2 * m + 1)) :
    (selector m k i).eval x = padBits m k x i := by
  unfold selector padBits
  by_cases h : (i : ℕ) < m
  · simp [h, BoolCircuitSyntax.eval]
  · by_cases h2 : (i : ℕ) < 2 * m + 1 - k <;> simp [h, h2, BoolCircuitSyntax.eval]

/-- **The padded count.**  `#ones(padBits x) = #ones(x) + (m+1-k)` for `k ≤ m+1`. -/
theorem trueCount_padBits (m k : ℕ) (hk : k ≤ m + 1) (x : Fin m → Bool) :
    (univ.filter (fun i : Fin (2 * m + 1) => padBits m k x i = true)).card
      = (univ.filter (fun j : Fin m => x j = true)).card + (m + 1 - k) := by
  classical
  set xb : ℕ → Bool := fun a => if h : a < m then x ⟨a, h⟩ else false with hxb
  set g : ℕ → ℕ := fun a => if a < m then (if xb a = true then 1 else 0)
                            else (if a < 2 * m + 1 - k then 1 else 0) with hg
  have hLHS : (univ.filter (fun i : Fin (2 * m + 1) => padBits m k x i = true)).card
      = ∑ i ∈ range (2 * m + 1), g i := by
    rw [Finset.card_filter]
    rw [show (∑ i : Fin (2 * m + 1), if padBits m k x i = true then 1 else 0)
          = ∑ i : Fin (2 * m + 1), g ↑i from ?_]
    · exact Fin.sum_univ_eq_sum_range g (2 * m + 1)
    · apply Finset.sum_congr rfl
      intro i _
      by_cases h : (↑i : ℕ) < m
      · simp only [padBits, hg, hxb, h, dif_pos, if_pos]
      · simp only [padBits, hg, hxb, h, dif_neg, if_neg, not_false_iff,
          decide_eq_true_eq]
  have hRHS1 : (univ.filter (fun j : Fin m => x j = true)).card = ∑ i ∈ range m, g i := by
    rw [Finset.card_filter, ← Fin.sum_univ_eq_sum_range g m]
    apply Finset.sum_congr rfl
    intro j _
    have hjm : (↑j : ℕ) < m := j.isLt
    simp only [hg, hxb, hjm, if_pos, dif_pos]
  rw [hLHS, hRHS1, show 2 * m + 1 = m + (m + 1) from by ring, Finset.sum_range_add]
  congr 1
  rw [show (∑ i ∈ range (m + 1), g (m + i)) = ∑ i ∈ range (m + 1), (if i < m + 1 - k then 1 else 0)
        from ?_]
  · rw [Finset.sum_boole]
    have hf : (range (m + 1)).filter (fun i => i < m + 1 - k) = range (m + 1 - k) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hf, Finset.card_range, Nat.cast_id]
  · apply Finset.sum_congr rfl
    intro i _
    have hnm : ¬ (m + i < m) := by omega
    have hcond : (m + i < 2 * m + 1 - k) = (i < m + 1 - k) := by rw [eq_iff_iff]; omega
    simp only [hg, hnm, if_neg, not_false_iff, hcond]

/-- The threshold gadget `[#ones ≥ k]` built from a Majority circuit on `2m+1` inputs. -/
def thresholdCirc (m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) : BoolCircuitSyntax m :=
  Layer4.padInputs (selector m k) Maj

theorem selector_isAC0p (p m k : ℕ) (i : Fin (2 * m + 1)) :
    IsAC0pSyntax p (selector m k i) := by
  unfold selector
  by_cases h : (i : ℕ) < m
  · simp [h, IsAC0pSyntax]
  · by_cases h2 : (i : ℕ) < 2 * m + 1 - k <;> simp [h, h2, IsAC0pSyntax]

theorem selector_depth (m k : ℕ) (i : Fin (2 * m + 1)) : (selector m k i).depth = 0 := by
  unfold selector
  by_cases h : (i : ℕ) < m
  · simp [h, BoolCircuitSyntax.depth]
  · by_cases h2 : (i : ℕ) < 2 * m + 1 - k <;> simp [h, h2, BoolCircuitSyntax.depth]

/-- **The gadget computes the threshold (proved).**  If `Maj` is Majority on `2m+1` inputs, the padded gadget
computes `[#ones(x) ≥ k]`. -/
theorem thresholdCirc_eval (m k : ℕ) (hk : k ≤ m + 1) (Maj : BoolCircuitSyntax (2 * m + 1))
    (hMaj : ∀ y, Maj.eval y
      = decide ((2 * m + 1 + 1) / 2 ≤ (univ.filter (fun i => y i = true)).card))
    (x : Fin m → Bool) :
    (thresholdCirc m k Maj).eval x = decide (k ≤ (univ.filter (fun j : Fin m => x j = true)).card) := by
  rw [thresholdCirc, Layer4.padInputs_eval]
  rw [show (fun i => (selector m k i).eval x) = padBits m k x from funext (selector_eval m k x)]
  rw [hMaj, trueCount_padBits m k hk x, decide_eq_decide]
  omega

/-- The gadget is `AC⁰[p]` whenever `Maj` is. -/
theorem thresholdCirc_isAC0p (p m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1))
    (hMaj : IsAC0pSyntax p Maj) : IsAC0pSyntax p (thresholdCirc m k Maj) :=
  Layer4.padInputs_isAC0pSyntax p (selector m k) (selector_isAC0p p m k) Maj hMaj

/-- The gadget has the same depth as `Maj` (padding substitutes only depth‑`0` leaves). -/
theorem thresholdCirc_depth (m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) :
    (thresholdCirc m k Maj).depth = Maj.depth :=
  Layer4.padInputs_depth (selector m k) (selector_depth m k) Maj

/-! ### Stage 2a: the `MOD_q` combination and its correctness -/

/-- `[#ones = k]` as `[#ones ≥ k] ∧ ¬[#ones ≥ k+1]`. -/
def andTerm (m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) : BoolCircuitSyntax m :=
  .andGate [thresholdCirc m k Maj, .not (thresholdCirc m (k + 1) Maj)]

/-- The `MOD_q` circuit: `⋁_{k ≤ m, k ≡ 0 (mod q)} [#ones = k]`. -/
def modqCirc (m q : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) : BoolCircuitSyntax m :=
  .orGate (((List.range (m + 1)).filter (fun k => k % q = 0)).map (fun k => andTerm m k Maj))

theorem andTerm_eval (m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) (x : Fin m → Bool) :
    (andTerm m k Maj).eval x
      = ((thresholdCirc m k Maj).eval x && !((thresholdCirc m (k + 1) Maj).eval x)) := by
  simp [andTerm, BoolCircuitSyntax.eval]

/-- `andTerm` computes `[#ones = k]`. -/
theorem andTerm_eval_eq (m k : ℕ) (hk : k ≤ m) (Maj : BoolCircuitSyntax (2 * m + 1))
    (hMaj : ∀ y, Maj.eval y
      = decide ((2 * m + 1 + 1) / 2 ≤ (univ.filter (fun i => y i = true)).card))
    (x : Fin m → Bool) :
    (andTerm m k Maj).eval x = decide ((univ.filter (fun j : Fin m => x j = true)).card = k) := by
  rw [andTerm_eval, thresholdCirc_eval m k (by omega) Maj hMaj,
      thresholdCirc_eval m (k + 1) (by omega) Maj hMaj]
  set c := (univ.filter (fun j : Fin m => x j = true)).card
  rcases Nat.lt_trichotomy c k with h | h | h
  · have e1 : decide (k ≤ c) = false := by rw [decide_eq_false_iff_not]; omega
    have e3 : decide (c = k) = false := by rw [decide_eq_false_iff_not]; omega
    rw [e1, e3, Bool.false_and]
  · have e1 : decide (k ≤ c) = true := by rw [decide_eq_true_eq]; omega
    have e2 : decide (k + 1 ≤ c) = false := by rw [decide_eq_false_iff_not]; omega
    have e3 : decide (c = k) = true := by rw [decide_eq_true_eq]; omega
    rw [e1, e2, e3, Bool.not_false, Bool.and_true]
  · have e1 : decide (k ≤ c) = true := by rw [decide_eq_true_eq]; omega
    have e2 : decide (k + 1 ≤ c) = true := by rw [decide_eq_true_eq]; omega
    have e3 : decide (c = k) = false := by rw [decide_eq_false_iff_not]; omega
    rw [e1, e2, e3, Bool.not_true, Bool.and_false]

/-- **The `MOD_q` circuit computes `MOD_q` (proved).**  If `Maj` computes Majority on `2m+1` inputs, then
`modqCirc` computes `[#ones(x) ≡ 0 (mod q)]`. -/
theorem modqCirc_eval (m q : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1))
    (hMaj : ∀ y, Maj.eval y
      = decide ((2 * m + 1 + 1) / 2 ≤ (univ.filter (fun i => y i = true)).card))
    (x : Fin m → Bool) :
    (modqCirc m q Maj).eval x = decide ((univ.filter (fun j : Fin m => x j = true)).card % q = 0) := by
  set c := (univ.filter (fun j : Fin m => x j = true)).card with hc
  have hcm : c ≤ m := by
    rw [hc]; exact le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_univ, Fintype.card_fin])
  have key : ∀ k ∈ (List.range (m + 1)).filter (fun k => k % q = 0),
      (andTerm m k Maj).eval x = decide (c = k) := by
    intro k hk
    rw [List.mem_filter, List.mem_range] at hk
    exact andTerm_eval_eq m k (by omega) Maj hMaj x
  simp only [modqCirc, BoolCircuitSyntax.eval, List.map_map, Function.comp_def]
  rw [List.map_congr_left key, List.any_map, Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨k, hkmem, hck⟩
    rw [List.mem_filter, List.mem_range] at hkmem
    have hck' : c = k := by simpa using hck
    have hk2 : k % q = 0 := by simpa using hkmem.2
    rw [decide_eq_true_eq, hck']
    exact hk2
  · intro h
    rw [decide_eq_true_eq] at h
    refine ⟨c, ?_, ?_⟩
    · rw [List.mem_filter, List.mem_range]
      exact ⟨by omega, by simp [h]⟩
    · simp

/-! ### Stage 2b: `AC⁰[p]` membership and constant depth -/

/-- The `MOD_q` circuit is `AC⁰[p]` whenever `Maj` is. -/
theorem modqCirc_isAC0p (p m q : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1))
    (hMaj : IsAC0pSyntax p Maj) : IsAC0pSyntax p (modqCirc m q Maj) := by
  simp only [modqCirc, IsAC0pSyntax, List.mem_map, forall_exists_index, and_imp]
  rintro C k _ rfl
  simp only [andTerm, IsAC0pSyntax, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false]
  rintro D (rfl | rfl)
  · exact thresholdCirc_isAC0p p m k Maj hMaj
  · simp only [IsAC0pSyntax]; exact thresholdCirc_isAC0p p m (k + 1) Maj hMaj

/-- A `foldl`‑max bound: if every circuit in the list has depth `≤ B`, the running max stays `≤ B`. -/
theorem foldl_max_depth_le {m : ℕ} (Cs : List (BoolCircuitSyntax m)) (B : ℕ) :
    ∀ acc : ℕ, acc ≤ B → (∀ C ∈ Cs, C.depth ≤ B) →
      Cs.foldl (fun a C => max a C.depth) acc ≤ B := by
  induction Cs with
  | nil => intro acc hacc _; exact hacc
  | cons C Cs ih =>
    intro acc hacc h
    apply ih
    · exact max_le hacc (h C (by simp))
    · intro D hD; exact h D (by simp [hD])

theorem andTerm_depth (m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) :
    (andTerm m k Maj).depth = Maj.depth + 2 := by
  simp only [andTerm, BoolCircuitSyntax.depth, List.foldl_cons, List.foldl_nil, thresholdCirc_depth]
  omega

theorem depth_orGate {m : ℕ} (Cs : List (BoolCircuitSyntax m)) :
    (BoolCircuitSyntax.orGate Cs).depth = Cs.foldl (fun a C => max a C.depth) 0 + 1 := by
  simp only [BoolCircuitSyntax.depth]

/-- The `MOD_q` circuit has constant depth `≤ Maj.depth + 3`. -/
theorem modqCirc_depth_le (m q : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) :
    (modqCirc m q Maj).depth ≤ Maj.depth + 3 := by
  simp only [modqCirc, depth_orGate]
  have h : (((List.range (m + 1)).filter (fun k => k % q = 0)).map
      (fun k => andTerm m k Maj)).foldl (fun a C => max a C.depth) 0 ≤ Maj.depth + 2 := by
    apply foldl_max_depth_le _ _ 0 (by omega)
    intro C hC
    rw [List.mem_map] at hC
    obtain ⟨k, _, rfl⟩ := hC
    exact (andTerm_depth m k Maj).le
  omega

/-! ### Stage 2c: polynomial size (subcircuit count) -/

theorem toFinset_card_cons_le {α : Type*} [DecidableEq α] (a : α) (l : List α) :
    (a :: l).toFinset.card ≤ l.toFinset.card + 1 := by
  rw [List.toFinset_cons]; exact Finset.card_insert_le _ _

theorem toFinset_card_append_le {α : Type*} [DecidableEq α] (l1 l2 : List α) :
    (l1 ++ l2).toFinset.card ≤ l1.toFinset.card + l2.toFinset.card := by
  rw [List.toFinset_append]; exact Finset.card_union_le _ _

open Classical in
theorem subcircuitsList_card_le {m : ℕ} (L : List (BoolCircuitSyntax m)) :
    (subcircuitsList L).toFinset.card ≤ (L.map (fun C => (subcircuits C).toFinset.card)).sum := by
  induction L with
  | nil => simp [subcircuitsList]
  | cons C Cs ih =>
    have heq : subcircuitsList (C :: Cs) = subcircuits C ++ subcircuitsList Cs := by
      simp only [subcircuitsList]
    rw [heq]
    refine (toFinset_card_append_le _ _).trans ?_
    simp only [List.map_cons, List.sum_cons]
    omega

open Classical in
theorem subcircuits_orGate_card_le {m : ℕ} (L : List (BoolCircuitSyntax m)) :
    (subcircuits (BoolCircuitSyntax.orGate L)).toFinset.card
      ≤ (L.map (fun C => (subcircuits C).toFinset.card)).sum + 1 := by
  have heq : subcircuits (BoolCircuitSyntax.orGate L) = .orGate L :: subcircuitsList L := by
    simp only [subcircuits]
  rw [heq]
  refine (toFinset_card_cons_le _ _).trans ?_
  have := subcircuitsList_card_le L
  omega

open Classical in
theorem selector_subcircuits_card_le (m k : ℕ) (i : Fin (2 * m + 1)) :
    (subcircuits (selector m k i)).toFinset.card ≤ 1 := by
  unfold selector
  by_cases h : (i : ℕ) < m
  · simp [h, subcircuits]
  · by_cases h2 : (i : ℕ) < 2 * m + 1 - k <;> simp [h, h2, subcircuits]

open Classical in
theorem thresholdCirc_subcircuits_card_le (m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) :
    (subcircuits (thresholdCirc m k Maj)).toFinset.card
      ≤ (subcircuits Maj).toFinset.card + (2 * m + 1) := by
  unfold thresholdCirc
  refine (Layer4.padInputs_subcircuits_card_le (selector m k) Maj).trans ?_
  have hs : ∑ i : Fin (2 * m + 1), (subcircuits (selector m k i)).toFinset.card
      ≤ ∑ _i : Fin (2 * m + 1), 1 :=
    Finset.sum_le_sum (fun i _ => selector_subcircuits_card_le m k i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hs
  omega

open Classical in
theorem andTerm_subcircuits_card_le (m k : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) :
    (subcircuits (andTerm m k Maj)).toFinset.card
      ≤ 2 * (subcircuits Maj).toFinset.card + 2 * (2 * m + 1) + 2 := by
  have heq : subcircuits (andTerm m k Maj)
      = .andGate [thresholdCirc m k Maj, .not (thresholdCirc m (k + 1) Maj)]
        :: (subcircuits (thresholdCirc m k Maj)
            ++ (.not (thresholdCirc m (k + 1) Maj) :: subcircuits (thresholdCirc m (k + 1) Maj))) := by
    simp only [andTerm, subcircuits, subcircuitsList, List.append_nil]
  rw [heq]
  have hA := thresholdCirc_subcircuits_card_le m k Maj
  have hB := thresholdCirc_subcircuits_card_le m (k + 1) Maj
  have c1 := toFinset_card_cons_le
    (BoolCircuitSyntax.andGate [thresholdCirc m k Maj, BoolCircuitSyntax.not (thresholdCirc m (k + 1) Maj)])
    (subcircuits (thresholdCirc m k Maj)
      ++ (BoolCircuitSyntax.not (thresholdCirc m (k + 1) Maj) :: subcircuits (thresholdCirc m (k + 1) Maj)))
  have c2 := toFinset_card_append_le (subcircuits (thresholdCirc m k Maj))
    (BoolCircuitSyntax.not (thresholdCirc m (k + 1) Maj) :: subcircuits (thresholdCirc m (k + 1) Maj))
  have c3 := toFinset_card_cons_le (BoolCircuitSyntax.not (thresholdCirc m (k + 1) Maj))
    (subcircuits (thresholdCirc m (k + 1) Maj))
  omega

/-! ### Stage 2d (i): `IsPolyBounded` closure -/

theorem pow_le_pow_add_one (n c1 c : ℕ) (h : c1 ≤ c) : n ^ c1 ≤ n ^ c + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases Nat.eq_zero_or_pos c1 with rfl | hc1
    · simp
    · rw [Nat.zero_pow (by omega)]; exact Nat.zero_le _
  · exact le_trans (Nat.pow_le_pow_right hn h) (Nat.le_succ _)

theorem pow_succ_le (m c : ℕ) : (m + 1) ^ c ≤ 2 ^ c * m ^ c + 2 ^ c := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.zero_add, Nat.one_pow]
    have : 1 ≤ 2 ^ c := Nat.one_le_two_pow
    nlinarith [Nat.zero_le (2 ^ c * (0:ℕ) ^ c)]
  · calc (m + 1) ^ c ≤ (2 * m) ^ c := Nat.pow_le_pow_left (by omega) c
      _ = 2 ^ c * m ^ c := by rw [mul_pow]
      _ ≤ 2 ^ c * m ^ c + 2 ^ c := Nat.le_add_right _ _

theorem ipb_const (b : ℕ) : Layer7.IsPolyBounded (fun _ => b) := ⟨0, 0, b, fun _ => by simp⟩

theorem ipb_linear (a b : ℕ) : Layer7.IsPolyBounded (fun m => a * m + b) :=
  ⟨a, 1, b, fun n => by rw [pow_one]⟩

theorem ipb_add {f g : ℕ → ℕ} (hf : Layer7.IsPolyBounded f) (hg : Layer7.IsPolyBounded g) :
    Layer7.IsPolyBounded (fun n => f n + g n) := by
  obtain ⟨a1, c1, b1, h1⟩ := hf
  obtain ⟨a2, c2, b2, h2⟩ := hg
  refine ⟨a1 + a2, max c1 c2, a1 + a2 + b1 + b2, fun n => ?_⟩
  have e1 : n ^ c1 ≤ n ^ max c1 c2 + 1 := pow_le_pow_add_one n c1 _ (le_max_left _ _)
  have e2 : n ^ c2 ≤ n ^ max c1 c2 + 1 := pow_le_pow_add_one n c2 _ (le_max_right _ _)
  calc f n + g n ≤ (a1 * n ^ c1 + b1) + (a2 * n ^ c2 + b2) := Nat.add_le_add (h1 n) (h2 n)
    _ ≤ (a1 * (n ^ max c1 c2 + 1) + b1) + (a2 * (n ^ max c1 c2 + 1) + b2) := by gcongr
    _ = (a1 + a2) * n ^ max c1 c2 + (a1 + a2 + b1 + b2) := by ring

theorem ipb_mul {f g : ℕ → ℕ} (hf : Layer7.IsPolyBounded f) (hg : Layer7.IsPolyBounded g) :
    Layer7.IsPolyBounded (fun n => f n * g n) := by
  obtain ⟨a1, c1, b1, h1⟩ := hf
  obtain ⟨a2, c2, b2, h2⟩ := hg
  refine ⟨a1 * a2 + a1 * b2 + b1 * a2, c1 + c2, a1 * b2 + b1 * a2 + b1 * b2, fun n => ?_⟩
  have e1 : n ^ c1 ≤ n ^ (c1 + c2) + 1 := pow_le_pow_add_one n c1 (c1 + c2) (by omega)
  have e2 : n ^ c2 ≤ n ^ (c1 + c2) + 1 := pow_le_pow_add_one n c2 (c1 + c2) (by omega)
  calc f n * g n ≤ (a1 * n ^ c1 + b1) * (a2 * n ^ c2 + b2) := Nat.mul_le_mul (h1 n) (h2 n)
    _ = a1 * a2 * (n ^ c1 * n ^ c2) + a1 * b2 * n ^ c1 + b1 * a2 * n ^ c2 + b1 * b2 := by ring
    _ = a1 * a2 * n ^ (c1 + c2) + a1 * b2 * n ^ c1 + b1 * a2 * n ^ c2 + b1 * b2 := by
        rw [← pow_add]
    _ ≤ a1 * a2 * n ^ (c1 + c2) + a1 * b2 * (n ^ (c1 + c2) + 1)
          + b1 * a2 * (n ^ (c1 + c2) + 1) + b1 * b2 := by gcongr
    _ = (a1 * a2 + a1 * b2 + b1 * a2) * n ^ (c1 + c2) + (a1 * b2 + b1 * a2 + b1 * b2) := by ring

theorem ipb_comp_affine {f : ℕ → ℕ} (hf : Layer7.IsPolyBounded f) (a b : ℕ) :
    Layer7.IsPolyBounded (fun m => f (a * m + b)) := by
  obtain ⟨A, C, B, hF⟩ := hf
  refine ⟨A * (a + b) ^ C * 2 ^ C, C, A * (a + b) ^ C * 2 ^ C + B, fun m => ?_⟩
  calc f (a * m + b) ≤ A * (a * m + b) ^ C + B := hF (a * m + b)
    _ ≤ A * ((a + b) * (m + 1)) ^ C + B := by
        gcongr
        nlinarith [Nat.zero_le (b * m), Nat.zero_le a]
    _ = A * ((a + b) ^ C * (m + 1) ^ C) + B := by rw [mul_pow]
    _ ≤ A * ((a + b) ^ C * (2 ^ C * m ^ C + 2 ^ C)) + B := by gcongr; exact pow_succ_le m C
    _ = A * (a + b) ^ C * 2 ^ C * m ^ C + (A * (a + b) ^ C * 2 ^ C + B) := by ring

theorem ipb_congr {f g : ℕ → ℕ} (h : ∀ n, f n = g n) (hg : Layer7.IsPolyBounded g) :
    Layer7.IsPolyBounded f := by
  obtain ⟨a, c, b, hb⟩ := hg
  exact ⟨a, c, b, fun n => by rw [h n]; exact hb n⟩

theorem ipb_succ : Layer7.IsPolyBounded (fun m => m + 1) := ⟨1, 1, 1, fun n => by simp⟩

/-! ### Stage 2d (ii): the size bound, the reduction family, and the conclusion -/

open Classical in
theorem modqCirc_subcircuits_card_le (m q : ℕ) (Maj : BoolCircuitSyntax (2 * m + 1)) :
    (subcircuits (modqCirc m q Maj)).toFinset.card
      ≤ (m + 1) * (2 * (subcircuits Maj).toFinset.card + 2 * (2 * m + 1) + 2) + 1 := by
  set B := 2 * (subcircuits Maj).toFinset.card + 2 * (2 * m + 1) + 2 with hB
  unfold modqCirc
  refine (subcircuits_orGate_card_le _).trans ?_
  simp only [List.map_map, Function.comp_def]
  set fks := (List.range (m + 1)).filter (fun k => k % q = 0) with hfks
  have hbound : ∀ x ∈ fks.map (fun k => (subcircuits (andTerm m k Maj)).toFinset.card), x ≤ B := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact andTerm_subcircuits_card_le m k Maj
  have hsum := List.sum_le_card_nsmul _ B hbound
  rw [List.length_map, smul_eq_mul] at hsum
  have hlen : fks.length ≤ m + 1 := by
    rw [hfks]; exact le_trans (List.length_filter_le _ _) (by rw [List.length_range])
  have hmul : fks.length * B ≤ (m + 1) * B := mul_le_mul_right' hlen B
  omega

open Classical in
/-- The `AC⁰[p]` family computing `MOD_q` built from a `Majority` family `F` (the reduction circuit). -/
def reductionFamily (p q : ℕ) (F : Layer7.AC0pFamily p) : Layer7.AC0pFamily p where
  circ := fun m => modqCirc m q (F.circ (2 * m + 1))
  isAC0p := fun m => modqCirc_isAC0p p m q (F.circ (2 * m + 1)) (F.isAC0p (2 * m + 1))
  depthBound := F.depthBound + 3
  hdepth := fun m => le_trans (modqCirc_depth_le m q (F.circ (2 * m + 1)))
    (by have := F.hdepth (2 * m + 1); omega)
  sizeBound := fun m => (m + 1) * (2 * F.sizeBound (2 * m + 1) + 2 * (2 * m + 1) + 2) + 1
  hsize := fun m => le_trans (modqCirc_subcircuits_card_le m q (F.circ (2 * m + 1)))
    (by gcongr; exact F.hsize (2 * m + 1))

/-- **The reduction `MOD_q ≤_{AC⁰[p]} Majority` (proved, no axioms beyond the standard trio).**  Builds, from
any poly‑size `AC⁰[p]` family computing `majorityLang`, a poly‑size `AC⁰[p]` family computing `modqLang q`. -/
theorem modq_AC0pReduction (p q : ℕ) :
    MajorityAC0pScope.AC0pReduction (Layer7.modqLang q) MajorityAC0pScope.majorityLang p := by
  intro F hpoly hComp
  refine ⟨reductionFamily p q F, ?_, ?_⟩
  · show Layer7.IsPolyBounded
        (fun m => (m + 1) * (2 * F.sizeBound (2 * m + 1) + 2 * (2 * m + 1) + 2) + 1)
    refine ipb_congr ?_ (ipb_add (ipb_mul ipb_succ (ipb_add (ipb_add
      (ipb_mul (ipb_const 2) (ipb_comp_affine hpoly 2 1)) (ipb_linear 4 2)) (ipb_const 2)))
      (ipb_const 1))
    intro m; ring
  · intro m x
    have hMaj : ∀ y, (F.circ (2 * m + 1)).eval y
        = decide ((2 * m + 1 + 1) / 2 ≤ (univ.filter (fun i => y i = true)).card) := by
      intro y; rw [hComp (2 * m + 1) y]; rfl
    show (modqCirc m q (F.circ (2 * m + 1))).eval x = Layer7.modqLang q m x
    rw [modqCirc_eval m q (F.circ (2 * m + 1)) hMaj x]
    rfl

/-! ### The unconditional payoff -/

/-- **`Majority ∉ AC⁰[p]` (unconditional, proved).**  Discharging the reduction, no poly‑size `AC⁰[p]` family
computes `majorityLang`. -/
theorem majority_not_in_AC0p (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    (F : Layer7.AC0pFamily p) (hpoly : Layer7.IsPolyBounded F.sizeBound) :
    ¬ F.Computes MajorityAC0pScope.majorityLang :=
  MajorityAC0pScope.majority_not_AC0p_of_reduction p q hpq (modq_AC0pReduction p q) F hpoly

/-- **Majority unconditionally resists the `AC⁰[p]` inverter class.** -/
theorem majority_resists_AC0p (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p) :
    UnifiedInverterFrontier.ResistsAC0p UnifiedInverterFrontier.majorityF2 p :=
  MajorityAC0pScope.majority_resists_AC0p_of_reduction p q hpq (modq_AC0pReduction p q)

/-- **The simultaneous‑resistance wall, unconditionally witnessed by Majority (proved).**  For `n = 2t-1` and
distinct primes `p ≠ q`, `majorityF2` resists **both** the low‑degree algebraic class and the `AC⁰[p]` class —
`SimultaneousAlgAC0pResistance` holds with no remaining hypothesis. -/
theorem majority_simultaneous_resistance {t : ℕ} (ht : 1 ≤ t)
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p) :
    UnifiedInverterFrontier.SimultaneousAlgAC0pResistance t p :=
  MajorityAC0pScope.majority_witnesses_simultaneous_of_reduction ht p q hpq (modq_AC0pReduction p q)

end PallLean.Paper93.DeepMath.PathB.ModqReducesMajority

#print axioms PallLean.Paper93.DeepMath.PathB.ModqReducesMajority.majority_not_in_AC0p
#print axioms PallLean.Paper93.DeepMath.PathB.ModqReducesMajority.majority_simultaneous_resistance
