import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMTwoSliceKill

/-!
# Brick 4d of the `SlackComposes` m = 2 attack: THE FINALE

The remaining kills and the theorem:

* **`kill_g2_split` / `kill_g1_split` (proved)** — a gadget meeting the shared
  subtree in exactly two variables yields a literal `Split` of its `allEq3`
  restriction through the one-bit mediation — refuted by `allEq3_no_split`;
* **`kill_all_S` (proved)** — if every variable is in the shared subtree,
  `AEm 2 = U ∘ (wire s)` with `U` unary, and `unary_shape` reduces to the
  root-unary kills of brick 2a (the prefix would compute `±AEm 2` in ≤ 11
  gates);
* **`no_twelve_gate` (proved)** — the case driver: no 12-gate circuit computes
  `AEm 2`;
* **`cbudget_AEm_two` (proved)**: `13 ≤ cbudget (AEm 2)`;
* **`slackComposes_at_two` (proved)**: `7·2 − 1 ≤ cbudget (AEm 2)` — THE
  COMPOSITION BARRIER IS REFUTED AT m = 2.

Honest scope: this is one composition step (`+1` per gadget at `m = 2`); the
general `SlackComposes` (all `m`) and everything superpolynomial remain open.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- **The kill when gadget 2 meets the shared subtree in exactly two variables
(proved).** -/
theorem kill_g2_split (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (w₀ : Fin (3 * 2)) (hw₀3 : 3 ≤ w₀.val)
    (hw₀n : ¬ Reach c s (varPos c w₀))
    (hother : ∀ j : Fin (3 * 2), 3 ≤ j.val → j ≠ w₀ → Reach c s (varPos c j)) :
    False := by
  have hsl := hsh.s_lt
  have hs : s < c.length := by omega
  have h3 : (3:ℕ) < 3 * 2 := by omega
  have h4 : (4:ℕ) < 3 * 2 := by omega
  have h5 : (5:ℕ) < 3 * 2 := by omega
  have hmed : ∀ x, AEm 2 x = output (swapC c s (wire c x s)) x := fun x =>
    ((output_swapC c hs x).trans (hcomp x)).symm
  rcases fin6_hi w₀ hw₀3 with rfl | rfl | rfl
  · apply allEq3_no_split_a
    rw [← AEm_gadget2_allEq3 h3 h4 h5]
    refine ⟨fun d u => output (swapC c s u) (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ d),
      fun q r => wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ true) ⟨4, h4⟩ q) ⟨5, h5⟩ r) s, fun a b cc => ?_⟩
    show AEm 2 (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b) ⟨5, h5⟩ cc)
      = output (swapC c s (wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ true) ⟨4, h4⟩ b) ⟨5, h5⟩ cc) s)) (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a)
    rw [hmed]
    have hGeq : wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b) ⟨5, h5⟩ cc) s = wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ true) ⟨4, h4⟩ b) ⟨5, h5⟩ cc) s :=
      eval_agree_of_blind (fun z => wire c z s) (fun j => Reach c s (varPos c j))
        (fun j hj z b' => wire_s_blind c hsh hcomp hlen j hj z b') _ _
        (fun j hjS => by
          by_cases hjC : j = ⟨5, h5⟩
          · subst hjC
            rfl
          · by_cases hjB : j = ⟨4, h4⟩
            · subst hjB
              rfl
            · by_cases hjA : j = ⟨3, h3⟩
              · exact (hw₀n (by rw [← hjA]; exact hjS)).elim
              · rw [Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b),
                  Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ true) ⟨4, h4⟩ b),
                  Function.update_of_ne hjB b (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a),
                  Function.update_of_ne hjB b (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ true),
                  Function.update_of_ne hjA a ((fun _ : Fin (3 * 2) => true)),
                  Function.update_of_ne hjA true ((fun _ : Fin (3 * 2) => true))]
        )
    rw [hGeq]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a)
      (fun j hj => by
        by_cases hjP : j = ⟨3, h3⟩
        · subst hjP
          rfl
        · by_cases hjQ : j = ⟨4, h4⟩
          · rw [hjQ] at hj
            exact (hj (hother ⟨4, h4⟩ (by show (3:ℕ) ≤ 4; omega) (by intro he; simp at he))).elim
          · by_cases hjR : j = ⟨5, h5⟩
            · rw [hjR] at hj
              exact (hj (hother ⟨5, h5⟩ (by show (3:ℕ) ≤ 5; omega) (by intro he; simp at he))).elim
            · rw [Function.update_of_ne hjR cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b),
                Function.update_of_ne hjQ b (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a),
                Function.update_of_ne hjP a ((fun _ : Fin (3 * 2) => true))])
  · apply allEq3_no_split_b
    rw [← AEm_gadget2_allEq3 h3 h4 h5]
    refine ⟨fun d u => output (swapC c s u) (Function.update (fun _ : Fin (3 * 2) => true) ⟨4, h4⟩ d),
      fun q r => wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ q) ⟨4, h4⟩ true) ⟨5, h5⟩ r) s, fun a b cc => ?_⟩
    show AEm 2 (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b) ⟨5, h5⟩ cc)
      = output (swapC c s (wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ true) ⟨5, h5⟩ cc) s)) (Function.update (fun _ : Fin (3 * 2) => true) ⟨4, h4⟩ b)
    rw [hmed]
    have hGeq : wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b) ⟨5, h5⟩ cc) s = wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ true) ⟨5, h5⟩ cc) s :=
      eval_agree_of_blind (fun z => wire c z s) (fun j => Reach c s (varPos c j))
        (fun j hj z b' => wire_s_blind c hsh hcomp hlen j hj z b') _ _
        (fun j hjS => by
          by_cases hjC : j = ⟨5, h5⟩
          · subst hjC
            rfl
          · by_cases hjB : j = ⟨4, h4⟩
            · exact (hw₀n (by rw [← hjB]; exact hjS)).elim
            · by_cases hjA : j = ⟨3, h3⟩
              · subst hjA
                rfl
              · rw [Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b),
                  Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ true),
                  Function.update_of_ne hjB b (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a),
                  Function.update_of_ne hjB true (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a),
                  Function.update_of_ne hjA a ((fun _ : Fin (3 * 2) => true))]
        )
    rw [hGeq]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (Function.update (fun _ : Fin (3 * 2) => true) ⟨4, h4⟩ b)
      (fun j hj => by
        by_cases hjP : j = ⟨4, h4⟩
        · subst hjP
          rfl
        · by_cases hjQ : j = ⟨3, h3⟩
          · rw [hjQ] at hj
            exact (hj (hother ⟨3, h3⟩ (by show (3:ℕ) ≤ 3; omega) (by intro he; simp at he))).elim
          · by_cases hjR : j = ⟨5, h5⟩
            · rw [hjR] at hj
              exact (hj (hother ⟨5, h5⟩ (by show (3:ℕ) ≤ 5; omega) (by intro he; simp at he))).elim
            · rw [Function.update_of_ne hjR cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b),
                Function.update_of_ne hjP b (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a),
                Function.update_of_ne hjQ a ((fun _ : Fin (3 * 2) => true)),
                Function.update_of_ne hjP b ((fun _ : Fin (3 * 2) => true))])
  · apply allEq3_no_split_c
    rw [← AEm_gadget2_allEq3 h3 h4 h5]
    refine ⟨fun d u => output (swapC c s u) (Function.update (fun _ : Fin (3 * 2) => true) ⟨5, h5⟩ d),
      fun q r => wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ q) ⟨4, h4⟩ r) ⟨5, h5⟩ true) s, fun a b cc => ?_⟩
    show AEm 2 (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b) ⟨5, h5⟩ cc)
      = output (swapC c s (wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b) ⟨5, h5⟩ true) s)) (Function.update (fun _ : Fin (3 * 2) => true) ⟨5, h5⟩ cc)
    rw [hmed]
    have hGeq : wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b) ⟨5, h5⟩ cc) s = wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b) ⟨5, h5⟩ true) s :=
      eval_agree_of_blind (fun z => wire c z s) (fun j => Reach c s (varPos c j))
        (fun j hj z b' => wire_s_blind c hsh hcomp hlen j hj z b') _ _
        (fun j hjS => by
          by_cases hjC : j = ⟨5, h5⟩
          · exact (hw₀n (by rw [← hjC]; exact hjS)).elim
          · by_cases hjB : j = ⟨4, h4⟩
            · subst hjB
              rfl
            · by_cases hjA : j = ⟨3, h3⟩
              · subst hjA
                rfl
              · rw [Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b),
                  Function.update_of_ne hjC true (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b),
                  Function.update_of_ne hjB b (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a),
                  Function.update_of_ne hjA a ((fun _ : Fin (3 * 2) => true))]
        )
    rw [hGeq]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (Function.update (fun _ : Fin (3 * 2) => true) ⟨5, h5⟩ cc)
      (fun j hj => by
        by_cases hjP : j = ⟨5, h5⟩
        · subst hjP
          rfl
        · by_cases hjQ : j = ⟨3, h3⟩
          · rw [hjQ] at hj
            exact (hj (hother ⟨3, h3⟩ (by show (3:ℕ) ≤ 3; omega) (by intro he; simp at he))).elim
          · by_cases hjR : j = ⟨4, h4⟩
            · rw [hjR] at hj
              exact (hj (hother ⟨4, h4⟩ (by show (3:ℕ) ≤ 4; omega) (by intro he; simp at he))).elim
            · rw [Function.update_of_ne hjP cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a) ⟨4, h4⟩ b),
                Function.update_of_ne hjR b (Function.update (fun _ : Fin (3 * 2) => true) ⟨3, h3⟩ a),
                Function.update_of_ne hjQ a ((fun _ : Fin (3 * 2) => true)),
                Function.update_of_ne hjP cc ((fun _ : Fin (3 * 2) => true))])

/-- **The kill when gadget 1 meets the shared subtree in exactly two variables
(proved).** -/
theorem kill_g1_split (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (w₀ : Fin (3 * 2)) (hw₀3 : w₀.val < 3)
    (hw₀n : ¬ Reach c s (varPos c w₀))
    (hother : ∀ j : Fin (3 * 2), j.val < 3 → j ≠ w₀ → Reach c s (varPos c j)) :
    False := by
  have hsl := hsh.s_lt
  have hs : s < c.length := by omega
  have h0 : (0:ℕ) < 3 * 2 := by omega
  have h1 : (1:ℕ) < 3 * 2 := by omega
  have h2 : (2:ℕ) < 3 * 2 := by omega
  have hmed : ∀ x, AEm 2 x = output (swapC c s (wire c x s)) x := fun x =>
    ((output_swapC c hs x).trans (hcomp x)).symm
  rcases fin6_lo w₀ hw₀3 with rfl | rfl | rfl
  · apply allEq3_no_split_a
    rw [← AEm_gadget_allEq3 2 h0 h1 h2]
    refine ⟨fun d u => output (swapC c s u) (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ d),
      fun q r => wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ true) ⟨1, h1⟩ q) ⟨2, h2⟩ r) s, fun a b cc => ?_⟩
    show AEm 2 (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ cc)
      = output (swapC c s (wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ true) ⟨1, h1⟩ b) ⟨2, h2⟩ cc) s)) (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a)
    rw [hmed]
    have hGeq : wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ cc) s = wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ true) ⟨1, h1⟩ b) ⟨2, h2⟩ cc) s :=
      eval_agree_of_blind (fun z => wire c z s) (fun j => Reach c s (varPos c j))
        (fun j hj z b' => wire_s_blind c hsh hcomp hlen j hj z b') _ _
        (fun j hjS => by
          by_cases hjC : j = ⟨2, h2⟩
          · subst hjC
            rfl
          · by_cases hjB : j = ⟨1, h1⟩
            · subst hjB
              rfl
            · by_cases hjA : j = ⟨0, h0⟩
              · exact (hw₀n (by rw [← hjA]; exact hjS)).elim
              · rw [Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b),
                  Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ true) ⟨1, h1⟩ b),
                  Function.update_of_ne hjB b (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a),
                  Function.update_of_ne hjB b (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ true),
                  Function.update_of_ne hjA a ((fun _ : Fin (3 * 2) => true)),
                  Function.update_of_ne hjA true ((fun _ : Fin (3 * 2) => true))]
        )
    rw [hGeq]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a)
      (fun j hj => by
        by_cases hjP : j = ⟨0, h0⟩
        · subst hjP
          rfl
        · by_cases hjQ : j = ⟨1, h1⟩
          · rw [hjQ] at hj
            exact (hj (hother ⟨1, h1⟩ (by show (1:ℕ) < 3; omega) (by intro he; simp at he))).elim
          · by_cases hjR : j = ⟨2, h2⟩
            · rw [hjR] at hj
              exact (hj (hother ⟨2, h2⟩ (by show (2:ℕ) < 3; omega) (by intro he; simp at he))).elim
            · rw [Function.update_of_ne hjR cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b),
                Function.update_of_ne hjQ b (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a),
                Function.update_of_ne hjP a ((fun _ : Fin (3 * 2) => true))])
  · apply allEq3_no_split_b
    rw [← AEm_gadget_allEq3 2 h0 h1 h2]
    refine ⟨fun d u => output (swapC c s u) (Function.update (fun _ : Fin (3 * 2) => true) ⟨1, h1⟩ d),
      fun q r => wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ q) ⟨1, h1⟩ true) ⟨2, h2⟩ r) s, fun a b cc => ?_⟩
    show AEm 2 (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ cc)
      = output (swapC c s (wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ true) ⟨2, h2⟩ cc) s)) (Function.update (fun _ : Fin (3 * 2) => true) ⟨1, h1⟩ b)
    rw [hmed]
    have hGeq : wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ cc) s = wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ true) ⟨2, h2⟩ cc) s :=
      eval_agree_of_blind (fun z => wire c z s) (fun j => Reach c s (varPos c j))
        (fun j hj z b' => wire_s_blind c hsh hcomp hlen j hj z b') _ _
        (fun j hjS => by
          by_cases hjC : j = ⟨2, h2⟩
          · subst hjC
            rfl
          · by_cases hjB : j = ⟨1, h1⟩
            · exact (hw₀n (by rw [← hjB]; exact hjS)).elim
            · by_cases hjA : j = ⟨0, h0⟩
              · subst hjA
                rfl
              · rw [Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b),
                  Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ true),
                  Function.update_of_ne hjB b (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a),
                  Function.update_of_ne hjB true (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a),
                  Function.update_of_ne hjA a ((fun _ : Fin (3 * 2) => true))]
        )
    rw [hGeq]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (Function.update (fun _ : Fin (3 * 2) => true) ⟨1, h1⟩ b)
      (fun j hj => by
        by_cases hjP : j = ⟨1, h1⟩
        · subst hjP
          rfl
        · by_cases hjQ : j = ⟨0, h0⟩
          · rw [hjQ] at hj
            exact (hj (hother ⟨0, h0⟩ (by show (0:ℕ) < 3; omega) (by intro he; simp at he))).elim
          · by_cases hjR : j = ⟨2, h2⟩
            · rw [hjR] at hj
              exact (hj (hother ⟨2, h2⟩ (by show (2:ℕ) < 3; omega) (by intro he; simp at he))).elim
            · rw [Function.update_of_ne hjR cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b),
                Function.update_of_ne hjP b (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a),
                Function.update_of_ne hjQ a ((fun _ : Fin (3 * 2) => true)),
                Function.update_of_ne hjP b ((fun _ : Fin (3 * 2) => true))])
  · apply allEq3_no_split_c
    rw [← AEm_gadget_allEq3 2 h0 h1 h2]
    refine ⟨fun d u => output (swapC c s u) (Function.update (fun _ : Fin (3 * 2) => true) ⟨2, h2⟩ d),
      fun q r => wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ q) ⟨1, h1⟩ r) ⟨2, h2⟩ true) s, fun a b cc => ?_⟩
    show AEm 2 (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ cc)
      = output (swapC c s (wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ true) s)) (Function.update (fun _ : Fin (3 * 2) => true) ⟨2, h2⟩ cc)
    rw [hmed]
    have hGeq : wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ cc) s = wire c (Function.update (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b) ⟨2, h2⟩ true) s :=
      eval_agree_of_blind (fun z => wire c z s) (fun j => Reach c s (varPos c j))
        (fun j hj z b' => wire_s_blind c hsh hcomp hlen j hj z b') _ _
        (fun j hjS => by
          by_cases hjC : j = ⟨2, h2⟩
          · exact (hw₀n (by rw [← hjC]; exact hjS)).elim
          · by_cases hjB : j = ⟨1, h1⟩
            · subst hjB
              rfl
            · by_cases hjA : j = ⟨0, h0⟩
              · subst hjA
                rfl
              · rw [Function.update_of_ne hjC cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b),
                  Function.update_of_ne hjC true (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b),
                  Function.update_of_ne hjB b (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a),
                  Function.update_of_ne hjA a ((fun _ : Fin (3 * 2) => true))]
        )
    rw [hGeq]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (Function.update (fun _ : Fin (3 * 2) => true) ⟨2, h2⟩ cc)
      (fun j hj => by
        by_cases hjP : j = ⟨2, h2⟩
        · subst hjP
          rfl
        · by_cases hjQ : j = ⟨0, h0⟩
          · rw [hjQ] at hj
            exact (hj (hother ⟨0, h0⟩ (by show (0:ℕ) < 3; omega) (by intro he; simp at he))).elim
          · by_cases hjR : j = ⟨1, h1⟩
            · rw [hjR] at hj
              exact (hj (hother ⟨1, h1⟩ (by show (1:ℕ) < 3; omega) (by intro he; simp at he))).elim
            · rw [Function.update_of_ne hjP cc (Function.update (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a) ⟨1, h1⟩ b),
                Function.update_of_ne hjR b (Function.update (fun _ : Fin (3 * 2) => true) ⟨0, h0⟩ a),
                Function.update_of_ne hjQ a ((fun _ : Fin (3 * 2) => true)),
                Function.update_of_ne hjP cc ((fun _ : Fin (3 * 2) => true))])

/-- **The kill when every variable is in the shared subtree (proved).** -/
theorem kill_all_S (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12)
    (hall : ∀ j : Fin (3 * 2), Reach c s (varPos c j)) : False := by
  have hsl := hsh.s_lt
  have hs : s < c.length := by omega
  have hmed : ∀ x, AEm 2 x = output (swapC c s (wire c x s)) x := fun x =>
    ((output_swapC c hs x).trans (hcomp x)).symm
  have hU : ∀ x, AEm 2 x
      = output (swapC c s (wire c x s)) (fun _ : Fin (3 * 2) => true) := fun x =>
    (hmed x).trans (eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      x (fun _ => true) (fun j hj => absurd (hall j) hj))
  have htlen : (c.take (s + 1)).length = s + 1 := by
    rw [List.length_take]
    omega
  rcases unary_shape
      (fun u => output (swapC c s u) (fun _ : Fin (3 * 2) => true)) with hop | hop | hop
  · exact AEm_two_not_const (output (swapC c s false) (fun _ : Fin (3 * 2) => true))
      (fun x => (hU x).trans (hop (wire c x s)))
  · have hc' : computes (c.take (s + 1)) (AEm 2) := by
      intro x
      rw [wire_take_output c hs x]
      exact ((hU x).trans (hop (wire c x s))).symm
    have hle : cbudget (AEm 2) ≤ s + 1 :=
      le_trans (Nat.sInf_le ⟨c.take (s + 1), hc', rfl⟩) (le_of_eq htlen)
    have h12 := AEm_above_floor 2 (by omega)
    omega
  · have hc' : computes (c.take (s + 1)) (fun x => !(AEm 2 x)) := by
      intro x
      rw [wire_take_output c hs x]
      show wire c x s = !(AEm 2 x)
      rw [hU x, hop (wire c x s), Bool.not_not]
    have hle : cbudget (fun x => !(AEm 2 x)) ≤ s + 1 :=
      le_trans (Nat.sInf_le ⟨c.take (s + 1), hc', rfl⟩) (le_of_eq htlen)
    have h12 := cbudget_not_AEm_two
    omega

/-- **THE CASE DRIVER (proved)**: no 12-gate circuit computes `AEm 2`. -/
theorem no_twelve_gate (c : List (CGate (3 * 2))) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) : False := by
  obtain ⟨s, r₁, r₂, hsh⟩ := twelve_shape c hcomp hlen
  obtain ⟨⟨v₁, hv₁3, hv₁S⟩, ⟨v₂, hv₂3, hv₂S⟩⟩ := shape_S_hits c hsh hcomp hlen
  by_cases hg2 : ∀ j : Fin (3 * 2), 3 ≤ j.val → Reach c s (varPos c j) → j = v₂
  · exact kill_g2_single c hsh hcomp hlen v₁ v₂ hv₁3 hv₂3 hv₁S hv₂S hg2
  · push_neg at hg2
    obtain ⟨u₂, hu₂3, hu₂S, hu₂ne⟩ := hg2
    by_cases hg1 : ∀ j : Fin (3 * 2), j.val < 3 → Reach c s (varPos c j) → j = v₁
    · exact kill_g1_single c hsh hcomp hlen v₁ v₂ hv₁3 hv₂3 hv₁S hv₂S hg1
    · push_neg at hg1
      obtain ⟨u₁, hu₁3, hu₁S, hu₁ne⟩ := hg1
      by_cases hw2 : ∃ w₀ : Fin (3 * 2), 3 ≤ w₀.val ∧ ¬ Reach c s (varPos c w₀)
      · obtain ⟨w₀, hw₀3, hw₀n⟩ := hw2
        refine kill_g2_split c hsh hcomp hlen w₀ hw₀3 hw₀n ?_
        intro j hj3 hjne
        have hne2 : v₂.val ≠ w₀.val := fun he =>
          hw₀n (by rw [← Fin.ext he]; exact hv₂S)
        have hneu : u₂.val ≠ w₀.val := fun he =>
          hw₀n (by rw [← Fin.ext he]; exact hu₂S)
        have hjw : j.val ≠ w₀.val := fun he => hjne (Fin.ext he)
        have hvu : u₂.val ≠ v₂.val := fun he => hu₂ne (Fin.ext he)
        have hju : j.val = v₂.val ∨ j.val = u₂.val := by
          have b1 := j.isLt
          have b2 := v₂.isLt
          have b3 := u₂.isLt
          have b4 := w₀.isLt
          omega
        rcases hju with he | he
        · rw [Fin.ext he]
          exact hv₂S
        · rw [Fin.ext he]
          exact hu₂S
      · push_neg at hw2
        by_cases hw1 : ∃ w₀ : Fin (3 * 2), w₀.val < 3 ∧ ¬ Reach c s (varPos c w₀)
        · obtain ⟨w₀, hw₀3, hw₀n⟩ := hw1
          refine kill_g1_split c hsh hcomp hlen w₀ hw₀3 hw₀n ?_
          intro j hj3 hjne
          have hne2 : v₁.val ≠ w₀.val := fun he =>
            hw₀n (by rw [← Fin.ext he]; exact hv₁S)
          have hneu : u₁.val ≠ w₀.val := fun he =>
            hw₀n (by rw [← Fin.ext he]; exact hu₁S)
          have hjw : j.val ≠ w₀.val := fun he => hjne (Fin.ext he)
          have hvu : u₁.val ≠ v₁.val := fun he => hu₁ne (Fin.ext he)
          have hju : j.val = v₁.val ∨ j.val = u₁.val := by
            have b1 := j.isLt
            have b2 := v₁.isLt
            have b3 := u₁.isLt
            have b4 := w₀.isLt
            omega
          rcases hju with he | he
          · rw [Fin.ext he]
            exact hv₁S
          · rw [Fin.ext he]
            exact hu₁S
        · push_neg at hw1
          refine kill_all_S c hsh hcomp hlen ?_
          intro j
          rcases Nat.lt_or_ge j.val 3 with h | h
          · exact hw1 j h
          · exact hw2 j h

/-- **THE m = 2 LOWER BOUND (proved)**: `13 ≤ cbudget (AEm 2)`. -/
theorem cbudget_AEm_two : 13 ≤ cbudget (AEm 2) := by
  have h12 : 12 ≤ cbudget (AEm 2) := AEm_above_floor 2 (by omega)
  rcases Nat.lt_or_ge (cbudget (AEm 2)) 13 with h | h
  · exfalso
    obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem (cbudget_set_nonempty (AEm 2))
    have hclen' : c.length = cbudget (AEm 2) := hclen
    exact no_twelve_gate c hcomp (by omega)
  · exact h

/-- **SLACKCOMPOSES HOLDS AT m = 2 (proved)**: the composition barrier is
refuted at the first step — the slack is `+1` per gadget at `m = 2`. -/
theorem slackComposes_at_two : 7 * 2 - 1 ≤ cbudget (AEm 2) := by
  have := cbudget_AEm_two
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.no_twelve_gate
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_AEm_two
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.slackComposes_at_two
