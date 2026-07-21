import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMTwoMediation

/-!
# Brick 4c of the `SlackComposes` m = 2 attack: the two-slice kills

The single-overlap cases: if the shared subtree meets a gadget in exactly one
variable `v₂`, two slices of the mediation share the same one-bit function `G`
(the gadget's other two variables are outside the subtree, so flipping them
changes only the swapped circuit's fixed input, not `G`'s argument), forcing
`a ∧ b` and `a ∧ ¬b` to both factor through `G` — impossible:

* `AEm_slice1` / `AEm_slice2g2` / `AEm_slice2g1` — the concrete slice values;
* `two_slice_contra` / `two_slice_contra'` — the Boolean impossibility;
* **`kill_g2_single` / `kill_g1_single` (proved)** — the kills.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-! ### Slice values -/

/-- All-true except the second gadget's non-`v₂` variables. -/
def g2base (v₂ : Fin (3 * 2)) : Fin (3 * 2) → Bool := fun j =>
  if 3 ≤ j.val ∧ j ≠ v₂ then false else true

/-- All-true except the first gadget's non-`v₁` variables. -/
def g1base (v₁ : Fin (3 * 2)) : Fin (3 * 2) → Bool := fun j =>
  if j.val < 3 ∧ j ≠ v₁ then false else true

theorem fin6_lo (v : Fin (3 * 2)) (h : v.val < 3) :
    v = ⟨0, by decide⟩ ∨ v = ⟨1, by decide⟩ ∨ v = ⟨2, by decide⟩ := by
  have hv : v.val = 0 ∨ v.val = 1 ∨ v.val = 2 := by omega
  rcases hv with hv | hv | hv
  · exact Or.inl (Fin.ext hv)
  · exact Or.inr (Or.inl (Fin.ext hv))
  · exact Or.inr (Or.inr (Fin.ext hv))

theorem fin6_hi (v : Fin (3 * 2)) (h : 3 ≤ v.val) :
    v = ⟨3, by decide⟩ ∨ v = ⟨4, by decide⟩ ∨ v = ⟨5, by decide⟩ := by
  have hlt := v.isLt
  have hv : v.val = 3 ∨ v.val = 4 ∨ v.val = 5 := by omega
  rcases hv with hv | hv | hv
  · exact Or.inl (Fin.ext hv)
  · exact Or.inr (Or.inl (Fin.ext hv))
  · exact Or.inr (Or.inr (Fin.ext hv))

theorem AEm_slice1 (v₁ v₂ : Fin (3 * 2)) (h1 : v₁.val < 3) (h2 : 3 ≤ v₂.val) :
    ∀ a b, AEm 2 (Function.update (Function.update
      (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b) = (a && b) := by
  rcases fin6_lo v₁ h1 with rfl | rfl | rfl <;>
    rcases fin6_hi v₂ h2 with rfl | rfl | rfl <;>
    intro a b <;> cases a <;> cases b <;> rfl

theorem AEm_slice2g2 (v₁ v₂ : Fin (3 * 2)) (h1 : v₁.val < 3) (h2 : 3 ≤ v₂.val) :
    ∀ a b, AEm 2 (Function.update (Function.update (g2base v₂) v₁ a) v₂ b)
      = (a && !b) := by
  rcases fin6_lo v₁ h1 with rfl | rfl | rfl <;>
    rcases fin6_hi v₂ h2 with rfl | rfl | rfl <;>
    intro a b <;> cases a <;> cases b <;> rfl

theorem AEm_slice2g1 (v₁ v₂ : Fin (3 * 2)) (h1 : v₁.val < 3) (h2 : 3 ≤ v₂.val) :
    ∀ a b, AEm 2 (Function.update (Function.update (g1base v₁) v₁ a) v₂ b)
      = (!a && b) := by
  rcases fin6_lo v₁ h1 with rfl | rfl | rfl <;>
    rcases fin6_hi v₂ h2 with rfl | rfl | rfl <;>
    intro a b <;> cases a <;> cases b <;> rfl

/-! ### The Boolean impossibility -/

theorem two_slice_contra (U₁ U₂ : Bool → Bool) (G₂ : Bool → Bool → Bool)
    (h₁ : ∀ a b, (a && b) = U₁ (G₂ a b)) (h₂ : ∀ a b, (a && !b) = U₂ (G₂ a b)) :
    False := by
  have e1 := h₁ true true
  have e2 := h₁ true false
  have e3 := h₁ false true
  have e4 := h₂ true false
  have e5 := h₂ false true
  cases hp : G₂ true true <;> cases hq : G₂ true false <;>
    cases hr : G₂ false true <;> simp_all

theorem two_slice_contra' (U₁ U₂ : Bool → Bool) (G₂ : Bool → Bool → Bool)
    (h₁ : ∀ a b, (a && b) = U₁ (G₂ a b)) (h₂ : ∀ a b, (!a && b) = U₂ (G₂ a b)) :
    False := by
  have e1 := h₁ true true
  have e2 := h₁ true false
  have e3 := h₁ false true
  have e4 := h₂ false true
  have e5 := h₂ true false
  cases hp : G₂ true true <;> cases hq : G₂ true false <;>
    cases hr : G₂ false true <;> simp_all

/-! ### The single-overlap kills -/

/-- **The kill when the shared subtree meets gadget 2 in exactly `v₂` (proved).** -/
theorem kill_g2_single (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (v₁ v₂ : Fin (3 * 2)) (h1 : v₁.val < 3)
    (h2 : 3 ≤ v₂.val) (hS1 : Reach c s (varPos c v₁)) (hS2 : Reach c s (varPos c v₂))
    (honly : ∀ j : Fin (3 * 2), 3 ≤ j.val → Reach c s (varPos c j) → j = v₂) :
    False := by
  have hsl := hsh.s_lt
  have hs : s < c.length := by omega
  have hv12 : v₁ ≠ v₂ := fun he => by rw [he] at h1; omega
  have hmed : ∀ x, AEm 2 x = output (swapC c s (wire c x s)) x := fun x =>
    ((output_swapC c hs x).trans (hcomp x)).symm
  refine two_slice_contra
    (fun u => output (swapC c s u) (fun _ : Fin (3 * 2) => true))
    (fun u => output (swapC c s u) (g2base v₂))
    (fun a b => wire c (Function.update (Function.update
      (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b) s) ?_ ?_
  · intro a b
    show (a && b) = output (swapC c s (wire c (Function.update (Function.update
      (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b) s)) (fun _ : Fin (3 * 2) => true)
    rw [← AEm_slice1 v₁ v₂ h1 h2 a b, hmed]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (fun _ => true) (fun j hj => by
        have hne1 : j ≠ v₁ := fun he => hj (by rw [he]; exact hS1)
        have hne2 : j ≠ v₂ := fun he => hj (by rw [he]; exact hS2)
        show Function.update (Function.update
          (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b j = true
        rw [Function.update_of_ne hne2 b
          (Function.update (fun _ : Fin (3 * 2) => true) v₁ a),
          Function.update_of_ne hne1 a (fun _ : Fin (3 * 2) => true)])
  · intro a b
    show (a && !b) = output (swapC c s (wire c (Function.update (Function.update
      (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b) s)) (g2base v₂)
    rw [← AEm_slice2g2 v₁ v₂ h1 h2 a b, hmed]
    have hGeq : wire c (Function.update (Function.update (g2base v₂) v₁ a) v₂ b) s
        = wire c (Function.update (Function.update
          (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b) s :=
      eval_agree_of_blind (fun z => wire c z s) (fun j => Reach c s (varPos c j))
        (fun j hj z b' => wire_s_blind c hsh hcomp hlen j hj z b')
        _ _ (fun j hjS => by
          by_cases hj2 : j = v₂
          · subst hj2
            rw [Function.update_self, Function.update_self]
          · by_cases hj1 : j = v₁
            · subst hj1
              rw [Function.update_of_ne hv12 b
                (Function.update (g2base v₂) j a),
                Function.update_of_ne hv12 b
                (Function.update (fun _ : Fin (3 * 2) => true) j a),
                Function.update_self, Function.update_self]
            · have hlt : j.val < 3 := by
                by_contra hge
                exact hj2 (honly j (by omega) hjS)
              rw [Function.update_of_ne hj2 b
                (Function.update (g2base v₂) v₁ a),
                Function.update_of_ne hj2 b
                (Function.update (fun _ : Fin (3 * 2) => true) v₁ a),
                Function.update_of_ne hj1 a (g2base v₂),
                Function.update_of_ne hj1 a (fun _ : Fin (3 * 2) => true)]
              show g2base v₂ j = true
              rw [g2base, if_neg (by
                rintro ⟨h3, -⟩
                omega)])
    rw [hGeq]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (g2base v₂) (fun j hj => by
        have hne1 : j ≠ v₁ := fun he => hj (by rw [he]; exact hS1)
        have hne2 : j ≠ v₂ := fun he => hj (by rw [he]; exact hS2)
        show Function.update (Function.update (g2base v₂) v₁ a) v₂ b j = g2base v₂ j
        rw [Function.update_of_ne hne2 b (Function.update (g2base v₂) v₁ a),
          Function.update_of_ne hne1 a (g2base v₂)])

/-- **The kill when the shared subtree meets gadget 1 in exactly `v₁` (proved).** -/
theorem kill_g1_single (c : List (CGate (3 * 2))) {s r₁ r₂ : ℕ}
    (hsh : TwelveShape c s r₁ r₂) (hcomp : computes c (AEm 2))
    (hlen : c.length = 12) (v₁ v₂ : Fin (3 * 2)) (h1 : v₁.val < 3)
    (h2 : 3 ≤ v₂.val) (hS1 : Reach c s (varPos c v₁)) (hS2 : Reach c s (varPos c v₂))
    (honly : ∀ j : Fin (3 * 2), j.val < 3 → Reach c s (varPos c j) → j = v₁) :
    False := by
  have hsl := hsh.s_lt
  have hs : s < c.length := by omega
  have hv12 : v₁ ≠ v₂ := fun he => by rw [he] at h1; omega
  have hmed : ∀ x, AEm 2 x = output (swapC c s (wire c x s)) x := fun x =>
    ((output_swapC c hs x).trans (hcomp x)).symm
  refine two_slice_contra'
    (fun u => output (swapC c s u) (fun _ : Fin (3 * 2) => true))
    (fun u => output (swapC c s u) (g1base v₁))
    (fun a b => wire c (Function.update (Function.update
      (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b) s) ?_ ?_
  · intro a b
    show (a && b) = output (swapC c s (wire c (Function.update (Function.update
      (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b) s)) (fun _ : Fin (3 * 2) => true)
    rw [← AEm_slice1 v₁ v₂ h1 h2 a b, hmed]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (fun _ => true) (fun j hj => by
        have hne1 : j ≠ v₁ := fun he => hj (by rw [he]; exact hS1)
        have hne2 : j ≠ v₂ := fun he => hj (by rw [he]; exact hS2)
        show Function.update (Function.update
          (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b j = true
        rw [Function.update_of_ne hne2 b
          (Function.update (fun _ : Fin (3 * 2) => true) v₁ a),
          Function.update_of_ne hne1 a (fun _ : Fin (3 * 2) => true)])
  · intro a b
    show (!a && b) = output (swapC c s (wire c (Function.update (Function.update
      (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b) s)) (g1base v₁)
    rw [← AEm_slice2g1 v₁ v₂ h1 h2 a b, hmed]
    have hGeq : wire c (Function.update (Function.update (g1base v₁) v₁ a) v₂ b) s
        = wire c (Function.update (Function.update
          (fun _ : Fin (3 * 2) => true) v₁ a) v₂ b) s :=
      eval_agree_of_blind (fun z => wire c z s) (fun j => Reach c s (varPos c j))
        (fun j hj z b' => wire_s_blind c hsh hcomp hlen j hj z b')
        _ _ (fun j hjS => by
          by_cases hj2 : j = v₂
          · subst hj2
            rw [Function.update_self, Function.update_self]
          · by_cases hj1 : j = v₁
            · subst hj1
              rw [Function.update_of_ne hv12 b
                (Function.update (g1base j) j a),
                Function.update_of_ne hv12 b
                (Function.update (fun _ : Fin (3 * 2) => true) j a),
                Function.update_self, Function.update_self]
            · have hge : 3 ≤ j.val := by
                by_contra hlt
                exact hj1 (honly j (by omega) hjS)
              rw [Function.update_of_ne hj2 b
                (Function.update (g1base v₁) v₁ a),
                Function.update_of_ne hj2 b
                (Function.update (fun _ : Fin (3 * 2) => true) v₁ a),
                Function.update_of_ne hj1 a (g1base v₁),
                Function.update_of_ne hj1 a (fun _ : Fin (3 * 2) => true)]
              show g1base v₁ j = true
              rw [g1base, if_neg (by
                rintro ⟨h3, -⟩
                omega)])
    rw [hGeq]
    exact eval_agree_of_blind _ (fun j => ¬ Reach c s (varPos c j))
      (fun j hj z b' => swapC_blind c hsh hcomp hlen _ j (not_not.mp hj) z b')
      _ (g1base v₁) (fun j hj => by
        have hne1 : j ≠ v₁ := fun he => hj (by rw [he]; exact hS1)
        have hne2 : j ≠ v₂ := fun he => hj (by rw [he]; exact hS2)
        show Function.update (Function.update (g1base v₁) v₁ a) v₂ b j = g1base v₁ j
        rw [Function.update_of_ne hne2 b (Function.update (g1base v₁) v₁ a),
          Function.update_of_ne hne1 a (g1base v₁)])

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kill_g2_single
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.kill_g1_single
