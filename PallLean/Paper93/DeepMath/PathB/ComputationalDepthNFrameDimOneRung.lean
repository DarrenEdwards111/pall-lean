import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATTarget

/-!
# N-Frame: the bounded-dimension ladder — the dimension-1 rung (absolute tearing)

Step 6's bounded-dimension ladder, base rung, proved: at boundary dimension `1`, tearing is **absolute** — no energy
budget of any size computes even the XOR of two variables.  With the dimension no-go (`boundaryDim_le_three`) this pins
the ladder's two proven ends:

  `width_pos` / `width_one_junta` — **PROVED**: dimension-1 observers are juntas on at most one variable (a binary node
        forces dimension `≥ 2`).
  `xor2_needs_dim_two` — **PROVED, the rung**: any observer computing `x₀ ⊕ x₁` has dimension `≥ 2` — at dimension `1`
        the realization set is empty: **infinite tearing**, at every volume.

**The ladder**: dimension 1 — absolute tearing (this file, proved) · dimension 2 — the open classical regime
(width-2 super-polynomial bounds; BDFP-style literature to be verified before formalizing — named, not assumed) ·
dimension ≥ 3 — universal realizability (`boundaryDim_le_three`), where the content is the joint budget with its proven
`Ω(N²/log N)` Nečiporuk tearing.  The super-polynomial middle rung is the next genuine open step of the mountain path.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {n : ℕ}

theorem width_pos (t : Trans n) : 1 ≤ width t := by
  induction t with
  | var i => exact le_refl 1
  | cst b => exact le_refl 1
  | un op t ih => exact ih
  | bin op t₁ t₂ ih₁ ih₂ =>
    show 1 ≤ (if width t₁ = width t₂ then width t₁ + 1 else max (width t₁) (width t₂))
    split <;> omega

/-- **Dimension-1 observers are (at most) one-variable juntas (proved)**: a binary node forces dimension `≥ 2`. -/
theorem width_one_junta (t : Trans n) (h1 : width t = 1) :
    ∃ v : Option (Fin n), ∀ x y : Fin n → Bool,
      (∀ j : Fin n, v = some j → x j = y j) → eval t x = eval t y := by
  induction t with
  | var i =>
    exact ⟨some i, fun x y h => h i rfl⟩
  | cst b =>
    exact ⟨none, fun x y _ => rfl⟩
  | un op t ih =>
    obtain ⟨v, hv⟩ := ih h1
    exact ⟨v, fun x y h => congrArg op (hv x y h)⟩
  | bin op t₁ t₂ ih₁ ih₂ =>
    exfalso
    have hp₁ := width_pos t₁
    have hp₂ := width_pos t₂
    have : width (Trans.bin op t₁ t₂)
        = (if width t₁ = width t₂ then width t₁ + 1 else max (width t₁) (width t₂)) := rfl
    rw [this] at h1
    revert h1
    split <;> omega

/-- **The dimension-1 rung (proved, absolute)**: any observer computing `x₀ ⊕ x₁` has dimension `≥ 2` — at dimension
`1` the realization set is empty at every volume: infinite tearing. -/
theorem xor2_needs_dim_two (hn : 2 ≤ n) (t : Trans n)
    (ht : eval t = fun x => xor (x ⟨0, by omega⟩) (x ⟨1, by omega⟩)) :
    2 ≤ width t := by
  by_contra hlt
  have h1 : width t = 1 := by have := width_pos t; omega
  obtain ⟨v, hv⟩ := width_one_junta t h1
  -- pick a target variable the junta ignores
  have key : ∀ j : Fin n, (v ≠ some j) →
      eval t (fun _ => false) = eval t (Function.update (fun _ => false) j true) := by
    intro j hj
    apply hv
    intro k hk
    have hkj : k ≠ j := fun h => hj (h ▸ hk)
    rw [Function.update_of_ne hkj]
  have hne : v ≠ some (⟨0, by omega⟩ : Fin n) ∨ v ≠ some (⟨1, by omega⟩ : Fin n) := by
    by_cases h0 : v = some (⟨0, by omega⟩ : Fin n)
    · right
      rw [h0]
      intro hc
      have hval := congrArg Fin.val (Option.some_injective _ hc)
      simp at hval
    · exact Or.inl h0
  rcases hne with hne | hne
  · have hkey := key ⟨0, by omega⟩ hne
    rw [ht] at hkey
    simp only [Function.update_self] at hkey
    rw [Function.update_of_ne (show (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ from by
      intro hc
      have hval := congrArg Fin.val hc
      simp at hval)] at hkey
    simp at hkey
  · have hkey := key ⟨1, by omega⟩ hne
    rw [ht] at hkey
    simp only [Function.update_self] at hkey
    rw [Function.update_of_ne (show (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ from by
      intro hc
      have hval := congrArg Fin.val hc
      simp at hval)] at hkey
    simp at hkey

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.width_one_junta
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.xor2_needs_dim_two
