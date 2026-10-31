import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Padding
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Assembly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Capstone

/-!
# Layer 4 (Route A) — `padTrue` subcircuit count, and the literal `MOD_q` family separation

The last bookkeeping step: bounding `#subcircuits (padTrue D)` so a **literal** `MOD_q ∈ AC⁰[p]` family
(rather than the per-residue indicator circuits of `mod_q_indicators_false`) drives the separation.

* **`mem_padInputs_subcircuits`** — every subcircuit of `padInputs f C` is either `padInputs f G` for some
  `G ∈ subcircuits C`, or a subcircuit of some `f i` (structural recursion through the gates).
* **`padInputs_subcircuits_card_le`** — hence `#subcircuits (padInputs f C) ≤ #subcircuits C +
  ∑ᵢ #subcircuits (f i)` (subset into `image ∪ biUnion`, then count).
* **`padTrue_subcircuits_card_le`** — for `padTrue` the substituted leaves are single nodes, so
  `#subcircuits (padTrue D) ≤ #subcircuits D + (n+k)` (the `q-j` pad bits add `≤ n+k` distinct leaves).

* **`mod_q_family_false`** — the separation from a literal family: for distinct primes `p ≠ q`, over
  `K = F_{p^{q-1}}`, there is **no** family `D_0,…,D_{q-1}` with each `D_j : BoolCircuitSyntax ((2m+1)+(q-j))`
  computing `MOD_q` (residue `0`), `AC⁰[p]`, of bounded size `4q·(#subcircuits + (2m+1+q)) ≤ p^t` and depth
  `≤ d`, inside the window `16·((p-1)t)^{2d} < 2m+3`.  Proof: set `C_j := padTrue (D_j)` (which computes
  `[#ones ≡ j]` by `padTrue_computes_indicator`, is `AC⁰[p]` by `padTrue_isAC0pSyntax`, has depth
  `(D_j).depth` by `padTrue_depth`, and size bounded by `padTrue_subcircuits_card_le`) and apply
  `mod_q_indicators_false`.  This is the **complete general-`q` Razborov–Smolensky lower bound**
  (`MOD_q = [#ones ≡ 0]`), assembled end-to-end and sorry-free.
-/

namespace PallLean.Paper93.DeepMath.PathB.Layer4

open PallLean.Paper93.DeepMath.PathB

/-- Every subcircuit of `padInputs f C` is either `padInputs f G` for some `G ∈ subcircuits C`, or a
subcircuit of some substituted leaf `f i`. -/
theorem mem_padInputs_subcircuits {m n : ℕ} (f : Fin m → BoolCircuitSyntax n) :
    ∀ (C : BoolCircuitSyntax m) (G : BoolCircuitSyntax n),
      G ∈ Layer3.subcircuits (padInputs f C) →
        (∃ G' ∈ Layer3.subcircuits C, G = padInputs f G') ∨ (∃ i, G ∈ Layer3.subcircuits (f i))
  | .const b, G, hG => by
      have hpad : padInputs f (.const b) = (.const b : BoolCircuitSyntax n) := by simp only [padInputs]
      rw [hpad, Layer3.subcircuits, List.mem_singleton] at hG
      exact Or.inl ⟨.const b, by rw [Layer3.subcircuits]; exact List.mem_singleton.mpr rfl,
        hG.trans hpad.symm⟩
  | .input i, G, hG => by
      have hpad : padInputs f (.input i) = f i := by simp only [padInputs]
      rw [hpad] at hG; exact Or.inr ⟨i, hG⟩
  | .not c, G, hG => by
      have hpad : padInputs f (.not c) = .not (padInputs f c) := by simp only [padInputs]
      rw [hpad, Layer3.subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact Or.inl ⟨.not c, by rw [Layer3.subcircuits]; exact List.mem_cons_self .., hpad.symm⟩
      · rcases mem_padInputs_subcircuits f c G hG with ⟨G', hG', rfl⟩ | ⟨i, hi⟩
        · exact Or.inl ⟨G', by rw [Layer3.subcircuits]; exact List.mem_cons_of_mem _ hG', rfl⟩
        · exact Or.inr ⟨i, hi⟩
  | .orGate cs, G, hG => by
      have hpad : padInputs f (.orGate cs) = .orGate (cs.map (padInputs f)) := by simp only [padInputs]
      rw [hpad, Layer3.subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact Or.inl ⟨.orGate cs, by rw [Layer3.subcircuits]; exact List.mem_cons_self .., hpad.symm⟩
      · obtain ⟨c', hc', hGc'⟩ := exists_of_mem_subcircuitsList G _ hG
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
        rcases mem_padInputs_subcircuits f c G hGc' with ⟨G', hG', rfl⟩ | ⟨i, hi⟩
        · exact Or.inl ⟨G', by rw [Layer3.subcircuits]; exact List.mem_cons_of_mem _ (Layer3.mem_subcircuitsList c cs hc G' hG'), rfl⟩
        · exact Or.inr ⟨i, hi⟩
  | .andGate cs, G, hG => by
      have hpad : padInputs f (.andGate cs) = .andGate (cs.map (padInputs f)) := by simp only [padInputs]
      rw [hpad, Layer3.subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact Or.inl ⟨.andGate cs, by rw [Layer3.subcircuits]; exact List.mem_cons_self .., hpad.symm⟩
      · obtain ⟨c', hc', hGc'⟩ := exists_of_mem_subcircuitsList G _ hG
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
        rcases mem_padInputs_subcircuits f c G hGc' with ⟨G', hG', rfl⟩ | ⟨i, hi⟩
        · exact Or.inl ⟨G', by rw [Layer3.subcircuits]; exact List.mem_cons_of_mem _ (Layer3.mem_subcircuitsList c cs hc G' hG'), rfl⟩
        · exact Or.inr ⟨i, hi⟩
  | .modGate a r cs, G, hG => by
      have hpad : padInputs f (.modGate a r cs) = .modGate a r (cs.map (padInputs f)) := by
        simp only [padInputs]
      rw [hpad, Layer3.subcircuits, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact Or.inl ⟨.modGate a r cs, by rw [Layer3.subcircuits]; exact List.mem_cons_self .., hpad.symm⟩
      · obtain ⟨c', hc', hGc'⟩ := exists_of_mem_subcircuitsList G _ hG
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
        rcases mem_padInputs_subcircuits f c G hGc' with ⟨G', hG', rfl⟩ | ⟨i, hi⟩
        · exact Or.inl ⟨G', by rw [Layer3.subcircuits]; exact List.mem_cons_of_mem _ (Layer3.mem_subcircuitsList c cs hc G' hG'), rfl⟩
        · exact Or.inr ⟨i, hi⟩

open Classical Finset in
/-- `#subcircuits (padInputs f C) ≤ #subcircuits C + ∑ᵢ #subcircuits (f i)`. -/
theorem padInputs_subcircuits_card_le {m n : ℕ} (f : Fin m → BoolCircuitSyntax n)
    (C : BoolCircuitSyntax m) :
    (Layer3.subcircuits (padInputs f C)).toFinset.card ≤
      (Layer3.subcircuits C).toFinset.card + ∑ i, (Layer3.subcircuits (f i)).toFinset.card := by
  have hsub : (Layer3.subcircuits (padInputs f C)).toFinset ⊆
      (Layer3.subcircuits C).toFinset.image (padInputs f)
        ∪ Finset.univ.biUnion (fun i => (Layer3.subcircuits (f i)).toFinset) := by
    intro G hG
    rw [List.mem_toFinset] at hG
    rcases mem_padInputs_subcircuits f C G hG with ⟨G', hG', rfl⟩ | ⟨i, hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨G', List.mem_toFinset.mpr hG', rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, List.mem_toFinset.mpr hi⟩)
  refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_union_le _ _) ?_)
  exact Nat.add_le_add Finset.card_image_le Finset.card_biUnion_le

open Classical Finset in
/-- **`padTrue` subcircuit count bound:** `#subcircuits (padTrue D) ≤ #subcircuits D + (n+k)` (each pad
leaf is a single node). -/
theorem padTrue_subcircuits_card_le {n k : ℕ} (D : BoolCircuitSyntax (n + k)) :
    (Layer3.subcircuits (padTrue D)).toFinset.card ≤ (Layer3.subcircuits D).toFinset.card + (n + k) := by
  rw [padTrue]
  refine le_trans (padInputs_subcircuits_card_le _ D) (Nat.add_le_add_left ?_ _)
  calc ∑ i : Fin (n + k),
          (Layer3.subcircuits (if h : (i : ℕ) < n then .input ⟨i, h⟩ else .const true)).toFinset.card
      ≤ ∑ _i : Fin (n + k), 1 := Finset.sum_le_sum (fun i _ => by
          by_cases h : (i : ℕ) < n <;> simp [h, Layer3.subcircuits])
    _ = n + k := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

open Classical Finset in
/-- **The general-`q` separation from a literal `MOD_q ∈ AC⁰[p]` family.**  For distinct primes `p ≠ q`,
over `K = F_{p^{q-1}}`: no family `D_0,…,D_{q-1}` (with `D_j` on `(2m+1)+(q-j)` inputs) can have each `D_j`
compute `MOD_q`, be `AC⁰[p]`, with `4q·(#subcircuits + (2m+1+q)) ≤ p^t` and `depth ≤ d`, inside the window
`16·((p-1)t)^{2d} < 2m+3`.  (`C_j := padTrue (D_j)` computes `[#ones ≡ j]`; apply `mod_q_indicators_false`.) -/
theorem mod_q_family_false (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : ¬ q ∣ p)
    {m t d : ℕ} (ht1 : 1 ≤ t) (hpt1 : 1 ≤ (p - 1) * t)
    (D : (j : ℕ) → BoolCircuitSyntax ((2 * m + 1) + (q - j)))
    (hD : ∀ j ∈ Finset.range q, ∀ x : Fin ((2 * m + 1) + (q - j)) → Bool,
      (D j).eval x = decide ((Finset.univ.filter (fun i => x i = true)).card % q = 0))
    (hDAC : ∀ j ∈ Finset.range q, BoolCircuitSyntax.IsAC0pSyntax p (D j))
    (hDsize : ∀ j ∈ Finset.range q,
      4 * q * ((Layer3.subcircuits (D j)).toFinset.card + ((2 * m + 1) + q)) ≤ p ^ t)
    (hDdepth : ∀ j ∈ Finset.range q, (D j).depth ≤ d)
    (hwindow : 16 * (((p - 1) * t) ^ d) ^ 2 < 2 * m + 3) : False := by
  have hq : 0 < q := (Fact.out (p := q.Prime)).pos
  refine mod_q_indicators_false p q hpq ht1 hpt1 (fun j => padTrue (D j)) ?_ ?_ ?_ ?_ hwindow
  · intro j hj x
    exact padTrue_computes_indicator hq (Finset.mem_range.mp hj) (D j) (hD j hj) x
  · intro j hj; exact padTrue_isAC0pSyntax p (D j) (hDAC j hj)
  · intro j hj
    refine le_trans (Nat.mul_le_mul_left _ (padTrue_subcircuits_card_le (D j)))
      (le_trans ?_ (hDsize j hj))
    gcongr
    omega
  · intro j hj; rw [padTrue_depth]; exact hDdepth j hj

end PallLean.Paper93.DeepMath.PathB.Layer4

#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.padTrue_subcircuits_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.Layer4.mod_q_family_false
