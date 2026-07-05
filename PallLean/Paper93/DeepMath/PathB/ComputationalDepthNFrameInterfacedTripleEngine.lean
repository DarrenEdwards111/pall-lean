import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSignGraphConnectivity

/-!
# N-Frame: the interfaced triple engine — lifting the selector families

The selector families carry L-triples (V1/V0), not XOR-squares, so lifting them to interfaced cuts
needs the triple analogue of `crossing_cells_kill_interfaced`.  Same discovery, same proof shape: the
triple corner analysis of `f = op (g|_A, h|_B)` never touches `A ∩ B` — only `s ∉ B`, `t ∉ A` enter.
The Bool core `odd_matrix_triples_kill` is reused verbatim.

  `crossing_triples_kill_interfaced` — **PROVED, the engine**: one odd square + one V1 triple + one V0
        triple, each crossing at its own pair (`op` is global), refute any interfaced factorization
        regardless of `|A ∩ B|`.  Subsumes `triples_kill_split_mixed` (the `A = S, B = Sᶜ` case).
  `sat3_selector_cells_kill_interfaced` — **PROVED**: a crossing same-block selector pair (odd + V1
        from `sat3_same_block_{odd,V1}_t`) plus a crossing cross-block selector pair (V0 from
        `sat3_cross_block_V0_t`) kill any interfaced factorization of `sat3Family` — any slots, any
        variables, any interface.
  `sat3_selector_pair_dodge` — **PROVED**: no interfaced factorization admits both a crossing
        same-block pair and a crossing cross-block pair (all four orientation combinations).
  `sat3_selector_family_dichotomy` — **PROVED**: every interfaced factorization dodges the whole
        same-block family or the whole cross-block family.

## Honest scope

This lifts the same-block and cross-block selector families.  The aligned-branch kill additionally
needs the **mixed sign↔selector** (V1-carrying) and **pinned-selector** (V0-carrying) families lifted —
those two supply the V1/V0 sources when signs and selectors sit on opposite sides — plus the counting
over the resulting cell graphs.  Named, not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE INTERFACED TRIPLE ENGINE (proved)**: odd square + V1 triple + V0 triple, each crossing at its
own pair, kill any interfaced factorization — the interface never enters. -/
theorem crossing_triples_kill_interfaced {n : ℕ} (f : (Fin n → Bool) → Bool)
    (A B : Finset (Fin n)) (op : Bool → Bool → Bool) (g h : (Fin n → Bool) → Bool)
    (hg : ∀ x y : Fin n → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin n → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, f x = op (g x) (h x))
    (s₁ t₁ s₂ t₂ s₃ t₃ : Fin n)
    (hs₁ : s₁ ∉ B) (ht₁ : t₁ ∉ A) (hst₁ : s₁ ≠ t₁)
    (hs₂ : s₂ ∉ B) (ht₂ : t₂ ∉ A) (hst₂ : s₂ ≠ t₂)
    (hs₃ : s₃ ∉ B) (ht₃ : t₃ ∉ A) (hst₃ : s₃ ≠ t₃)
    (w u₁ u₀ : Fin n → Bool)
    (hodd : xor (xor (f w) (f (Function.update w s₁ (!(w s₁)))))
        (xor (f (Function.update w t₁ (!(w t₁))))
          (f (Function.update (Function.update w s₁ (!(w s₁))) t₁ (!(w t₁))))) = true)
    (h11 : f u₁ = true)
    (h12 : f (Function.update (Function.update u₁ s₂ (!(u₁ s₂))) t₂ (!(u₁ t₂))) = true)
    (h13 : f (Function.update u₁ t₂ (!(u₁ t₂))) = false)
    (h01 : f u₀ = false)
    (h02 : f (Function.update (Function.update u₀ s₃ (!(u₀ s₃))) t₃ (!(u₀ t₃))) = false)
    (h03 : f (Function.update u₀ t₃ (!(u₀ t₃))) = true) : False := by
  classical
  have hhsP : ∀ s : Fin n, s ∉ B → ∀ (z : Fin n → Bool) (v : Bool),
      h (Function.update z s v) = h z := by
    intro s hs z v
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hc => hs (by rw [← hc]; exact hi)) _ _
  have hgtP : ∀ t : Fin n, t ∉ A → ∀ (z : Fin n → Bool) (v : Bool),
      g (Function.update z t v) = g z := by
    intro t ht z v
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hc => ht (by rw [← hc]; exact hi)) _ _
  simp only [hf] at hodd h11 h12 h13 h01 h02 h03
  rw [hhsP s₁ hs₁, hgtP t₁ ht₁, hgtP t₁ ht₁,
    Function.update_comm hst₁, hhsP s₁ hs₁] at hodd
  rw [hgtP t₂ ht₂] at h13
  rw [hgtP t₂ ht₂, Function.update_comm hst₂, hhsP s₂ hs₂] at h12
  rw [hgtP t₃ ht₃] at h03
  rw [hgtP t₃ ht₃, Function.update_comm hst₃, hhsP s₃ hs₃] at h02
  exact odd_matrix_triples_kill op (g w) (h w)
    (g (Function.update w s₁ (!(w s₁)))) (h (Function.update w t₁ (!(w t₁))))
    (g u₁) (h u₁)
    (g (Function.update u₁ s₂ (!(u₁ s₂)))) (h (Function.update u₁ t₂ (!(u₁ t₂))))
    (g u₀) (h u₀)
    (g (Function.update u₀ s₃ (!(u₀ s₃)))) (h (Function.update u₀ t₃ (!(u₀ t₃))))
    hodd h11 h12 h13 h01 h02 h03

/-- **THE SELECTOR KILL (proved)**: a crossing same-block pair (odd + V1) and a crossing cross-block
pair (V0) refute any interfaced factorization of `sat3Family` — any slots, variables, interface. -/
theorem sat3_selector_cells_kill_interfaced (N : ℕ) (hv : 1 ≤ sat3V N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N))
    (hne : sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)
      ≠ sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
    (hsb : sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega) ∉ B)
    (htb : sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega) ∉ A)
    (c₁ c₂ : Fin (sat3M N)) (hc : c₁.val ≠ c₂.val)
    (t₃ t₄ : Fin 3) (j₃ j₄ : Fin (sat3V N))
    (hsb' : sat3Bit N c₁ t₃ j₃.val (by have := j₃.isLt; omega) ∉ B)
    (htb' : sat3Bit N c₂ t₄ j₄.val (by have := j₄.isLt; omega) ∉ A) : False := by
  obtain ⟨v1a, v1b, v1c⟩ := sat3_same_block_V1_t N hv c t₁ t₂ j₁ j₂ hne
  obtain ⟨v0a, v0b, v0c⟩ := sat3_cross_block_V0_t N hv c₁ c₂ hc t₃ t₄ j₃ j₄
  exact crossing_triples_kill_interfaced (sat3Family N) A B op g h hg hh hf
    (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega))
    (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
    (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega))
    (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
    (sat3Bit N c₁ t₃ j₃.val (by have := j₃.isLt; omega))
    (sat3Bit N c₂ t₄ j₄.val (by have := j₄.isLt; omega))
    hsb htb hne hsb htb hne
    hsb' htb' (sat3Bit_ne_of_clause N _ _ _ _ hc)
    (sat3ZBase N c)
    (Function.update (sat3ZBase N c)
      (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega)) true)
    (Function.update (sat3ZBase2 N c₁ c₂)
      (sat3Bit N c₁ t₃ j₃.val (by have := j₃.isLt; omega)) true)
    (sat3_same_block_odd_t N hv c t₁ t₂ j₁ j₂)
    v1a v1b v1c v0a v0b v0c

/-- **THE SELECTOR DODGE (proved)**: no interfaced factorization admits both a crossing same-block
pair and a crossing cross-block pair — all four orientation combinations. -/
theorem sat3_selector_pair_dodge (N : ℕ) (hv : 1 ≤ sat3V N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N))
    (hne : sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)
      ≠ sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
    (c₁ c₂ : Fin (sat3M N)) (hc : c₁.val ≠ c₂.val)
    (t₃ t₄ : Fin 3) (j₃ j₄ : Fin (sat3V N)) :
    ¬ (((sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega) ∉ B
          ∧ sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega) ∉ A)
        ∨ (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega) ∉ B
          ∧ sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega) ∉ A))
      ∧ (((sat3Bit N c₁ t₃ j₃.val (by have := j₃.isLt; omega) ∉ B
          ∧ sat3Bit N c₂ t₄ j₄.val (by have := j₄.isLt; omega) ∉ A)
        ∨ (sat3Bit N c₂ t₄ j₄.val (by have := j₄.isLt; omega) ∉ B
          ∧ sat3Bit N c₁ t₃ j₃.val (by have := j₃.isLt; omega) ∉ A)))) := by
  rintro ⟨hSB | hSB, hCB | hCB⟩
  · exact sat3_selector_cells_kill_interfaced N hv op g h A B hg hh hf
      c t₁ t₂ j₁ j₂ hne hSB.1 hSB.2 c₁ c₂ hc t₃ t₄ j₃ j₄ hCB.1 hCB.2
  · exact sat3_selector_cells_kill_interfaced N hv op g h A B hg hh hf
      c t₁ t₂ j₁ j₂ hne hSB.1 hSB.2 c₂ c₁ (fun h' => hc h'.symm)
      t₄ t₃ j₄ j₃ hCB.1 hCB.2
  · exact sat3_selector_cells_kill_interfaced N hv op g h A B hg hh hf
      c t₂ t₁ j₂ j₁ hne.symm hSB.1 hSB.2 c₁ c₂ hc t₃ t₄ j₃ j₄ hCB.1 hCB.2
  · exact sat3_selector_cells_kill_interfaced N hv op g h A B hg hh hf
      c t₂ t₁ j₂ j₁ hne.symm hSB.1 hSB.2 c₂ c₁ (fun h' => hc h'.symm)
      t₄ t₃ j₄ j₃ hCB.1 hCB.2

/-- **THE SELECTOR FAMILY DICHOTOMY (proved)**: every interfaced factorization dodges the whole
same-block family or the whole cross-block family. -/
theorem sat3_selector_family_dichotomy (N : ℕ) (hv : 1 ≤ sat3V N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x)) :
    (∀ (c : Fin (sat3M N)) (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N)),
      sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)
        ≠ sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega) →
      ¬ ((sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega) ∉ B
          ∧ sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega) ∉ A)
        ∨ (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega) ∉ B
          ∧ sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega) ∉ A)))
    ∨ (∀ (c₁ c₂ : Fin (sat3M N)), c₁.val ≠ c₂.val →
        ∀ (t₃ t₄ : Fin 3) (j₃ j₄ : Fin (sat3V N)),
      ¬ ((sat3Bit N c₁ t₃ j₃.val (by have := j₃.isLt; omega) ∉ B
          ∧ sat3Bit N c₂ t₄ j₄.val (by have := j₄.isLt; omega) ∉ A)
        ∨ (sat3Bit N c₂ t₄ j₄.val (by have := j₄.isLt; omega) ∉ B
          ∧ sat3Bit N c₁ t₃ j₃.val (by have := j₃.isLt; omega) ∉ A))) := by
  classical
  by_cases hs : ∃ (c : Fin (sat3M N)) (t₁ t₂ : Fin 3) (j₁ j₂ : Fin (sat3V N)),
      (sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega)
        ≠ sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega))
      ∧ ((sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega) ∉ B
          ∧ sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega) ∉ A)
        ∨ (sat3Bit N c t₂ j₂.val (by have := j₂.isLt; omega) ∉ B
          ∧ sat3Bit N c t₁ j₁.val (by have := j₁.isLt; omega) ∉ A))
  · right
    intro c₁ c₂ hc t₃ t₄ j₃ j₄ hcross'
    obtain ⟨c, t₁, t₂, j₁, j₂, hne, hcross⟩ := hs
    exact sat3_selector_pair_dodge N hv op g h A B hg hh hf
      c t₁ t₂ j₁ j₂ hne c₁ c₂ hc t₃ t₄ j₃ j₄ ⟨hcross, hcross'⟩
  · left
    intro c t₁ t₂ j₁ j₂ hne hcross
    exact hs ⟨c, t₁, t₂, j₁, j₂, hne, hcross⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.crossing_triples_kill_interfaced
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_cells_kill_interfaced
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_family_dichotomy
