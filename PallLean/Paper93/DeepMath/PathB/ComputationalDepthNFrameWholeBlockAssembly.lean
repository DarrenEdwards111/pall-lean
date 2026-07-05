import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSignSelectorPatterns

/-!
# N-Frame: the whole-block assembly — sign↔selector separation dies when a cross V0 exists

The mixed engine fired on the new edge type.

  `sat3_split_killed_of_sign_selector_separation` — **PROVED**: a cut separating a block's designated
        sign from one of its pinned slot-2 selectors, in either orientation, refutes the split —
        **provided** some cross-block slot-2 pair is also separated (the V0 source).  Odd and V1 come
        from the sign↔selector pair itself (`f = !sign ∨ sel`); the reversed orientation is an
        update-commutation plus an xor-shuffle.
  `Sat3MonolithicMassNoSplit` — the **thinned residual** (NOT discharged): pins aligned, blocks
        monolithic, and *either* every block's sign is aligned with its pinned selectors *or* the slot-2
        selector layer is globally monolithic.
  `sat3_block_monolithic_of_mass` / `sat3_cbudget_2mD_of_mass` — the reduction and the record.

## Honest scope

Surviving cuts are now essentially two-mass configurations: the sign layer and the slot-2 selector layer
each move as one body, and they may only separate *jointly* (all selectors vs all signs) — the
configuration the single-coordinate engine cannot touch, because sign↔selector tables never carry V0.
The named next engine is the **set-flip generalization** (`p, p⊕A, p⊕B, p⊕A⊕B` for known-side coordinate
sets, via `pinAll`), which turns block-sized selector flips and sign-package flips into op-matrix cells.
Slot-0/1 selectors and slot-1/2 signs also remain to be wired in.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE SIGN↔SELECTOR KILL (proved)**: separation of a block's sign from a pinned slot-2 selector,
plus any separated cross-block selector pair, refutes the split. -/
theorem sat3_split_killed_of_sign_selector_separation (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)) (hjv : j₀.val < sat3V N)
    (hsep : (sat3S2Sel N c ⟨j₀.val, hjv⟩ ∈ S ∧ sat3SignBit N c ∉ S)
      ∨ (sat3SignBit N c ∈ S ∧ sat3S2Sel N c ⟨j₀.val, hjv⟩ ∉ S))
    (c₁ c₂ : Fin (sat3M N)) (i₁ i₂ : Fin (sat3V N)) (hcc : c₁.val ≠ c₂.val)
    (hx1 : sat3S2Sel N c₁ i₁ ∈ S) (hx2 : sat3S2Sel N c₂ i₂ ∉ S) : False := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hne_ss : sat3S2Sel N c ⟨j₀.val, hjv⟩ ≠ sat3SignBit N c :=
    sat3S2Sel_ne_signBit N c ⟨j₀.val, hjv⟩ c
  have hne_cross : sat3S2Sel N c₁ i₁ ≠ sat3S2Sel N c₂ i₂ := by
    intro hcon
    have hd := sat3S2Sel_div N c₁ i₁
    rw [hcon, sat3S2Sel_div] at hd
    exact hcc hd.symm
  obtain ⟨hV0a, hV0b, hV0c⟩ :=
    sat3_cross_block_selector_V0 N hv c₁ c₂ hcc i₁ i₂
  have hodd := sat3_sign_selector_odd N hv hk hkv hm3 c j₀ hjv
  rcases hsep with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · -- orientation A: selector ∈ S, sign ∉ S — massage the odd square, V1 has the sign down
    obtain ⟨hV1a, hV1b, hV1c⟩ := sat3_sign_selector_V1_signDown N hv hk hkv hm3 c j₀ hjv
    have hodd' : xor (xor (sat3Family N (mixedPt N c hk j₀ hjv true false))
        (sat3Family N (Function.update (mixedPt N c hk j₀ hjv true false)
          (sat3S2Sel N c ⟨j₀.val, hjv⟩)
          (!(mixedPt N c hk j₀ hjv true false (sat3S2Sel N c ⟨j₀.val, hjv⟩))))))
      (xor (sat3Family N (Function.update (mixedPt N c hk j₀ hjv true false)
          (sat3SignBit N c)
          (!(mixedPt N c hk j₀ hjv true false (sat3SignBit N c)))))
        (sat3Family N (Function.update (Function.update
          (mixedPt N c hk j₀ hjv true false) (sat3S2Sel N c ⟨j₀.val, hjv⟩)
          (!(mixedPt N c hk j₀ hjv true false (sat3S2Sel N c ⟨j₀.val, hjv⟩))))
          (sat3SignBit N c)
          (!(mixedPt N c hk j₀ hjv true false (sat3SignBit N c)))))) = true := by
      rw [show Function.update (Function.update
          (mixedPt N c hk j₀ hjv true false) (sat3S2Sel N c ⟨j₀.val, hjv⟩)
          (!(mixedPt N c hk j₀ hjv true false (sat3S2Sel N c ⟨j₀.val, hjv⟩))))
          (sat3SignBit N c)
          (!(mixedPt N c hk j₀ hjv true false (sat3SignBit N c)))
        = Function.update (Function.update
          (mixedPt N c hk j₀ hjv true false) (sat3SignBit N c)
          (!(mixedPt N c hk j₀ hjv true false (sat3SignBit N c))))
          (sat3S2Sel N c ⟨j₀.val, hjv⟩)
          (!(mixedPt N c hk j₀ hjv true false (sat3S2Sel N c ⟨j₀.val, hjv⟩))) from
        Function.update_comm hne_ss _ _ _]
      rw [xor_shuffle]
      exact hodd
    exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
      (sat3S2Sel N c ⟨j₀.val, hjv⟩) (sat3SignBit N c)
      (sat3S2Sel N c ⟨j₀.val, hjv⟩) (sat3SignBit N c)
      (sat3S2Sel N c₁ i₁) (sat3S2Sel N c₂ i₂)
      hp hq hne_ss hp hq hne_ss hx1 hx2 hne_cross
      (mixedPt N c hk j₀ hjv true false)
      (mixedPt N c hk j₀ hjv false false)
      (Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ i₁) true)
      hodd' hV1a hV1b hV1c hV0a hV0b hV0c
  · -- orientation B: sign ∈ S, selector ∉ S — odd square direct, V1 has the selector down
    obtain ⟨hV1a, hV1b, hV1c⟩ := sat3_sign_selector_V1_selDown N hv hk hkv hm3 c j₀ hjv
    exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
      (sat3SignBit N c) (sat3S2Sel N c ⟨j₀.val, hjv⟩)
      (sat3SignBit N c) (sat3S2Sel N c ⟨j₀.val, hjv⟩)
      (sat3S2Sel N c₁ i₁) (sat3S2Sel N c₂ i₂)
      hp hq hne_ss.symm hp hq hne_ss.symm hx1 hx2 hne_cross
      (mixedPt N c hk j₀ hjv true false)
      (mixedPt N c hk j₀ hjv true true)
      (Function.update (sat3ZBase2 N c₁ c₂) (sat3S2Sel N c₁ i₁) true)
      hodd hV1a hV1b hV1c hV0a hV0b hV0c

/-- The **thinned residual** (NOT discharged): pins aligned, blocks monolithic, and either every block's
sign travels with its pinned selectors or the slot-2 layer is globally monolithic. -/
def Sat3MonolithicMassNoSplit (N : ℕ) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) : Prop :=
  ∀ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
    (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) →
    (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) →
    (∀ x, sat3Family N x = op (g x) (h x)) →
    (∃ s₀ : Fin N, s₀ ∈ S) → (∃ t₀ : Fin N, t₀ ∉ S) →
    (∀ (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)),
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ↔ sat3SignBit N cIdx ∈ S)) →
    (∀ (c : Fin (sat3M N)) (j₁ j₂ : Fin (sat3V N)),
      (sat3S2Sel N c j₁ ∈ S ↔ sat3S2Sel N c j₂ ∈ S)) →
    ((∀ (c : Fin (sat3M N)) (jv : Fin (sat3V N)), jv.val < sat3M N - 2 →
        (sat3S2Sel N c jv ∈ S ↔ sat3SignBit N c ∈ S))
      ∨ (∀ (c₁ c₂ : Fin (sat3M N)) (i₁ i₂ : Fin (sat3V N)),
        (sat3S2Sel N c₁ i₁ ∈ S ↔ sat3S2Sel N c₂ i₂ ∈ S))) → False

/-- **THE REDUCTION (proved)**: killing the two-mass cuts suffices for the block-monolithic residual. -/
theorem sat3_block_monolithic_of_mass (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3MonolithicMassNoSplit N hm3 hk) :
    Sat3BlockMonolithicNoSplit N hm3 hk := by
  intro op g h S hg hh hf hs ht hal hmono
  classical
  by_cases hglob : ∀ (c₁ c₂ : Fin (sat3M N)) (i₁ i₂ : Fin (sat3V N)),
      (sat3S2Sel N c₁ i₁ ∈ S ↔ sat3S2Sel N c₂ i₂ ∈ S)
  · exact hW op g h S hg hh hf hs ht hal hmono (Or.inr hglob)
  · by_cases hss : ∀ (c : Fin (sat3M N)) (jv : Fin (sat3V N)), jv.val < sat3M N - 2 →
        (sat3S2Sel N c jv ∈ S ↔ sat3SignBit N c ∈ S)
    · exact hW op g h S hg hh hf hs ht hal hmono (Or.inl hss)
    · -- a violated sign↔selector pair, and a separated cross-block pair from non-global-monolithicity
      push_neg at hglob hss
      obtain ⟨c, jv, hjpin, hciff⟩ := hss
      obtain ⟨c₁, c₂, i₁, i₂, hciff2⟩ := hglob
      have hjv : jv.val < sat3V N := by have := jv.isLt; omega
      have hcross : ∃ (d₁ d₂ : Fin (sat3M N)) (k₁ k₂ : Fin (sat3V N)),
          d₁.val ≠ d₂.val ∧ sat3S2Sel N d₁ k₁ ∈ S ∧ sat3S2Sel N d₂ k₂ ∉ S := by
        rcases hciff2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · by_cases hcb : c₁.val = c₂.val
          · exfalso
            apply h2
            have hce : c₁ = c₂ := Fin.ext hcb
            apply (hmono c₂ i₂ i₁).mpr
            rw [← hce]
            exact h1
          · exact ⟨c₁, c₂, i₁, i₂, hcb, h1, h2⟩
        · by_cases hcb : c₂.val = c₁.val
          · exfalso
            apply h1
            have hce : c₂ = c₁ := Fin.ext hcb
            apply (hmono c₁ i₁ i₂).mpr
            rw [← hce]
            exact h2
          · exact ⟨c₂, c₁, i₂, i₁, hcb, h2, h1⟩
      obtain ⟨d₁, d₂, k₁, k₂, hdd, hk1, hk2⟩ := hcross
      have hsep : (sat3S2Sel N c ⟨jv.val, hjv⟩ ∈ S ∧ sat3SignBit N c ∉ S)
          ∨ (sat3SignBit N c ∈ S ∧ sat3S2Sel N c ⟨jv.val, hjv⟩ ∉ S) := by
        have hjeta : sat3S2Sel N c ⟨jv.val, hjv⟩ = sat3S2Sel N c jv := rfl
        rw [hjeta]
        rcases hciff with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h2, h1⟩
      exact sat3_split_killed_of_sign_selector_separation N hv hm3 hk
        op g h S hg hh hf c ⟨jv.val, by omega⟩ hjv hsep d₁ d₂ k₁ k₂ hdd hk1 hk2

/-- **THE CONDITIONAL RECORD (hypothesis named, not claimed)**: two-mass residual ⇒
`2·m·D ≤ cbudget`. -/
theorem sat3_cbudget_2mD_of_mass (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3MonolithicMassNoSplit N hm3 hk) :
    2 * (sat3M N * sat3D N) ≤ cbudget (sat3Family N) :=
  sat3_cbudget_2mD_of_block_monolithic N hv hm3 hk
    (sat3_block_monolithic_of_mass N hv hm3 hk hW)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_split_killed_of_sign_selector_separation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_2mD_of_mass
