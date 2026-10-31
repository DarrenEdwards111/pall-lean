import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCrossBlockSelectorPatterns

/-!
# N-Frame: split coverage, the mixed-engine assembly — same-block slot-2 separation dies

The first firing of `triples_kill_split_mixed` on produced patterns, and the honest audit of what it
closes.  A cut separating two slot-2 selectors of the **same block** supplies its own odd square and V1
triple, and a V0 source always exists: any other block's selector lies on one side or the other, giving a
separated cross-block pair either way.

  `sat3_split_killed_of_same_block_s2_separation` — **PROVED**: any bipartite split whose cut separates
        two slot-2 selectors of one block is refuted — odd + V1 from the pair itself, V0 from a
        constructed cross-block pair, `triples_kill_split_mixed` fires.
  `Sat3BlockMonolithicNoSplit` — the **thinned residual** (NOT discharged): refutation demanded only for
        proper cuts that are fully sign-aligned **and** keep each block's slot-2 selectors monolithic.
  `sat3_all_pins_aligned_of_block_monolithic` / `sat3_cbudget_2mD_of_block_monolithic` — the reduction
        and the conditional record through the standing chain.

## Honest scope — the audit

The produced patterns do **not** yet discharge `Sat3AllPinsAlignedNoSplit` outright, and the gap is
recorded exactly.  Full alignment makes the slot-0 sign layer monolithic; a surviving cut must now also
keep each block's slot-2 selectors together.  What survives both: cuts moving whole blocks (or slot-0/1
selectors, or slot-1/2 signs) across.  Killing those needs pattern types not yet produced: the
mixed-literal workhorse (probe plus pinned slot-2 literal, giving OR-shaped sign↔selector edges — with
the signs monolithic this is the decisive edge type), general-slot analogues of the `ZBase` flips for
slot-0/1 selectors, and slot-`t` probes for the remaining sign fields.  Each is a mirror of an existing
build.  Named, not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE SAME-BLOCK KILL (proved)**: a cut separating two slot-2 selectors of one block refutes the
split — the pair carries its own odd square and V1, and a cross-block V0 source always exists. -/
theorem sat3_split_killed_of_same_block_s2_separation (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) (j₁ j₂ : Fin (sat3V N))
    (hp : sat3S2Sel N c j₁ ∈ S) (hq : sat3S2Sel N c j₂ ∉ S) : False := by
  classical
  have hj : j₁ ≠ j₂ := by
    intro hcon
    subst hcon
    exact hq hp
  have hne12 : sat3S2Sel N c j₁ ≠ sat3S2Sel N c j₂ := by
    intro hcon
    have h1 := sat3S2Sel_rem N c j₁
    rw [hcon, sat3S2Sel_rem] at h1
    exact hj (Fin.ext (by omega))
  -- a second block, and its variable-0 selector
  have hc' : ∃ c' : Fin (sat3M N), c'.val ≠ c.val := by
    by_cases h0 : c.val = 0
    · exact ⟨⟨1, by omega⟩, by show (1 : ℕ) ≠ c.val; omega⟩
    · exact ⟨⟨0, by omega⟩, by show (0 : ℕ) ≠ c.val; omega⟩
  obtain ⟨c', hcc⟩ := hc'
  obtain ⟨hV1a, hV1b, hV1c⟩ := sat3_same_block_selector_V1 N hv c j₁ j₂ hj
  have hodd := sat3_same_block_selector_odd N hv c j₁ j₂
  by_cases hy : sat3S2Sel N c' ⟨0, hv⟩ ∈ S
  · -- V0 at (sel c' 0 ∈ S, sel c j₂ ∉ S)
    obtain ⟨hV0a, hV0b, hV0c⟩ :=
      sat3_cross_block_selector_V0 N hv c' c hcc ⟨0, hv⟩ j₂
    have hne3 : sat3S2Sel N c' ⟨0, hv⟩ ≠ sat3S2Sel N c j₂ := by
      intro hcon
      have hd := sat3S2Sel_div N c' ⟨0, hv⟩
      rw [hcon, sat3S2Sel_div] at hd
      exact hcc hd.symm
    exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
      (sat3S2Sel N c j₁) (sat3S2Sel N c j₂)
      (sat3S2Sel N c j₁) (sat3S2Sel N c j₂)
      (sat3S2Sel N c' ⟨0, hv⟩) (sat3S2Sel N c j₂)
      hp hq hne12 hp hq hne12 hy hq hne3
      (sat3ZBase N c)
      (Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true)
      (Function.update (sat3ZBase2 N c' c) (sat3S2Sel N c' ⟨0, hv⟩) true)
      hodd hV1a hV1b hV1c hV0a hV0b hV0c
  · -- V0 at (sel c j₁ ∈ S, sel c' 0 ∉ S)
    obtain ⟨hV0a, hV0b, hV0c⟩ :=
      sat3_cross_block_selector_V0 N hv c c' (fun h' => hcc h'.symm) j₁ ⟨0, hv⟩
    have hne3 : sat3S2Sel N c j₁ ≠ sat3S2Sel N c' ⟨0, hv⟩ := by
      intro hcon
      have hd := sat3S2Sel_div N c j₁
      rw [hcon, sat3S2Sel_div] at hd
      exact hcc hd
    exact triples_kill_split_mixed (sat3Family N) S op g h hg hh hf
      (sat3S2Sel N c j₁) (sat3S2Sel N c j₂)
      (sat3S2Sel N c j₁) (sat3S2Sel N c j₂)
      (sat3S2Sel N c j₁) (sat3S2Sel N c' ⟨0, hv⟩)
      hp hq hne12 hp hq hne12 hp hy hne3
      (sat3ZBase N c)
      (Function.update (sat3ZBase N c) (sat3S2Sel N c j₂) true)
      (Function.update (sat3ZBase2 N c c') (sat3S2Sel N c j₁) true)
      hodd hV1a hV1b hV1c hV0a hV0b hV0c

/-- The **thinned residual** (NOT discharged): fully sign-aligned cuts that additionally keep each
block's slot-2 selectors monolithic. -/
def Sat3BlockMonolithicNoSplit (N : ℕ) (hm3 : 3 ≤ sat3M N)
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
      (sat3S2Sel N c j₁ ∈ S ↔ sat3S2Sel N c j₂ ∈ S)) → False

/-- **THE REDUCTION (proved)**: killing block-monolithic cuts suffices for the all-pins residual. -/
theorem sat3_all_pins_aligned_of_block_monolithic (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3BlockMonolithicNoSplit N hm3 hk) :
    Sat3AllPinsAlignedNoSplit N hm3 hk := by
  intro op g h S hg hh hf hs ht hal
  classical
  by_cases hmono : ∀ (c : Fin (sat3M N)) (j₁ j₂ : Fin (sat3V N)),
      (sat3S2Sel N c j₁ ∈ S ↔ sat3S2Sel N c j₂ ∈ S)
  · exact hW op g h S hg hh hf hs ht hal hmono
  · push_neg at hmono
    obtain ⟨c, j₁, j₂, hciff⟩ := hmono
    rcases hciff with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact sat3_split_killed_of_same_block_s2_separation N hv hm3
        op g h S hg hh hf c j₁ j₂ hp hq
    · exact sat3_split_killed_of_same_block_s2_separation N hv hm3
        op g h S hg hh hf c j₂ j₁ hq hp

/-- **THE CONDITIONAL RECORD (hypothesis named, not claimed)**: block-monolithic residual ⇒
`2·m·D ≤ cbudget` — through the entire standing chain. -/
theorem sat3_cbudget_2mD_of_block_monolithic (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3BlockMonolithicNoSplit N hm3 hk) :
    2 * (sat3M N * sat3D N) ≤ cbudget (sat3Family N) :=
  sat3_cbudget_2mD_of_all_pins_aligned N hv hm3 hk
    (sat3_all_pins_aligned_of_block_monolithic N hv hm3 hk hW)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_split_killed_of_same_block_s2_separation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_2mD_of_block_monolithic
