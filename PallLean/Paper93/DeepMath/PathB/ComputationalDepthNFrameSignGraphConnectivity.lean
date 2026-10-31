import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFramePositiveCellObstruction

/-!
# N-Frame: sign-graph connectivity — alignment or an `Ω(m)` interface

The first counting step past the dodge constraint.  The sign-pair cells of
`sat3_sign_pair_dodge` form a graph on the `m` blocks: block `d` is joined to block `p` whenever `p`
is one of `d`'s pin blocks.  From `sat3PinClause_val`, the pin blocks of `d` are `{0..m−2} \ {d}` —
the sign graph is the complete graph minus the single edge `{m−2, m−1}`.  So any two blocks are
**directly** joined unless they are that one pair; no path argument is needed, and the exception
costs a constant in the count.

  `sat3_signBit_ne` — sign bits of distinct blocks are distinct coordinates.
  `sat3_signBit_mem_union` — **PROVED**: every sign bit is essential, hence read: `∈ A ∪ B`.
  `sat3_sign_edge_same_side` — **PROVED, the edge rigidity**: for an edge (pin `p` < designated `d`,
        `p ≤ m−3`), two non-interned sign bits lie on the **same** exclusive side.
  `sat3_sign_alignment_or_interface` — **PROVED, the dichotomy**: for any interfaced factorization
        of `sat3Family`, either all non-interned sign bits lie in `A \ B`, or all lie in `B \ A`, or
        `m ≤ |A ∩ B| + 4`.  In the non-aligned branch this is an **`Ω(m)` interface bound**: a cut
        with sign bits on both exclusive sides must intern all but four sign bits — because every
        such bit is directly edge-constrained against both sides.

## Honest scope — what remains between this and `coneExcess ≥ Ω(m)`

Two named gaps, unclaimed: (1) the **aligned branch is not a contradiction** — it is the interfaced
version of Track A's sign-aligned residual, and killing it requires lifting the remaining pattern
families (selector pairs, mixed pairs, pinned pairs, slot probes) exactly as the Track A chain did at
interface zero; (2) the **circuit-to-factorization extraction with interface**: Track A's
`sat3_split_frame_proper` extracts a *zero*-interface factorization from a *zero*-excess minimal
circuit; the analogue "`coneExcess ≤ k` ⇒ factorization with `|A ∩ B| ≤ f(k)`" is not yet built —
the frontier machinery (`frontier_val_agree`, `coneExcess_ge_multiReader`) factors through *wire
values*, and converting a wire frontier into a *coordinate* interface is the missing structural
rung.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Sign bits of distinct blocks are distinct coordinates. -/
theorem sat3_signBit_ne (N : ℕ) {x y : Fin (sat3M N)} (h : x.val ≠ y.val) :
    sat3SignBit N x ≠ sat3SignBit N y := by
  show sat3Bit N x ⟨0, by omega⟩ (sat3V N) (by omega)
    ≠ sat3Bit N y ⟨0, by omega⟩ (sat3V N) (by omega)
  exact sat3Bit_ne_of_clause N _ _ _ _ h

/-- **Every sign bit is read (proved)**: the XOR-square corners make it essential, so it lies in
`A ∪ B`. -/
theorem sat3_signBit_mem_union (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (c : Fin (sat3M N)) : sat3SignBit N c ∈ A ∪ B := by
  by_contra hout
  rw [Finset.mem_union] at hout
  push_neg at hout
  obtain ⟨hA, hB⟩ := hout
  obtain ⟨u, hu, -, hut, -⟩ :=
    sat3_xor_square_all_pins N hv hm3 hk c ⟨0, by omega⟩ (fun _ => false)
  rw [hf] at hu hut
  have hgu : g (Function.update u (sat3SignBit N c) (!(u (sat3SignBit N c)))) = g u := by
    apply hg
    intro i hi
    exact Function.update_of_ne (fun hc => hA (by rw [← hc]; exact hi)) _ _
  have hhu : h (Function.update u (sat3SignBit N c) (!(u (sat3SignBit N c)))) = h u := by
    apply hh
    intro i hi
    exact Function.update_of_ne (fun hc => hB (by rw [← hc]; exact hi)) _ _
  rw [hgu, hhu, hu] at hut
  simp at hut

/-- **THE EDGE RIGIDITY (proved)**: across a sign-graph edge (pin `p` < designated `d`, `p ≤ m−3`),
two non-interned sign bits lie on the same exclusive side. -/
theorem sat3_sign_edge_same_side (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (p d : Fin (sat3M N)) (hpd : p.val < d.val) (hp3 : p.val + 3 ≤ sat3M N)
    (hpI : sat3SignBit N p ∉ A ∩ B) (hdI : sat3SignBit N d ∉ A ∩ B) :
    (sat3SignBit N p ∈ A \ B ∧ sat3SignBit N d ∈ A \ B) ∨
    (sat3SignBit N p ∈ B \ A ∧ sat3SignBit N d ∈ B \ A) := by
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin (sat3M N - 2), j₀.val = p.val :=
    ⟨⟨p.val, by omega⟩, rfl⟩
  have hpc : sat3PinClause N d hk j₀ = p := by
    apply Fin.ext
    rw [sat3PinClause_val, if_pos (show j₀.val < d.val by rw [hj₀]; exact hpd)]
    exact hj₀
  have hdodge := sat3_sign_pair_dodge N hv hm3 hk op g h A B hg hh hf d j₀
  rw [hpc] at hdodge
  have hdodge' : ¬((sat3SignBit N p ∉ B ∧ sat3SignBit N d ∉ A)
      ∨ (sat3SignBit N d ∉ B ∧ sat3SignBit N p ∉ A)) := hdodge
  push_neg at hdodge'
  obtain ⟨h1, h2⟩ := hdodge'
  have hpu := sat3_signBit_mem_union N hv hm3 hk op g h A B hg hh hf p
  have hdu := sat3_signBit_mem_union N hv hm3 hk op g h A B hg hh hf d
  rw [Finset.mem_union] at hpu hdu
  rw [Finset.mem_inter] at hpI hdI
  push_neg at hpI hdI
  simp only [Finset.mem_sdiff]
  by_cases hPA : sat3SignBit N p ∈ A <;>
    by_cases hDA : sat3SignBit N d ∈ A <;> tauto

/-- The low-index block pool: `m − 2` blocks of value `≤ m − 3`, as one named Finset. -/
theorem sat3_low_block_pool (N : ℕ) :
    ∃ T₀ : Finset (Fin (sat3M N)), T₀.card = sat3M N - 2 ∧
      ∀ b ∈ T₀, b.val + 3 ≤ sat3M N := by
  classical
  refine ⟨Finset.univ.map (Fin.castLEEmb (by omega : sat3M N - 2 ≤ sat3M N)), ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro b hb
    rw [Finset.mem_map] at hb
    obtain ⟨j, -, hj⟩ := hb
    rw [← hj]
    show j.val + 3 ≤ sat3M N
    have := j.isLt
    omega

/-- **THE SIGN-GRAPH DICHOTOMY (proved)**: for any interfaced factorization of `sat3Family`, either
all non-interned sign bits lie in `A \ B`, or all lie in `B \ A`, or the interface holds all but four
sign bits: `m ≤ |A ∩ B| + 4`. -/
theorem sat3_sign_alignment_or_interface (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (A B : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ A → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∈ B → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x)) :
    (∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ A \ B) ∨
    (∀ c : Fin (sat3M N), sat3SignBit N c ∉ A ∩ B → sat3SignBit N c ∈ B \ A) ∨
    sat3M N ≤ (A ∩ B).card + 4 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hL, hR, hcard⟩ := hcon
  obtain ⟨c₀, hc₀I, hc₀L⟩ := hL
  obtain ⟨c₁, hc₁I, hc₁R⟩ := hR
  have hdisj : ∀ x : Fin N, x ∈ A \ B → x ∈ B \ A → False := by
    intro x h1 h2
    rw [Finset.mem_sdiff] at h1 h2
    exact h2.2 h1.1
  -- region resolution: `c₀`'s bit is right-exclusive, `c₁`'s is left-exclusive
  have hc₀B : sat3SignBit N c₀ ∈ B \ A := by
    have hu := sat3_signBit_mem_union N hv hm3 hk op g h A B hg hh hf c₀
    rw [Finset.mem_union] at hu
    rw [Finset.mem_inter] at hc₀I
    rw [Finset.mem_sdiff] at hc₀L
    rw [Finset.mem_sdiff]
    push_neg at hc₀I hc₀L
    tauto
  have hc₁A : sat3SignBit N c₁ ∈ A \ B := by
    have hu := sat3_signBit_mem_union N hv hm3 hk op g h A B hg hh hf c₁
    rw [Finset.mem_union] at hu
    rw [Finset.mem_inter] at hc₁I
    rw [Finset.mem_sdiff] at hc₁R
    rw [Finset.mem_sdiff]
    push_neg at hc₁I hc₁R
    tauto
  obtain ⟨T₀, hT₀card, hT₀low⟩ := sat3_low_block_pool N
  -- every low-index block other than c₀, c₁ is interned: it is edge-joined to BOTH sides
  have hbint : ∀ b ∈ (T₀.erase c₀).erase c₁, sat3SignBit N b ∈ A ∩ B := by
    intro b hb
    have hbc₁ : b ≠ c₁ := Finset.ne_of_mem_erase hb
    have hb' : b ∈ T₀.erase c₀ := Finset.mem_of_mem_erase hb
    have hbc₀ : b ≠ c₀ := Finset.ne_of_mem_erase hb'
    have hbT₀ : b ∈ T₀ := Finset.mem_of_mem_erase hb'
    have hb3 : b.val + 3 ≤ sat3M N := hT₀low b hbT₀
    by_contra hbI
    have hbB : sat3SignBit N b ∈ B \ A := by
      rcases Nat.lt_or_ge b.val c₀.val with hlt | hge
      · rcases sat3_sign_edge_same_side N hv hm3 hk op g h A B hg hh hf
          b c₀ hlt hb3 hbI hc₀I with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact (hdisj _ hy hc₀B).elim
        · exact hx
      · have hlt' : c₀.val < b.val :=
          Nat.lt_of_le_of_ne hge (fun hh' => hbc₀ (Fin.ext hh'.symm))
        rcases sat3_sign_edge_same_side N hv hm3 hk op g h A B hg hh hf
          c₀ b hlt' (by omega) hc₀I hbI with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact (hdisj _ hx hc₀B).elim
        · exact hy
    have hbA : sat3SignBit N b ∈ A \ B := by
      rcases Nat.lt_or_ge b.val c₁.val with hlt | hge
      · rcases sat3_sign_edge_same_side N hv hm3 hk op g h A B hg hh hf
          b c₁ hlt hb3 hbI hc₁I with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact hx
        · exact (hdisj _ hc₁A hy).elim
      · have hlt' : c₁.val < b.val :=
          Nat.lt_of_le_of_ne hge (fun hh' => hbc₁ (Fin.ext hh'.symm))
        rcases sat3_sign_edge_same_side N hv hm3 hk op g h A B hg hh hf
          c₁ b hlt' (by omega) hc₁I hbI with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact hy
        · exact (hdisj _ hc₁A hx).elim
    exact hdisj _ hbA hbB
  -- counting: the interned pool injects into the interface
  have herase : ∀ (s : Finset (Fin (sat3M N))) (a : Fin (sat3M N)),
      s.card - 1 ≤ (s.erase a).card := by
    intro s a
    by_cases hmem : a ∈ s
    · rw [Finset.card_erase_of_mem hmem]
    · rw [Finset.erase_eq_self.mpr hmem]
      omega
  have hinjOn : Set.InjOn (sat3SignBit N) ↑((T₀.erase c₀).erase c₁) := by
    intro x _ y _ hxy
    by_contra hne
    exact sat3_signBit_ne N (fun hv' => hne (Fin.ext hv')) hxy
  have hsub : ((T₀.erase c₀).erase c₁).image (sat3SignBit N) ⊆ A ∩ B := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
    exact hbint b hb
  have hchain : ((T₀.erase c₀).erase c₁).card ≤ (A ∩ B).card := by
    rw [← Finset.card_image_of_injOn hinjOn]
    exact Finset.card_le_card hsub
  have e2 := herase T₀ c₀
  have e3 := herase (T₀.erase c₀) c₁
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_edge_same_side
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_alignment_or_interface
