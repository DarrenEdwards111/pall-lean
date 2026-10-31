import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTraceBlockPropagation

/-!
# N-Frame: the balanced wire cut — the swallowed-side recursion dissolves into selection

The swallowed-side problem asked what to do when the **top** cut is degenerate.  The answer is not
to recurse but to **cut elsewhere**: every wire `w` of a minimal circuit induces a one-sided cut
factorization across its cone boundary — the function's dependence on `vars(cone w)` factors
through the cone's **exit trace** — and every exit other than `w` itself has two distinct readers
(one inside the cone by `cone_parent`, one outside by the exit property, placed in the root cone by
fullness), so the trace width is at most `coneExcess + 1`.  A minimum-trick over the DAG then
selects a wire whose variable support is balanced at **any** threshold: no descent, no invariant to
maintain.

  `CutFactorization f S j` — the one-sided cut object: `f`'s dependence on the `S`-part factors
        through a `j`-bit trace of `S`.
  `cut_row_capacity` — **PROVED**: families with pairwise-distinct rows over `Sᶜ` have at most `2^j`
        members.
  `wireExits` / `wireExits_card_le` — **PROVED, the charge**: `|wireExits| ≤ coneExcess + 1`.
  `sat3_wire_cut_factorization` — **PROVED, the cut at any wire**: for every `w < root`,
        `CutFactorization (sat3Family N) (varsOf c w) |wireExits c w|`.
  `balanced_wire_exists` — **PROVED, the selection**: below any root with `≥ T` cone variables sits
        a wire with `T ≤ |varsOf| ≤ 2T − 2` — the minimum of the `≥ T` wires works, since its
        children fall below `T`.
  `sat3_balanced_cut` — **PROVED, the composite**: for every minimal SAT circuit and every threshold
        band, there is a coordinate set `S` with `T ≤ |S| ≤ 2T − 2` and a cut factorization of SAT
        over `S` with trace width `≤ coneExcess + 1`.

## Honest scope

The endgame now reads: a balanced `S` exists at every scale, with all of SAT's dependence on it
compressed into `coneExcess + 1` bits; producing `Ω(m)` pairwise-distinct rows over `Sᶜ` against an
*adversarial balanced* `S` is what remains.  The pin-context families read only pinned-variable
structure, and the current pin construction ties pin `j` to variable `j` — the generalized-pin and
selector-data workhorses that would widen the readable structure are the remaining semantic work,
named.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE ONE-SIDED CUT OBJECT**: `f`'s dependence on the `S`-part factors through a `j`-bit trace
of `S`. -/
def CutFactorization {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) (j : ℕ) : Prop :=
  ∃ φ : (Fin n → Bool) → (Fin j → Bool),
    (∀ x y : Fin n → Bool, (∀ i, i ∈ S → x i = y i) → φ x = φ y) ∧
    (∀ x y y' : Fin n → Bool, φ y = φ y' →
      f (mixOn Sᶜ x y) = f (mixOn Sᶜ x y'))

/-- **THE CUT ROW CAPACITY (proved)**: pairwise-distinct rows over `Sᶜ` are bounded by `2^j`. -/
theorem cut_row_capacity {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) (j : ℕ) (hcut : CutFactorization f S j)
    (Y : Finset (Fin n → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, f (mixOn Sᶜ x y) ≠ f (mixOn Sᶜ x y')) :
    Y.card ≤ 2 ^ j := by
  classical
  obtain ⟨φ, hφS, hφsep⟩ := hcut
  by_contra hbig
  push_neg at hbig
  have hcard : (Finset.univ : Finset (Fin j → Bool)).card < Y.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    omega
  obtain ⟨y, hy, y', hy', hne, hcol⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun y _ => Finset.mem_univ (φ y))
  obtain ⟨x, hx⟩ := hdist y hy y' hy' hne
  exact hx (hφsep x y y' hcol)

open Classical in
/-- The exit set of a single wire's cone: its wires read from outside, plus the wire itself. -/
noncomputable def wireExits {n : ℕ} (c : List (CGate n)) (w : ℕ) : Finset ℕ :=
  (coneOf c w).filter (fun u => u = w ∨
    ∃ r ∈ Finset.range c.length, r ∉ coneOf c w ∧ u ∈ childrenOf c r)

/-- **THE CHARGE (proved)**: every exit other than the wire itself has two distinct readers in the
root cone, so `|wireExits| ≤ coneExcess + 1`. -/
theorem wireExits_card_le {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (w : ℕ) (hw : w < c.length - 1) :
    (wireExits c w).card ≤ coneExcess c (c.length - 1) + 1 := by
  classical
  have herase : (wireExits c w).card ≤ ((wireExits c w).erase w).card + 1 := by
    by_cases hmem : w ∈ wireExits c w
    · have hpos := Finset.card_pos.mpr ⟨w, hmem⟩
      rw [Finset.card_erase_of_mem hmem]
      omega
    · rw [Finset.erase_eq_self.mpr hmem]
      omega
  refine le_trans herase (Nat.add_le_add_right ?_ 1)
  refine le_trans (Finset.card_le_card ?_)
    (coneExcess_ge_multiReader c (c.length - 1))
  intro u hu
  have huw : u ≠ w := Finset.ne_of_mem_erase hu
  have hu' := Finset.mem_of_mem_erase hu
  obtain ⟨hucone, hcase⟩ := Finset.mem_filter.mp hu'
  rcases hcase with h | ⟨rO, hrO, hrOnc, hrOch⟩
  · exact absurd h huw
  rcases cone_parent c w u hucone with heq | ⟨rI, hrI, hrIch⟩
  · exact absurd heq huw
  have hwcone_root : w ∈ coneOf c (c.length - 1) :=
    minimal_full_cone f c hcomp hmin w (by omega)
  have hrI_root : rI ∈ coneOf c (c.length - 1) :=
    cone_trans c _ w hwcone_root rI hrI
  have hrO_root : rO ∈ coneOf c (c.length - 1) := by
    rw [Finset.mem_range] at hrO
    exact minimal_full_cone f c hcomp hmin rO hrO
  have hune : rI ≠ rO := fun hcon => hrOnc (hcon ▸ hrI)
  have hu_root : u ∈ coneOf c (c.length - 1) :=
    cone_trans c _ w hwcone_root u hucone
  have hule : u ≤ w := cone_le c w u hucone
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_erase.mpr ⟨by omega, hu_root⟩, ?_⟩
  have h1lt : 1 < ((coneOf c (c.length - 1)).filter
      (fun q => u ∈ childrenOf c q)).card :=
    Finset.one_lt_card.mpr ⟨rI, Finset.mem_filter.mpr ⟨hrI_root, hrIch⟩,
      rO, Finset.mem_filter.mpr ⟨hrO_root, hrOch⟩, hune⟩
  omega

/-- **THE CUT AT ANY WIRE (proved)**: every wire below the root induces a cut factorization of SAT
over its cone's variable support, with the exit trace as interface. -/
theorem sat3_wire_cut_factorization (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (w : ℕ) (hw : w < c.length - 1) :
    CutFactorization (sat3Family N) (varsOf c w) (wireExits c w).card ∧
      (wireExits c w).card ≤ coneExcess c (c.length - 1) + 1 := by
  classical
  obtain ⟨opR, LL, RR, hroot, hLlt, hRlt, hLR⟩ :=
    sat3_root_shape N hv hm3 hk c hcomp hmin
  refine ⟨⟨fun z e => (runFrom z [] c).getD
      (((wireExits c w).equivFin.symm e).val) false, ?_, ?_⟩,
    wireExits_card_le (sat3Family N) c hcomp hmin w hw⟩
  · -- the trace is determined by the S-part
    intro z z' hzz
    funext e
    apply varsOf_agree_wire c (((wireExits c w).equivFin.symm e).val) z z'
    intro i hi
    apply hzz
    have hprop := ((wireExits c w).equivFin.symm e).2
    have hmemw : (((wireExits c w).equivFin.symm e).val) ∈ coneOf c w :=
      (Finset.mem_filter.mp hprop).1
    exact varsOf_mono c _ w hmemw hi
  · -- equal traces separate: the root value ignores the S-part beyond the trace
    intro x y y' hφeq
    have hsepPf : ∀ q ∈ coneOf c (c.length - 1), q ∉ coneOf c w →
        ∀ u ∈ childrenOf c q, u ∈ coneOf c w → u ∈ wireExits c w := by
      intro q hq hqT u huch huT
      exact Finset.mem_filter.mpr ⟨huT, Or.inr ⟨q, Finset.mem_range.mpr
        (by have := cone_le c (c.length - 1) q hq; omega), hqT, huch⟩⟩
    have hFvalPf : ∀ p ∈ wireExits c w,
        (runFrom (mixOn (varsOf c w)ᶜ x y) [] c).getD p false
          = (runFrom (mixOn (varsOf c w)ᶜ x y') [] c).getD p false := by
      intro p hp
      have hpmem : p ∈ coneOf c w := (Finset.mem_filter.mp hp).1
      have h1 : (runFrom (mixOn (varsOf c w)ᶜ x y) [] c).getD p false
          = (runFrom y [] c).getD p false := by
        apply varsOf_agree_wire
        intro i hi
        have hiS : i ∈ varsOf c w := varsOf_mono c p w hpmem hi
        show (if i ∈ (varsOf c w)ᶜ then x i else y i) = y i
        rw [if_neg (fun hc => (Finset.mem_compl.mp hc) hiS)]
      have h2 : (runFrom (mixOn (varsOf c w)ᶜ x y') [] c).getD p false
          = (runFrom y' [] c).getD p false := by
        apply varsOf_agree_wire
        intro i hi
        have hiS : i ∈ varsOf c w := varsOf_mono c p w hpmem hi
        show (if i ∈ (varsOf c w)ᶜ then x i else y' i) = y' i
        rw [if_neg (fun hc => (Finset.mem_compl.mp hc) hiS)]
      rw [h1, h2]
      have hidx := congrFun hφeq ((wireExits c w).equivFin ⟨p, hp⟩)
      simp only [Equiv.symm_apply_apply] at hidx
      exact hidx
    have hfrontPf : ∀ q ∈ coneOf c (c.length - 1), q ∉ coneOf c w →
        ∀ i, c.getD q (CGate.cst false) = CGate.var i →
        mixOn (varsOf c w)ᶜ x y i = mixOn (varsOf c w)ᶜ x y' i := by
      intro q hq hqT i hgate
      have hiNS : i ∉ varsOf c w := by
        intro hiS
        obtain ⟨-, p, hpw, hgate'⟩ := Finset.mem_filter.mp hiS
        have hple : p ≤ w := cone_le c w p hpw
        have hqle : q ≤ c.length - 1 := cone_le c (c.length - 1) q hq
        have hqlt : q < c.length - 1 := by
          rcases Nat.lt_or_eq_of_le hqle with h | h
          · exact h
          · exfalso
            rw [h, hroot] at hgate
            cases hgate
        have hpq : p = q := by
          rcases Nat.lt_trichotomy p q with hlt | heq | hgt
          · exact (var_gate_unique (sat3Family N) c hcomp hmin i p q hlt
              hqlt hgate' hgate).elim
          · exact heq
          · exact (var_gate_unique (sat3Family N) c hcomp hmin i q p hgt
              (by omega) hgate hgate').elim
        apply hqT
        rw [← hpq]
        exact hpw
      show (if i ∈ (varsOf c w)ᶜ then x i else y i)
        = (if i ∈ (varsOf c w)ᶜ then x i else y' i)
      rw [if_pos (Finset.mem_compl.mpr hiNS), if_pos (Finset.mem_compl.mpr hiNS)]
    have hrootnot : c.length - 1 ∉ coneOf c w := by
      intro hc
      have := cone_le c w (c.length - 1) hc
      omega
    have hmain := sep_frontier_val_agree c (c.length - 1) (coneOf c w)
      (wireExits c w) hsepPf (mixOn (varsOf c w)ᶜ x y) (mixOn (varsOf c w)ᶜ x y')
      hFvalPf hfrontPf (c.length - 1) (cone_self c (c.length - 1)) hrootnot
    calc sat3Family N (mixOn (varsOf c w)ᶜ x y)
        = (runFrom (mixOn (varsOf c w)ᶜ x y) [] c).getD (c.length - 1) false :=
          (hcomp _).symm
      _ = (runFrom (mixOn (varsOf c w)ᶜ x y') [] c).getD (c.length - 1) false :=
          hmain
      _ = sat3Family N (mixOn (varsOf c w)ᶜ x y') := hcomp _

/-- **THE SELECTION (proved)**: below any root with `≥ T` cone variables sits a wire whose variable
support lands in the band `[T, 2T − 2]` — the minimum of the `≥ T` wires, since its children fall
below `T`. -/
theorem balanced_wire_exists {n : ℕ} (c : List (CGate n)) (r : ℕ) (T : ℕ)
    (hT : 2 ≤ T) (hr : T ≤ (varsOf c r).card) :
    ∃ w ∈ coneOf c r, T ≤ (varsOf c w).card ∧ (varsOf c w).card ≤ 2 * T - 2 := by
  classical
  set W : Finset ℕ := (coneOf c r).filter (fun u => T ≤ (varsOf c u).card) with hW
  have hWne : W.Nonempty := ⟨r, Finset.mem_filter.mpr ⟨cone_self c r, hr⟩⟩
  obtain ⟨hw₀cone, hw₀T⟩ := Finset.mem_filter.mp (W.min'_mem hWne)
  refine ⟨W.min' hWne, hw₀cone, hw₀T, ?_⟩
  cases hg : c.getD (W.min' hWne) (CGate.cst false) with
  | var i =>
    exfalso
    have hcone := coneOf_eq_var c (W.min' hWne) i hg
    have hsub : varsOf c (W.min' hWne) ⊆ {i} := by
      intro i' hi'
      obtain ⟨-, p, hp, hgate⟩ := Finset.mem_filter.mp hi'
      rw [hcone] at hp
      have hpw : p = W.min' hWne := by
        rcases Finset.mem_insert.mp hp with h | h
        · exact h
        · exact absurd h (Finset.notMem_empty p)
      rw [hpw, hg] at hgate
      have hii : i = i' := by
        injection hgate
      rw [Finset.mem_singleton]
      exact hii.symm
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hcard
    omega
  | cst b =>
    exfalso
    have hcone := coneOf_eq_cst c (W.min' hWne) b hg
    have hsub : varsOf c (W.min' hWne) ⊆ ∅ := by
      intro i' hi'
      obtain ⟨-, p, hp, hgate⟩ := Finset.mem_filter.mp hi'
      rw [hcone] at hp
      have hpw : p = W.min' hWne := by
        rcases Finset.mem_insert.mp hp with h | h
        · exact h
        · exact absurd h (Finset.notMem_empty p)
      rw [hpw, hg] at hgate
      cases hgate
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_empty] at hcard
    omega
  | un op j =>
    exfalso
    have hcone := coneOf_eq_un c (W.min' hWne) op j hg
    by_cases hj : j < W.min' hWne
    · have hsub : varsOf c (W.min' hWne) ⊆ varsOf c j := by
        intro i' hi'
        obtain ⟨-, p, hp, hgate⟩ := Finset.mem_filter.mp hi'
        rw [hcone] at hp
        rcases Finset.mem_insert.mp hp with h | h
        · rw [h, hg] at hgate
          cases hgate
        · rw [dif_pos hj] at h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i', p, h, hgate⟩
      have hjcone : j ∈ coneOf c r := by
        apply cone_trans c r (W.min' hWne) hw₀cone j
        rw [hcone]
        exact Finset.mem_insert_of_mem (by rw [dif_pos hj]; exact cone_self c j)
      have hjW : j ∈ W := Finset.mem_filter.mpr
        ⟨hjcone, le_trans hw₀T (Finset.card_le_card hsub)⟩
      have := W.min'_le j hjW
      omega
    · have hsub : varsOf c (W.min' hWne) ⊆ ∅ := by
        intro i' hi'
        obtain ⟨-, p, hp, hgate⟩ := Finset.mem_filter.mp hi'
        rw [hcone] at hp
        rcases Finset.mem_insert.mp hp with h | h
        · rw [h, hg] at hgate
          cases hgate
        · rw [dif_neg hj] at h
          exact absurd h (Finset.notMem_empty p)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_empty] at hcard
      omega
  | bin op j k =>
    have hcone := coneOf_eq_bin c (W.min' hWne) op j k hg
    have hchildvars : ∀ u, u < W.min' hWne →
        (∀ i' ∈ varsOf c u, True) → u ∈ coneOf c (W.min' hWne) →
        (varsOf c u).card < T := by
      intro u hu _ hucone
      by_contra hge
      have hucone_r : u ∈ coneOf c r := cone_trans c r _ hw₀cone u hucone
      have huW : u ∈ W := Finset.mem_filter.mpr ⟨hucone_r, by omega⟩
      have := W.min'_le u huW
      omega
    by_cases hj : j < W.min' hWne <;> by_cases hkq : k < W.min' hWne
    · -- both children live: card ≤ (T−1) + (T−1)
      have hsub : varsOf c (W.min' hWne) ⊆ varsOf c j ∪ varsOf c k := by
        intro i' hi'
        obtain ⟨-, p, hp, hgate⟩ := Finset.mem_filter.mp hi'
        rw [hcone] at hp
        rcases Finset.mem_insert.mp hp with h | h
        · rw [h, hg] at hgate
          cases hgate
        · rcases Finset.mem_union.mp h with h' | h'
          · rw [dif_pos hj] at h'
            exact Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨Finset.mem_univ i', p, h', hgate⟩)
          · rw [dif_pos hkq] at h'
            exact Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨Finset.mem_univ i', p, h', hgate⟩)
      have hjc : (varsOf c j).card < T := by
        apply hchildvars j hj (fun _ _ => trivial)
        rw [hcone]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (by rw [dif_pos hj]; exact cone_self c j))
      have hkc : (varsOf c k).card < T := by
        apply hchildvars k hkq (fun _ _ => trivial)
        rw [hcone]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (by rw [dif_pos hkq]; exact cone_self c k))
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (varsOf c j) (varsOf c k)
      omega
    · -- only j lives: card ≤ T − 1 < T, contradiction
      exfalso
      have hsub : varsOf c (W.min' hWne) ⊆ varsOf c j := by
        intro i' hi'
        obtain ⟨-, p, hp, hgate⟩ := Finset.mem_filter.mp hi'
        rw [hcone] at hp
        rcases Finset.mem_insert.mp hp with h | h
        · rw [h, hg] at hgate
          cases hgate
        · rcases Finset.mem_union.mp h with h' | h'
          · rw [dif_pos hj] at h'
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ i', p, h', hgate⟩
          · rw [dif_neg hkq] at h'
            exact absurd h' (Finset.notMem_empty p)
      have hjc : (varsOf c j).card < T := by
        apply hchildvars j hj (fun _ _ => trivial)
        rw [hcone]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (by rw [dif_pos hj]; exact cone_self c j))
      have := Finset.card_le_card hsub
      omega
    · -- only k lives
      exfalso
      have hsub : varsOf c (W.min' hWne) ⊆ varsOf c k := by
        intro i' hi'
        obtain ⟨-, p, hp, hgate⟩ := Finset.mem_filter.mp hi'
        rw [hcone] at hp
        rcases Finset.mem_insert.mp hp with h | h
        · rw [h, hg] at hgate
          cases hgate
        · rcases Finset.mem_union.mp h with h' | h'
          · rw [dif_neg hj] at h'
            exact absurd h' (Finset.notMem_empty p)
          · rw [dif_pos hkq] at h'
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ i', p, h', hgate⟩
      have hkc : (varsOf c k).card < T := by
        apply hchildvars k hkq (fun _ _ => trivial)
        rw [hcone]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (by rw [dif_pos hkq]; exact cone_self c k))
      have := Finset.card_le_card hsub
      omega
    · -- neither lives: vars empty
      exfalso
      have hsub : varsOf c (W.min' hWne) ⊆ ∅ := by
        intro i' hi'
        obtain ⟨-, p, hp, hgate⟩ := Finset.mem_filter.mp hi'
        rw [hcone] at hp
        rcases Finset.mem_insert.mp hp with h | h
        · rw [h, hg] at hgate
          cases hgate
        · rcases Finset.mem_union.mp h with h' | h'
          · rw [dif_neg hj] at h'
            exact absurd h' (Finset.notMem_empty p)
          · rw [dif_neg hkq] at h'
            exact absurd h' (Finset.notMem_empty p)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_empty] at hcard
      omega

/-- **THE BALANCED CUT (proved)**: at every threshold band strictly below the root's support, a
minimal SAT circuit admits a cut factorization over a balanced coordinate set with trace width at
most `coneExcess + 1` — the swallowed-side recursion, dissolved into selection. -/
theorem sat3_balanced_cut (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf c (c.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2 ∧
      ∃ j : ℕ, j ≤ coneExcess c (c.length - 1) + 1 ∧
        CutFactorization (sat3Family N) S j := by
  obtain ⟨w, hwcone, hwT, hw2T⟩ := balanced_wire_exists c (c.length - 1) T hT
    (by omega)
  have hwne : w ≠ c.length - 1 := by
    intro hcon
    rw [hcon] at hw2T
    omega
  have hwlt : w < c.length - 1 :=
    Nat.lt_of_le_of_ne (cone_le c (c.length - 1) w hwcone) hwne
  obtain ⟨hcut, hj⟩ := sat3_wire_cut_factorization N hv hm3 hk c hcomp hmin w hwlt
  exact ⟨varsOf c w, hwT, hw2T, (wireExits c w).card, hj, hcut⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cut_row_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_wire_cut_factorization
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_balanced_cut
