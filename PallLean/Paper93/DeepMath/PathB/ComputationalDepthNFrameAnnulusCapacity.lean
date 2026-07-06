import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameUniformBound

/-!
# N-Frame: the annulus capacity — the excess ledger becomes additive

Rung 22 of the multi-block arc (… → uniform bound → **annulus capacity**).  The k-scale
composition law: for a NESTED chain of wires, the joint trace over all scales has capacity
bounded by the inner trace plus the per-annulus NEW exits — and the new exits of disjoint
annuli are disjoint multi-read wires, so their counts add against a single `coneExcess`.

  `wireExits_nested` — **PROVED, the containment**: an exit of the outer wire lying in the
        inner cone is already an exit of the inner wire (a reader outside the outer cone is
        outside the inner cone).
  `exit_multiread` — **PROVED**: every exit other than the wire itself is a multi-read wire of
        the root cone (the extraction of the `wireExits_card_le` core).
  `chain_union_card` — **PROVED, coordinate counting**: the union of all scales' exit sets has
        cardinality at most `|exits(w_0)| + Σ_i |exits(w_{i+1}) ∖ cone(w_i)|`.
  `chain_exit_ledger` — **PROVED, the additive ledger**: that same sum is at most
        `coneExcess(root) + (k+1)` — the per-annulus new exits are pairwise-disjoint multi-read
        wires, so they are charged against `coneExcess` SIMULTANEOUSLY, not once per scale.
  `exit_value_separation` — **PROVED**: equal exit values force equal mixes at that scale (the
        single-cut separation, exposed — no existential trace).
  `sat3_chain_capacity` / `sat3_chain_capacity_excess` — **PROVED, THE k-SCALE CAPACITY**: any
        row family pairwise distinguished at SOME scale of the chain satisfies
        `|Y| ≤ 2^{|exits(w_0)| + Σ_i |newExits_i|} ≤ 2^{coneExcess + k + 1}`.
  `balanced_chain_exists` / `sat3_annulus_capacity` — **PROVED, the chain supply + composite**:
        nested chains exist at any prescribed increasing bands (recursing `balanced_wire_exists`
        inside the previous wire's cone), and the composite theorem packages chain + capacity.

## Honest scope — the cap, stated so it cannot be resurrected

This is the CAPACITY side only.  It makes the excess ledger additive across scales: `k+1`
nested cuts cost the adversary `coneExcess + k + 1` trace bits TOTAL, not `(coneExcess+1)` per
cut.  It does NOT by itself amplify the flat-sat3 lower bound beyond `Ω(√N)`: the DIVERSITY
side of the pin paradigm is capped at `Θ(v)` by the poison/full dichotomy — poisoning any
moderate cut's sign columns beyond `j+2` forces the slot-full horn (`coneExcess = Θ(v)`), and
below that threshold every pin instrument is applicable, so a contradiction argument can push
`coneExcess` only up to the instrument's own applicability threshold.  All scales share ONE
global poison budget; there is no per-annulus log-amplification, and the earlier
`Ω(√N·log N)` sketch was WRONG for exactly this reason.  Reaching `(2+c)·N` requires a
diversity channel that survives total sign poisoning (pinless, `ω(1)` bits per block), which
no instrument in this arc provides.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The nested-exit containment -/

/-- **The containment (proved)**: an exit of the outer wire lying in the inner cone is already
an exit of the inner wire. -/
theorem wireExits_nested {n : ℕ} (c : List (CGate n)) (w w' : ℕ)
    (hww' : w ∈ coneOf c w') :
    ∀ u ∈ wireExits c w', u ∈ coneOf c w → u ∈ wireExits c w := by
  classical
  intro u hu huw
  obtain ⟨hucone', hcase⟩ := Finset.mem_filter.mp hu
  rcases hcase with heq | ⟨r, hr, hrnc, hrch⟩
  · subst heq
    have h1 : u ≤ w := cone_le c w u huw
    have h2 : w ≤ u := cone_le c u w hww'
    have h3 : u = w := by omega
    subst h3
    exact Finset.mem_filter.mpr ⟨cone_self c u, Or.inl rfl⟩
  · refine Finset.mem_filter.mpr ⟨huw, Or.inr ⟨r, hr, ?_, hrch⟩⟩
    intro hrw
    exact hrnc (cone_trans c w' w hww' r hrw)

/-! ### The multi-read extraction -/

/-- **The multi-read extraction (proved)**: every exit other than the wire itself has an inside
and an outside reader in the root cone, hence is a multi-read wire. -/
theorem exit_multiread {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (w : ℕ) (hw : w < c.length - 1) :
    (wireExits c w).erase w ⊆
      ((coneOf c (c.length - 1)).erase (c.length - 1)).filter
        (fun u => 2 ≤ ((coneOf c (c.length - 1)).filter
          (fun q => u ∈ childrenOf c q)).card) := by
  classical
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
  exact Finset.one_lt_card.mpr ⟨rI, Finset.mem_filter.mpr ⟨hrI_root, hrIch⟩,
    rO, Finset.mem_filter.mpr ⟨hrO_root, hrOch⟩, hune⟩

/-! ### Chain cone monotonicity -/

theorem chain_cone_mono {n : ℕ} (c : List (CGate n)) (k : ℕ) (ws : ℕ → ℕ)
    (hchain : ∀ i, i < k → ws i ∈ coneOf c (ws (i + 1))) :
    ∀ a b, a ≤ b → b ≤ k → ws a ∈ coneOf c (ws b) := by
  intro a b
  induction b with
  | zero =>
    intro hab _
    have h0 : a = 0 := by omega
    rw [h0]
    exact cone_self c (ws 0)
  | succ b ih =>
    intro hab hbk
    rcases Nat.lt_or_eq_of_le hab with h | h
    · have h1 : ws a ∈ coneOf c (ws b) := ih (by omega) (by omega)
      exact cone_trans c (ws (b + 1)) (ws b) (hchain b (by omega)) (ws a) h1
    · rw [h]
      exact cone_self c (ws (b + 1))

/-! ### The coordinate count -/

/-- **Coordinate counting (proved)**: the union of all scales' exit sets is bounded by the
inner exits plus the per-annulus NEW exits — coordinates present at an earlier scale are never
recounted. -/
theorem chain_union_card {n : ℕ} (c : List (CGate n)) (k : ℕ) (ws : ℕ → ℕ)
    (hchain : ∀ i, i < k → ws i ∈ coneOf c (ws (i + 1))) :
    ((Finset.range (k + 1)).biUnion (fun i => wireExits c (ws i))).card
      ≤ (wireExits c (ws 0)).card
        + ∑ i ∈ Finset.range k,
            ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card := by
  classical
  induction k with
  | zero =>
    have h1 : (Finset.range (0 + 1)).biUnion (fun i => wireExits c (ws i))
        = wireExits c (ws 0) := by
      rw [show (0 : ℕ) + 1 = 1 from rfl, Finset.range_one, Finset.singleton_biUnion]
    rw [h1, Finset.range_zero, Finset.sum_empty]
    omega
  | succ k ih =>
    have hchain' : ∀ i, i < k → ws i ∈ coneOf c (ws (i + 1)) :=
      fun i hi => hchain i (by omega)
    have hsplit : (Finset.range (k + 1 + 1)).biUnion (fun i => wireExits c (ws i))
        = ((Finset.range (k + 1)).biUnion (fun i => wireExits c (ws i)))
          ∪ wireExits c (ws (k + 1)) := by
      rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
    have hcard : (((Finset.range (k + 1)).biUnion (fun i => wireExits c (ws i)))
        ∪ wireExits c (ws (k + 1))).card
        ≤ ((Finset.range (k + 1)).biUnion (fun i => wireExits c (ws i))).card
          + ((wireExits c (ws (k + 1)))
            \ ((Finset.range (k + 1)).biUnion (fun i => wireExits c (ws i)))).card := by
      rw [← Finset.union_sdiff_self_eq_union]
      exact Finset.card_union_le _ _
    have hnew : ((wireExits c (ws (k + 1)))
        \ ((Finset.range (k + 1)).biUnion (fun i => wireExits c (ws i))))
        ⊆ ((wireExits c (ws (k + 1))) \ (coneOf c (ws k))) := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := Finset.mem_sdiff.mp hu
      refine Finset.mem_sdiff.mpr ⟨hu1, ?_⟩
      intro hucone
      apply hu2
      refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
      exact wireExits_nested c (ws k) (ws (k + 1)) (hchain k (by omega)) u hu1 hucone
    have hsum : ∑ i ∈ Finset.range (k + 1),
        ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card
        = (∑ i ∈ Finset.range k,
            ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card)
          + ((wireExits c (ws (k + 1))) \ (coneOf c (ws k))).card :=
      Finset.sum_range_succ _ k
    have hle := Finset.card_le_card hnew
    have hih := ih hchain'
    rw [hsplit]
    omega

/-! ### The additive ledger -/

set_option maxHeartbeats 1600000 in
/-- **THE ADDITIVE LEDGER (proved)**: the inner exits plus all per-annulus new exits are
charged against ONE `coneExcess` — the pieces are pairwise-disjoint multi-read wire sets. -/
theorem chain_exit_ledger {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (k : ℕ) (ws : ℕ → ℕ)
    (hlt : ∀ i, i ≤ k → ws i < c.length - 1)
    (hchain : ∀ i, i < k → ws i ∈ coneOf c (ws (i + 1))) :
    (wireExits c (ws 0)).card
      + ∑ i ∈ Finset.range k,
          ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card
      ≤ coneExcess c (c.length - 1) + (k + 1) := by
  classical
  set E0 : Finset ℕ := (wireExits c (ws 0)).erase (ws 0) with hE0
  set D : ℕ → Finset ℕ := fun i =>
    ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).erase (ws (i + 1)) with hD
  have hE0M : E0 ⊆ ((coneOf c (c.length - 1)).erase (c.length - 1)).filter
      (fun u => 2 ≤ ((coneOf c (c.length - 1)).filter
        (fun q => u ∈ childrenOf c q)).card) :=
    exit_multiread f c hcomp hmin (ws 0) (hlt 0 (by omega))
  have hDM : ∀ i, i < k → D i ⊆ ((coneOf c (c.length - 1)).erase (c.length - 1)).filter
      (fun u => 2 ≤ ((coneOf c (c.length - 1)).filter
        (fun q => u ∈ childrenOf c q)).card) := by
    intro i hik u hu
    apply exit_multiread f c hcomp hmin (ws (i + 1)) (hlt (i + 1) (by omega))
    simp only [hD] at hu
    have h1 : u ≠ ws (i + 1) := Finset.ne_of_mem_erase hu
    have h2 := Finset.mem_of_mem_erase hu
    exact Finset.mem_erase.mpr ⟨h1, (Finset.mem_sdiff.mp h2).1⟩
  have hDcone : ∀ i, i < k → ∀ u ∈ D i,
      u ∈ coneOf c (ws (i + 1)) ∧ u ∉ coneOf c (ws i) := by
    intro i _ u hu
    simp only [hD] at hu
    have h2 := Finset.mem_of_mem_erase hu
    obtain ⟨h3, h4⟩ := Finset.mem_sdiff.mp h2
    exact ⟨(Finset.mem_filter.mp h3).1, h4⟩
  have hdisjD : ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k, i ≠ j →
      Disjoint (D i) (D j) := by
    intro i hi j hj hne
    rw [Finset.mem_range] at hi hj
    rcases Nat.lt_or_ge i j with hij | hij
    · apply Finset.disjoint_left.mpr
      intro u hui huj
      have h1 := (hDcone i hi u hui).1
      have h2 := (hDcone j hj u huj).2
      apply h2
      have hmono : ws (i + 1) ∈ coneOf c (ws j) :=
        chain_cone_mono c k ws hchain (i + 1) j (by omega) (by omega)
      exact cone_trans c (ws j) (ws (i + 1)) hmono u h1
    · have hij' : j < i := by omega
      apply Finset.disjoint_left.mpr
      intro u hui huj
      have h1 := (hDcone j hj u huj).1
      have h2 := (hDcone i hi u hui).2
      apply h2
      have hmono : ws (j + 1) ∈ coneOf c (ws i) :=
        chain_cone_mono c k ws hchain (j + 1) i (by omega) (by omega)
      exact cone_trans c (ws i) (ws (j + 1)) hmono u h1
  have hbi : ((Finset.range k).biUnion D).card = ∑ i ∈ Finset.range k, (D i).card :=
    Finset.card_biUnion hdisjD
  have hE0disj : Disjoint E0 ((Finset.range k).biUnion D) := by
    apply Finset.disjoint_left.mpr
    intro u hu0 hubi
    obtain ⟨j, hj, huj⟩ := Finset.mem_biUnion.mp hubi
    rw [Finset.mem_range] at hj
    have h1 : u ∈ coneOf c (ws 0) := by
      have h2 := Finset.mem_of_mem_erase (by simpa [hE0] using hu0)
      exact (Finset.mem_filter.mp h2).1
    have h2 := (hDcone j hj u huj).2
    apply h2
    have hmono : ws 0 ∈ coneOf c (ws j) :=
      chain_cone_mono c k ws hchain 0 j (by omega) (by omega)
    exact cone_trans c (ws j) (ws 0) hmono u h1
  have hunion_sub : E0 ∪ (Finset.range k).biUnion D
      ⊆ ((coneOf c (c.length - 1)).erase (c.length - 1)).filter
        (fun u => 2 ≤ ((coneOf c (c.length - 1)).filter
          (fun q => u ∈ childrenOf c q)).card) := by
    intro u hu
    rcases Finset.mem_union.mp hu with h | h
    · exact hE0M h
    · obtain ⟨j, hj, huj⟩ := Finset.mem_biUnion.mp h
      rw [Finset.mem_range] at hj
      exact hDM j hj huj
  have hcards : E0.card + ∑ i ∈ Finset.range k, (D i).card
      ≤ coneExcess c (c.length - 1) := by
    have h1 : (E0 ∪ (Finset.range k).biUnion D).card
        = E0.card + ((Finset.range k).biUnion D).card :=
      Finset.card_union_of_disjoint hE0disj
    have h2 := Finset.card_le_card hunion_sub
    have h3 := coneExcess_ge_multiReader c (c.length - 1)
    omega
  have hE0card : (wireExits c (ws 0)).card ≤ E0.card + 1 := by
    by_cases hmem : ws 0 ∈ wireExits c (ws 0)
    · rw [hE0, Finset.card_erase_of_mem hmem]
      have := Finset.card_pos.mpr ⟨ws 0, hmem⟩
      omega
    · rw [hE0, Finset.erase_eq_self.mpr hmem]
      omega
  have hDcard : ∀ i ∈ Finset.range k,
      ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card ≤ (D i).card + 1 := by
    intro i _
    simp only [hD]
    by_cases hmem : ws (i + 1) ∈ (wireExits c (ws (i + 1))) \ (coneOf c (ws i))
    · rw [Finset.card_erase_of_mem hmem]
      have := Finset.card_pos.mpr ⟨_, hmem⟩
      omega
    · rw [Finset.erase_eq_self.mpr hmem]
      omega
  have hsum1 : ∑ i ∈ Finset.range k,
      ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card
      ≤ ∑ i ∈ Finset.range k, ((D i).card + 1) := Finset.sum_le_sum hDcard
  have hsum2 : ∑ i ∈ Finset.range k, ((D i).card + 1)
      = (∑ i ∈ Finset.range k, (D i).card) + k := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_range]
  omega

/-! ### The exposed separation -/

set_option maxHeartbeats 1600000 in
/-- **The exposed separation (proved)**: equal exit VALUES (not an abstract trace) force equal
mixes at that wire's cut. -/
theorem exit_value_separation (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (w : ℕ) (hw : w < c.length - 1)
    (x y y' : Fin N → Bool)
    (hexit : ∀ p ∈ wireExits c w,
      (runFrom y [] c).getD p false = (runFrom y' [] c).getD p false) :
    sat3Family N (mixOn (varsOf c w)ᶜ x y)
      = sat3Family N (mixOn (varsOf c w)ᶜ x y') := by
  classical
  obtain ⟨opR, LL, RR, hroot, hLlt, hRlt, hLR⟩ :=
    sat3_root_shape N hv hm3 hk c hcomp hmin
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
    exact hexit p hp
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

/-! ### The k-scale capacity -/

set_option maxHeartbeats 1600000 in
/-- **THE k-SCALE CAPACITY (proved)**: any row family pairwise distinguished at SOME scale of
a nested chain is bounded by the inner exits plus the per-annulus NEW exits. -/
theorem sat3_chain_capacity (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (k : ℕ) (ws : ℕ → ℕ)
    (hlt : ∀ i, i ≤ k → ws i < c.length - 1)
    (hchain : ∀ i, i < k → ws i ∈ coneOf c (ws (i + 1)))
    (Y : Finset (Fin N → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ∃ i, i ≤ k ∧ ∃ x,
      sat3Family N (mixOn (varsOf c (ws i))ᶜ x y)
        ≠ sat3Family N (mixOn (varsOf c (ws i))ᶜ x y')) :
    Y.card ≤ 2 ^ ((wireExits c (ws 0)).card
      + ∑ i ∈ Finset.range k,
          ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card) := by
  classical
  set U : Finset ℕ := (Finset.range (k + 1)).biUnion (fun i => wireExits c (ws i))
    with hU
  set Φ : (Fin N → Bool) → (↥U → Bool) := fun y u =>
    (runFrom y [] c).getD u.val false with hΦ
  have hinj : Set.InjOn Φ ↑Y := by
    intro y hy y' hy' heq
    by_contra hne
    obtain ⟨i, hik, x, hx⟩ := hdist y (Finset.mem_coe.mp hy) y'
      (Finset.mem_coe.mp hy') hne
    apply hx
    apply exit_value_separation N hv hm3 hk c hcomp hmin (ws i) (hlt i hik) x y y'
    intro p hp
    have hpU : p ∈ U := by
      rw [hU]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), hp⟩
    exact congrFun heq ⟨p, hpU⟩
  have hYle : Y.card ≤ 2 ^ U.card := by
    have hmaps : ∀ y ∈ Y, Φ y ∈ (Finset.univ : Finset (↥U → Bool)) :=
      fun y _ => Finset.mem_univ _
    have hcard := Finset.card_le_card_of_injOn Φ hmaps hinj
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe] at hcard
    exact hcard
  have hUcard := chain_union_card c k ws hchain
  calc Y.card ≤ 2 ^ U.card := hYle
    _ ≤ 2 ^ ((wireExits c (ws 0)).card
        + ∑ i ∈ Finset.range k,
            ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card) :=
      Nat.pow_le_pow_right (by omega) hUcard

/-- **THE HEADLINE (proved)**: `k+1` nested scales cost the adversary `coneExcess + k + 1`
trace bits TOTAL — the additive form of the cut capacity. -/
theorem sat3_chain_capacity_excess (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (k : ℕ) (ws : ℕ → ℕ)
    (hlt : ∀ i, i ≤ k → ws i < c.length - 1)
    (hchain : ∀ i, i < k → ws i ∈ coneOf c (ws (i + 1)))
    (Y : Finset (Fin N → Bool))
    (hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ∃ i, i ≤ k ∧ ∃ x,
      sat3Family N (mixOn (varsOf c (ws i))ᶜ x y)
        ≠ sat3Family N (mixOn (varsOf c (ws i))ᶜ x y')) :
    Y.card ≤ 2 ^ (coneExcess c (c.length - 1) + (k + 1)) := by
  calc Y.card
      ≤ 2 ^ ((wireExits c (ws 0)).card
        + ∑ i ∈ Finset.range k,
            ((wireExits c (ws (i + 1))) \ (coneOf c (ws i))).card) :=
        sat3_chain_capacity N hv hm3 hk c hcomp hmin k ws hlt hchain Y hdist
    _ ≤ 2 ^ (coneExcess c (c.length - 1) + (k + 1)) :=
        Nat.pow_le_pow_right (by omega)
          (chain_exit_ledger (sat3Family N) c hcomp hmin k ws hlt hchain)

/-! ### The chain supply -/

/-- **The chain supply (proved)**: nested chains exist at any prescribed increasing bands —
recurse `balanced_wire_exists` inside the previous wire's cone. -/
theorem balanced_chain_exists {n : ℕ} (c : List (CGate n)) (r : ℕ) (k : ℕ) (T : ℕ → ℕ)
    (hT2 : ∀ i, i ≤ k → 2 ≤ T i)
    (hTmono : ∀ i, i < k → T i ≤ T (i + 1))
    (hTr : T k ≤ (varsOf c r).card) :
    ∃ ws : ℕ → ℕ,
      (∀ i, i ≤ k → ws i ∈ coneOf c r
        ∧ T i ≤ (varsOf c (ws i)).card
        ∧ (varsOf c (ws i)).card ≤ 2 * T i - 2)
      ∧ (∀ i, i < k → ws i ∈ coneOf c (ws (i + 1))) := by
  classical
  induction k generalizing r with
  | zero =>
    obtain ⟨w, hwcone, hw1, hw2⟩ :=
      balanced_wire_exists c r (T 0) (hT2 0 le_rfl) hTr
    refine ⟨fun _ => w, ?_, ?_⟩
    · intro i hi
      show w ∈ coneOf c r ∧ T i ≤ (varsOf c w).card
        ∧ (varsOf c w).card ≤ 2 * T i - 2
      have h0 : i = 0 := by omega
      rw [h0]
      exact ⟨hwcone, hw1, hw2⟩
    · intro i hi
      exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    obtain ⟨w, hwcone, hw1, hw2⟩ :=
      balanced_wire_exists c r (T (k + 1)) (hT2 (k + 1) le_rfl) hTr
    obtain ⟨ws', hband', hchain'⟩ := ih (r := w)
      (fun i hi => hT2 i (by omega))
      (fun i hi => hTmono i (by omega))
      (by have := hTmono k (by omega); omega)
    refine ⟨fun i => if i = k + 1 then w else ws' i, ?_, ?_⟩
    · intro i hik
      show (if i = k + 1 then w else ws' i) ∈ coneOf c r
        ∧ T i ≤ (varsOf c (if i = k + 1 then w else ws' i)).card
        ∧ (varsOf c (if i = k + 1 then w else ws' i)).card ≤ 2 * T i - 2
      by_cases hi : i = k + 1
      · rw [if_pos hi, hi]
        exact ⟨hwcone, hw1, hw2⟩
      · rw [if_neg hi]
        obtain ⟨hc, h1, h2⟩ := hband' i (by omega)
        exact ⟨cone_trans c r w hwcone (ws' i) hc, h1, h2⟩
    · intro i hik
      show (if i = k + 1 then w else ws' i) ∈ coneOf c
        (if i + 1 = k + 1 then w else ws' (i + 1))
      by_cases hi : i + 1 = k + 1
      · rw [if_pos hi, if_neg (show ¬ i = k + 1 by omega)]
        have h0 : i = k := by omega
        rw [h0]
        exact (hband' k le_rfl).1
      · rw [if_neg (show ¬ i = k + 1 by omega), if_neg hi]
        exact hchain' i (by omega)

/-- Stepwise threshold monotonicity accumulates to the top index. -/
theorem chain_T_mono (T : ℕ → ℕ) :
    ∀ k, (∀ i, i < k → T i ≤ T (i + 1)) → ∀ i, i ≤ k → T i ≤ T k := by
  intro k
  induction k with
  | zero =>
    intro _ i hik
    have h0 : i = 0 := by omega
    subst h0
    exact le_rfl
  | succ k' ih =>
    intro hmono i hik
    rcases Nat.lt_or_eq_of_le hik with h | h
    · have h1 := ih (fun j hj => hmono j (by omega)) i (by omega)
      have h2 := hmono k' (by omega)
      omega
    · subst h
      exact le_rfl

set_option maxHeartbeats 1600000 in
/-- **THE COMPOSITE (proved)**: for every minimal SAT circuit and prescribed increasing bands
below the root, a nested chain exists at those bands, and every row family pairwise
distinguished at some scale of it is capped at `2^{coneExcess + k + 1}`. -/
theorem sat3_annulus_capacity (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (k : ℕ) (T : ℕ → ℕ)
    (hT2 : ∀ i, i ≤ k → 2 ≤ T i)
    (hTmono : ∀ i, i < k → T i ≤ T (i + 1))
    (hTtop : 2 * T k - 2 < (varsOf c (c.length - 1)).card)
    (hTr : T k ≤ (varsOf c (c.length - 1)).card) :
    ∃ ws : ℕ → ℕ,
      (∀ i, i ≤ k → ws i < c.length - 1
        ∧ T i ≤ (varsOf c (ws i)).card
        ∧ (varsOf c (ws i)).card ≤ 2 * T i - 2)
      ∧ (∀ i, i < k → ws i ∈ coneOf c (ws (i + 1)))
      ∧ ∀ Y : Finset (Fin N → Bool),
          (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → ∃ i, i ≤ k ∧ ∃ x,
            sat3Family N (mixOn (varsOf c (ws i))ᶜ x y)
              ≠ sat3Family N (mixOn (varsOf c (ws i))ᶜ x y')) →
          Y.card ≤ 2 ^ (coneExcess c (c.length - 1) + (k + 1)) := by
  classical
  obtain ⟨ws, hband, hchain⟩ :=
    balanced_chain_exists c (c.length - 1) k T hT2 hTmono hTr
  have hlt : ∀ i, i ≤ k → ws i < c.length - 1 := by
    intro i hik
    obtain ⟨hcone, h1, h2⟩ := hband i hik
    have hle : ws i ≤ c.length - 1 := cone_le c (c.length - 1) (ws i) hcone
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      rw [h] at h2
      have hmono : T i ≤ T k := chain_T_mono T k hTmono i hik
      omega
  refine ⟨ws, fun i hik => ⟨hlt i hik, (hband i hik).2.1, (hband i hik).2.2⟩,
    hchain, ?_⟩
  intro Y hdist
  exact sat3_chain_capacity_excess N hv hm3 hk c hcomp hmin k ws hlt hchain Y hdist

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.wireExits_nested
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chain_exit_ledger
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_chain_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_chain_capacity_excess
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.balanced_chain_exists
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_annulus_capacity
