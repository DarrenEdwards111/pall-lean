import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiBlockPingPong

/-!
# N-Frame: the alignment toolkit — the restricted census and column extraction

Rung 11 of the multi-block arc (… → circuit side → ping-pong → **alignment**).  Rung 7 proved
that pairwise structure cannot force a large rectangle in an arbitrary cut, so the extraction
must be built from finer instruments.  This file provides them — the deterministic column
toolkit that reduces the alignment question to its final optimization form:

  `sat3_multi_window_restricted` — **PROVED, the restricted census**: for ANY position window
        `W` with pool room and `C × W` cleanliness,
        `Σ_{c ∈ C} |In₀(c) ∩ W| ≤ j`.
        Subsumes the rectangle census (the case `W ⊆ In₀(c)` for all `c`) and prices ARBITRARY
        window mass, aligned or not.
  `sat3_multi_column_census` — **PROVED, the column census**: a single position `w` that is
        `C`-clean costs one pin — and then its whole column is priced: `deg₀(w, C) ≤ j`.
        Unpoisoned columns are thin, at every band, unconditionally.
  `sat3_multi_column_double_count` — window mass equals summed column masses.
  `sat3_multi_heavy_columns_few` — **PROVED, the extraction bound**: if every column of `W` has
        `C`-mass at least `θ` (and `W` has room), then `|W| · θ ≤ j` — heavy clean columns are
        FEW.  Contrapositive: to certify `j ≥ K` it suffices to exhibit an admissible window of
        columns with total mass `K` — no rectangle alignment needed, column masses add.

## Honest scope — the alignment question in final form

The drag reaches `j = Ω(N)` iff some admissible pair `(C, W)` — `C × W` slot-1-clean,
`|W| + Q_C ≤ m − |C|` — carries total column mass `Ω(N)`.  The two walls are now exact:
(1) POSITION POISON, `m`-amplified: one slot-1 bit at `(c₀, w)` forces `c₀ ∉ C` or `w ∉ W`;
keeping `w` costs a block, keeping `c₀` costs a column of up to `m` payload bits.
(2) THE POOL CAP: `|W| ≤ m − |C| − Q_C` — a window position costs a pin block.
At the optimum `|C|, |W| = Θ(m)` the mass potential is `Θ(m²) = Θ(N)`; whether a MINIMAL
circuit's balanced cut must leave such a window admissible — equivalently, whether its poison
pattern can simultaneously thin every admissible window — is the remaining open combinatorics.
(A probabilistic refinement — averaging over random `W` of size `k` prices a `k/v` fraction of
all unpoisoned mass — is not formalized here.)  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The restricted census -/

set_option maxHeartbeats 800000 in
/-- **THE RESTRICTED CENSUS (proved)**: any position window `W` with pool room and `C × W`
cleanliness has its total inside mass priced: `Σ_{c ∈ C} |In₀(c) ∩ W| ≤ j`. -/
theorem sat3_multi_window_restricted (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N))) (W : Finset (Fin (sat3V N)))
    (hcleanW : ∀ c ∈ C, ∀ w ∈ W,
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hpool : W.card + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    ∑ c ∈ C, (W.filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ j := by
  classical
  have hroom : (C.biUnion (fun c => W.filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
      + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card := by
    have hbu : (C.biUnion (fun c => W.filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))).card
        ≤ W.card :=
      Finset.card_le_card (Finset.biUnion_subset.mpr
        (fun c _ => Finset.filter_subset _ W))
    omega
  exact sat3_multi_window N hv hcut C
    (fun c => W.filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S))
    (fun c hc w hw => (Finset.mem_filter.mp hw).2)
    (fun c hc c' hc' w hw => hcleanW c hc w (Finset.mem_filter.mp hw).1)
    hkv hroom

/-! ### The column census -/

set_option maxHeartbeats 800000 in
/-- **THE COLUMN CENSUS (proved)**: a `C`-clean position costs one pin, and its whole column is
priced — `deg₀(w, C) ≤ j`.  Unpoisoned columns are thin. -/
theorem sat3_multi_column_census (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N))) (w : Fin (sat3V N))
    (hcleanw : ∀ c ∈ C,
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hpool : 1 + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card) :
    (C.filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card ≤ j := by
  classical
  have hres := sat3_multi_window_restricted N hv hcut C {w}
    (fun c hc w' hw' => by
      rw [Finset.mem_singleton] at hw'
      rw [hw']
      exact hcleanw c hc)
    hkv
    (by rw [Finset.card_singleton]; exact hpool)
  have htrans : ∑ c ∈ C, (({w} : Finset (Fin (sat3V N))).filter (fun w' =>
      sat3Bit N c ⟨0, by omega⟩ w'.val (by have := w'.isLt; omega) ∈ S)).card
      = (C.filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.filter_singleton]
    by_cases h : sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
    · rw [if_pos h, if_pos h, Finset.card_singleton]
    · rw [if_neg h, if_neg h, Finset.card_empty]
  omega

/-! ### The column double count -/

/-- Window mass equals summed column masses. -/
theorem sat3_multi_column_double_count (N : ℕ) (S : Finset (Fin N))
    (C : Finset (Fin (sat3M N))) (W : Finset (Fin (sat3V N))) :
    ∑ c ∈ C, (W.filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
    = ∑ w ∈ W, (C.filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card := by
  classical
  calc ∑ c ∈ C, (W.filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card
      = ∑ c ∈ C, ∑ w ∈ W,
        if sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        then 1 else 0 :=
        Finset.sum_congr rfl (fun c _ => by rw [Finset.card_filter])
    _ = ∑ w ∈ W, ∑ c ∈ C,
        if sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S
        then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ w ∈ W, (C.filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
        Finset.sum_congr rfl (fun w _ => by rw [Finset.card_filter])

/-! ### The extraction bound -/

set_option maxHeartbeats 800000 in
/-- **THE EXTRACTION BOUND (proved)**: heavy clean columns are few — if every column of an
admissible window `W` has `C`-mass at least `θ`, then `|W| · θ ≤ j`.  Contrapositive: any
admissible window of total column mass `K` certifies `j ≥ K`; column masses ADD, no rectangle
alignment required. -/
theorem sat3_multi_heavy_columns_few (N : ℕ) (hv : 1 ≤ sat3V N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (C : Finset (Fin (sat3M N))) (W : Finset (Fin (sat3V N))) (θ : ℕ)
    (hcleanW : ∀ c ∈ C, ∀ w ∈ W,
      sat3Bit N c ⟨1, by omega⟩ w.val (by have := w.isLt; omega) ∉ S)
    (hkv : sat3M N - C.card ≤ sat3V N)
    (hpool : W.card + ((((Finset.univ : Finset (Fin (sat3M N))) \ C)).filter (fun b =>
        sat3Bit N b ⟨0, by omega⟩ (sat3V N) (by omega) ∈ S)).card
      ≤ sat3M N - C.card)
    (hheavy : ∀ w ∈ W, θ ≤ (C.filter (fun c =>
      sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card) :
    W.card * θ ≤ j := by
  classical
  have hres := sat3_multi_window_restricted N hv hcut C W hcleanW hkv hpool
  have hdc := sat3_multi_column_double_count N S C W
  calc W.card * θ = ∑ _w ∈ W, θ := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ w ∈ W, (C.filter (fun c =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
        Finset.sum_le_sum hheavy
    _ = ∑ c ∈ C, (W.filter (fun w =>
        sat3Bit N c ⟨0, by omega⟩ w.val (by have := w.isLt; omega) ∈ S)).card :=
        hdc.symm
    _ ≤ j := hres

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_window_restricted
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_column_census
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_column_double_count
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_multi_heavy_columns_few
