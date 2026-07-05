import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameGeneralizedPins

/-!
# N-Frame: the min-form bound — every block starves one side of the matching

The quantitative cash-out of the generalized pins.  Since the variable assignment `α` is free, a
cut with `j`-bit trace cannot afford **any** matching of `j + 1` in-`S` pin signs to `j + 1`
off-`S` selectors — so for every block, one of the two sides is small.

  `exists_injection_mapping` — **PROVED, the matching extension**: equal-size subsets of `Fin k`
        and `Fin v` (`k ≤ v`) extend to a total injection carrying one into the other.
  `sat3_pin_selector_min_bound` — **PROVED, the min form**: for any cut factorization of SAT over
        `S` with a `j`-bit trace and any block `c`:
        `#{pins with pin sign ∈ S} ≤ j` **or** `#{variables with slot-0 selector of c ∉ S} ≤ j`.
  `sat3_circuit_pin_selector_bound` — **PROVED, the circuit cash-out**: every minimal SAT circuit
        admits, at every threshold band, a balanced coordinate set `S` such that **every** block
        has few pin signs inside `S` or few slot-0 selectors outside `S` — priced in
        `coneExcess + 1`.

## Honest scope

The balanced-cut endgame ledger after this rung: the all-selectors-in refuge is dead on size
grounds, and the signs-in/selectors-out tension is priced by cone excess for every block at once.
The remaining refuge is **all signs out of `S`** (then the min bound is satisfied vacuously on the
sign side), whose reading requires the selector-data families — contexts whose distinguishing data
is selector patterns rather than pin signs — the last named workhorse gap.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE MATCHING EXTENSION (proved)**: equal-size subsets of `Fin k` and `Fin v` extend to a
total injection carrying one into the other. -/
theorem exists_injection_mapping {k v : ℕ} (hkv : k ≤ v)
    (P : Finset (Fin k)) (V : Finset (Fin v)) (hcard : P.card = V.card) :
    ∃ α : Fin k → Fin v, Function.Injective α ∧ ∀ p ∈ P, α p ∈ V := by
  classical
  have hPle : P.card ≤ k := by
    have := Finset.card_le_card (Finset.subset_univ P)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hVle : V.card ≤ v := by
    have := Finset.card_le_card (Finset.subset_univ V)
    rwa [Finset.card_univ, Fintype.card_fin] at this
  have hle : (Pᶜ : Finset (Fin k)).card ≤ (Vᶜ : Finset (Fin v)).card := by
    rw [Finset.card_compl, Finset.card_compl, Fintype.card_fin, Fintype.card_fin]
    omega
  set β : ↥P ≃ ↥V := P.equivFin.trans ((finCongr hcard).trans V.equivFin.symm)
    with hβ
  set γ : ↥(Pᶜ : Finset (Fin k)) → ↥(Vᶜ : Finset (Fin v)) :=
    fun x => (Vᶜ : Finset (Fin v)).equivFin.symm
      (Fin.castLE hle ((Pᶜ : Finset (Fin k)).equivFin x)) with hγ
  have hγinj : Function.Injective γ := by
    intro x y hxy
    have h1 := (Vᶜ : Finset (Fin v)).equivFin.symm.injective hxy
    have h2 := Fin.castLE_injective hle h1
    exact (Pᶜ : Finset (Fin k)).equivFin.injective h2
  refine ⟨fun p => if hp : p ∈ P then (β ⟨p, hp⟩).val
    else (γ ⟨p, Finset.mem_compl.mpr hp⟩).val, ?_, ?_⟩
  · intro a b hab
    have hab' : (if hp : a ∈ P then (β ⟨a, hp⟩).val
        else (γ ⟨a, Finset.mem_compl.mpr hp⟩).val)
      = (if hp : b ∈ P then (β ⟨b, hp⟩).val
        else (γ ⟨b, Finset.mem_compl.mpr hp⟩).val) := hab
    by_cases ha : a ∈ P <;> by_cases hb : b ∈ P
    · rw [dif_pos ha, dif_pos hb] at hab'
      have h := β.injective (Subtype.ext hab')
      exact congrArg Subtype.val h
    · exfalso
      rw [dif_pos ha, dif_neg hb] at hab'
      have h1 : (β ⟨a, ha⟩).val ∈ V := (β ⟨a, ha⟩).2
      have h2 : (γ ⟨b, Finset.mem_compl.mpr hb⟩).val ∈ (Vᶜ : Finset (Fin v)) :=
        (γ ⟨b, Finset.mem_compl.mpr hb⟩).2
      rw [hab'] at h1
      exact (Finset.mem_compl.mp h2) h1
    · exfalso
      rw [dif_neg ha, dif_pos hb] at hab'
      have h1 : (β ⟨b, hb⟩).val ∈ V := (β ⟨b, hb⟩).2
      have h2 : (γ ⟨a, Finset.mem_compl.mpr ha⟩).val ∈ (Vᶜ : Finset (Fin v)) :=
        (γ ⟨a, Finset.mem_compl.mpr ha⟩).2
      rw [← hab'] at h1
      exact (Finset.mem_compl.mp h2) h1
    · rw [dif_neg ha, dif_neg hb] at hab'
      have h := hγinj (Subtype.ext hab')
      exact congrArg Subtype.val h
  · intro p hp
    show (if hp' : p ∈ P then (β ⟨p, hp'⟩).val
      else (γ ⟨p, Finset.mem_compl.mpr hp'⟩).val) ∈ V
    rw [dif_pos hp]
    exact (β ⟨p, hp⟩).2

/-- **THE MIN FORM (proved)**: over any cut factorization of SAT, every block has at most `j` pin
signs inside `S`, or at most `j` slot-0 selectors outside `S`. -/
theorem sat3_pin_selector_min_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    {S : Finset (Fin N)} {j : ℕ}
    (hcut : CutFactorization (sat3Family N) S j)
    (c : Fin (sat3M N)) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S)).card ≤ j
    ∨ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∉ S)).card ≤ j := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨hP, hV⟩ := hcon
  obtain ⟨P', hP'sub, hP'card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S)) (n := j + 1) (by omega)
  obtain ⟨V', hV'sub, hV'card⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
      sat3Bit N c ⟨0, by omega⟩ w.val
        (by have := w.isLt; omega) ∉ S)) (n := j + 1) (by omega)
  obtain ⟨α, hαinj, hαmap⟩ := exists_injection_mapping hkv P' V'
    (by rw [hP'card, hV'card])
  have hdrag := sat3_generalized_pin_drag N hv hk hcut c α hαinj
  have hsub : P' ⊆ (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ∧
      sat3Bit N c ⟨0, by omega⟩ (α p).val
        (by have := (α p).isLt; omega) ∉ S) := by
    intro p hp
    have hπ := (Finset.mem_filter.mp (hP'sub hp)).2
    have hsel := (Finset.mem_filter.mp (hV'sub (hαmap p hp))).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hπ, hsel⟩
  have hge := Finset.card_le_card hsub
  omega

/-- **THE CIRCUIT CASH-OUT (proved)**: every minimal SAT circuit admits, at every threshold band, a
balanced coordinate set `S` such that every block has few pin signs inside `S` or few slot-0
selectors outside `S` — priced in `coneExcess + 1`. -/
theorem sat3_circuit_pin_selector_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf cc (cc.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2 ∧
      ∀ cb : Fin (sat3M N),
        ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
          sat3Bit N (sat3PinClause N cb hk p) ⟨0, by omega⟩ (sat3V N)
            (by omega) ∈ S)).card ≤ coneExcess cc (cc.length - 1) + 1
        ∨ ((Finset.univ : Finset (Fin (sat3V N))).filter (fun w =>
          sat3Bit N cb ⟨0, by omega⟩ w.val
            (by have := w.isLt; omega) ∉ S)).card
          ≤ coneExcess cc (cc.length - 1) + 1 := by
  obtain ⟨S, h1, h2, j, hj, hcut⟩ :=
    sat3_balanced_cut N hv hm3 hk cc hcomp hmin T hT hband
  refine ⟨S, h1, h2, fun cb => ?_⟩
  rcases sat3_pin_selector_min_bound N hv hk hcut cb with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.exists_injection_mapping
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_pin_selector_min_bound
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_circuit_pin_selector_bound
