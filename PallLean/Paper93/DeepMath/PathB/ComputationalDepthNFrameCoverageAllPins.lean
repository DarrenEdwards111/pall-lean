import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameOddSquareAllPins

/-!
# N-Frame: widened coverage — every sign pair kills, the residual thins to full alignment

The assembly over the all-pins squares.

  `sat3_split_killed_of_sign_separation_all` — **PROVED**: any bipartite split whose cut separates the
        pin-sign of **any** `(cIdx, j₀)` from that block's designated sign is refuted, both orientations —
        `(m−2)·m` killable pairs.
  `Sat3AllPinsAlignedNoSplit` — the **thinned residual** (NOT discharged): refutation demanded only for
        proper cuts aligning **all** `(m−2)·m` sign pairs at once.
  `sat3_no_split_of_all_pins_aligned` / `sat3_cbudget_2mD_of_all_pins_aligned` — the reduction and the
        conditional record: thinned residual ⇒ `2·m·D ≤ cbudget`.

## Honest scope

Surviving cuts must now agree, for every block and every pinned variable, about the whole sign layer —
all `2m` designated-sign bits and all `(m−2)·m` pin-sign bits move in one aligned mass.  The hard tail is
unchanged and named: the selector-heavy fully-aligned cut, where monotonicity forbids XOR-squares and the
rectangle-closure route is required.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE WIDENED KILL (proved)**: separation of any `(cIdx, j₀)` sign pair refutes the split. -/
theorem sat3_split_killed_of_sign_separation_all (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (hsep : (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ∧ sat3SignBit N cIdx ∉ S)
      ∨ (sat3SignBit N cIdx ∈ S ∧ sat3Bit N (sat3PinClause N cIdx hk j₀)
        ⟨0, by omega⟩ (sat3V N) (by omega) ∉ S)) : False := by
  classical
  obtain ⟨u, hu, hus, hut, hust⟩ :=
    sat3_xor_square_all_pins N hv hm3 hk cIdx j₀ (fun _ => false)
  obtain ⟨w, hodd⟩ :=
    sat3_odd_square_all_pins N hv hm3 hk cIdx j₀ (fun _ => false)
  have hne : (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
      (sat3V N) (by omega) : Fin N) ≠ sat3SignBit N cIdx :=
    sat3Bit_ne_of_clause N _ _ _ _
      (fun h' => sat3PinClause_ne N cIdx hk j₀ h')
  rcases hsep with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · exact two_squares_kill_split (sat3Family N) S op g h hg hh hf
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      (sat3SignBit N cIdx) hp hq hne u w false hu hus hut hust hodd
  · have hust' : sat3Family N (Function.update (Function.update u
        (sat3SignBit N cIdx) (!(u (sat3SignBit N cIdx))))
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
        (!(u (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
          (sat3V N) (by omega))))) = false := by
      rw [show Function.update (Function.update u
          (sat3SignBit N cIdx) (!(u (sat3SignBit N cIdx))))
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(u (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega))))
        = Function.update (Function.update u
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(u (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega)))))
          (sat3SignBit N cIdx) (!(u (sat3SignBit N cIdx))) from
        Function.update_comm hne.symm _ _ _]
      exact hust
    have hodd' : xor (xor (sat3Family N w)
        (sat3Family N (Function.update w (sat3SignBit N cIdx)
          (!(w (sat3SignBit N cIdx))))))
        (xor (sat3Family N (Function.update w
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega))))))
          (sat3Family N (Function.update (Function.update w
            (sat3SignBit N cIdx) (!(w (sat3SignBit N cIdx))))
            (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
              (by omega))
            (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
              (sat3V N) (by omega))))))) = true := by
      rw [show Function.update (Function.update w
          (sat3SignBit N cIdx) (!(w (sat3SignBit N cIdx))))
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega))))
        = Function.update (Function.update w
          (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
          (!(w (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
            (sat3V N) (by omega)))))
          (sat3SignBit N cIdx) (!(w (sat3SignBit N cIdx))) from
        Function.update_comm hne.symm _ _ _]
      rw [xor_shuffle]
      exact hodd
    exact two_squares_kill_split (sat3Family N) S op g h hg hh hf
      (sat3SignBit N cIdx)
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
      hq hp hne.symm u w false hu hut hus hust' hodd'

/-- The **thinned residual** (NOT discharged): only cuts aligning all `(m−2)·m` sign pairs remain. -/
def Sat3AllPinsAlignedNoSplit (N : ℕ) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) : Prop :=
  ∀ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
    (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) →
    (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) →
    (∀ x, sat3Family N x = op (g x) (h x)) →
    (∃ s₀ : Fin N, s₀ ∈ S) → (∃ t₀ : Fin N, t₀ ∉ S) →
    (∀ (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)),
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ↔ sat3SignBit N cIdx ∈ S)) → False

/-- **THE REDUCTION (proved)**: killing fully-aligned cuts suffices. -/
theorem sat3_no_split_of_all_pins_aligned (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3AllPinsAlignedNoSplit N hm3 hk) :
    Sat3NoBipartiteSplitProper N := by
  intro op g h S hg hh hf hs ht
  classical
  by_cases hal : ∀ (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2)),
      (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ↔ sat3SignBit N cIdx ∈ S)
  · exact hW op g h S hg hh hf hs ht hal
  · push_neg at hal
    obtain ⟨cIdx, j₀, hciff⟩ := hal
    rcases hciff with hc | ⟨hp, hq⟩
    · exact sat3_split_killed_of_sign_separation_all N hv hm3 hk op g h S hg hh hf
        cIdx j₀ (Or.inl hc)
    · exact sat3_split_killed_of_sign_separation_all N hv hm3 hk op g h S hg hh hf
        cIdx j₀ (Or.inr ⟨hq, hp⟩)

/-- **THE CONDITIONAL RECORD (hypothesis named, not claimed)**: thinned residual ⇒ `2·m·D ≤ cbudget`. -/
theorem sat3_cbudget_2mD_of_all_pins_aligned (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (hW : Sat3AllPinsAlignedNoSplit N hm3 hk) :
    2 * (sat3M N * sat3D N) ≤ cbudget (sat3Family N) :=
  sat3_cbudget_2mD_of_no_proper_split N hv hm3 hk
    (sat3_no_split_of_all_pins_aligned N hv hm3 hk hW)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_split_killed_of_sign_separation_all
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_2mD_of_all_pins_aligned
