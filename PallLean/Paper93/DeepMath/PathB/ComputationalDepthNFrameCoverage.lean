import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameOddSquare

/-!
# N-Frame: the coverage core — sign-separating cuts die; the residual is named

Track A, rung 3, at its provable core.  With both squares produced, `two_squares_kill_split` closes every
proper cut that separates a block's pin-sign bit from its designated sign bit — in **either** orientation.

  `sat3_split_killed_of_sign_separation` — **PROVED, the coverage core**: any bipartite split of SAT whose
        cut separates `pinSign(cIdx)` from `signBit(cIdx)` for some block is refuted — eight canonical
        evaluations, both orientations handled (the reversed orientation needs only an update-commutation
        and an xor-shuffle).
  `Sat3SignAlignedNoSplit` — the **named residual** (NOT discharged): refutation demanded only for proper
        cuts that keep every block's (pin-sign, designated-sign) pair together.
  `sat3_no_split_of_sign_aligned` — **PROVED, the reduction**: residual ⇒ `Sat3NoBipartiteSplitProper`.
  `sat3_cbudget_2mD_of_sign_aligned` — **the conditional record**: residual ⇒ `2·m·D ≤ cbudget`.

## Honest scope

The kill-class is now large — any cut disagreeing about a single block's sign pair dies — but the residual
is real: sign-aligned cuts, where all `2m` sign coordinates travel in aligned pairs.  Shrinking it further
needs squares for more pairs (vary the pinned variable `j₀` and the probe target, which the identification
lemma already supports generically), and the genuinely hard tail is the selector-heavy sign-aligned cut,
where monotonicity forbids XOR-squares and the rectangle-closure route is required.  Named, not claimed.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

theorem xor_shuffle (a b c d : Bool) :
    xor (xor a c) (xor b d) = xor (xor a b) (xor c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- **THE COVERAGE CORE (proved)**: a split whose cut separates some block's pin-sign from its designated
sign is refuted, in either orientation. -/
theorem sat3_split_killed_of_sign_separation (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N))
    (hg : ∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y)
    (hh : ∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y)
    (hf : ∀ x, sat3Family N x = op (g x) (h x))
    (cIdx : Fin (sat3M N))
    (hsep : (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ∧ sat3SignBit N cIdx ∉ S)
      ∨ (sat3SignBit N cIdx ∈ S ∧ sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩)
        ⟨0, by omega⟩ (sat3V N) (by omega) ∉ S)) : False := by
  classical
  obtain ⟨u, hu, hus, hut, hust⟩ :=
    sat3_xor_square_pinSign_designatedSign N hv hm3 hk cIdx (fun _ => false)
  obtain ⟨w, hodd⟩ :=
    sat3_odd_square_pinSign_designatedSign N hv hm3 hk cIdx (fun _ => false)
  have hne : (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
      (sat3V N) (by omega) : Fin N) ≠ sat3SignBit N cIdx :=
    sat3Bit_ne_of_clause N _ _ _ _
      (fun h' => sat3PinClause_ne N cIdx hk ⟨0, by omega⟩ h')
  rcases hsep with ⟨hp, hq⟩ | ⟨hq, hp⟩
  · -- s₀ := pin-sign, t₀ := designated sign: the squares are in engine format verbatim
    exact two_squares_kill_split (sat3Family N) S op g h hg hh hf
      (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
        (by omega))
      (sat3SignBit N cIdx) hp hq hne u w false hu hus hut hust hodd
  · -- s₀ := designated sign, t₀ := pin-sign: commute the double update, shuffle the parity
    have hust' : sat3Family N (Function.update (Function.update u
        (sat3SignBit N cIdx) (!(u (sat3SignBit N cIdx))))
        (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
          (by omega))
        (!(u (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
          (sat3V N) (by omega))))) = false := by
      rw [show Function.update (Function.update u
          (sat3SignBit N cIdx) (!(u (sat3SignBit N cIdx))))
          (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
            (by omega))
          (!(u (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
            (sat3V N) (by omega))))
        = Function.update (Function.update u
          (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
            (by omega))
          (!(u (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
            (sat3V N) (by omega)))))
          (sat3SignBit N cIdx) (!(u (sat3SignBit N cIdx))) from
        Function.update_comm hne.symm _ _ _]
      exact hust
    have hodd' : xor (xor (sat3Family N w)
        (sat3Family N (Function.update w (sat3SignBit N cIdx)
          (!(w (sat3SignBit N cIdx))))))
        (xor (sat3Family N (Function.update w
          (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
            (by omega))
          (!(w (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
            (sat3V N) (by omega))))))
          (sat3Family N (Function.update (Function.update w
            (sat3SignBit N cIdx) (!(w (sat3SignBit N cIdx))))
            (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
              (by omega))
            (!(w (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
              (sat3V N) (by omega))))))) = true := by
      rw [show Function.update (Function.update w
          (sat3SignBit N cIdx) (!(w (sat3SignBit N cIdx))))
          (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
            (by omega))
          (!(w (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
            (sat3V N) (by omega))))
        = Function.update (Function.update w
          (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
            (by omega))
          (!(w (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
            (sat3V N) (by omega)))))
          (sat3SignBit N cIdx) (!(w (sat3SignBit N cIdx))) from
        Function.update_comm hne.symm _ _ _]
      rw [xor_shuffle]
      exact hodd
    exact two_squares_kill_split (sat3Family N) S op g h hg hh hf
      (sat3SignBit N cIdx)
      (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
        (by omega))
      hq hp hne.symm u w false hu hut hus hust' hodd'

/-- The **named residual** (NOT discharged): refutation demanded only for proper cuts keeping every
block's (pin-sign, designated-sign) pair together. -/
def Sat3SignAlignedNoSplit (N : ℕ) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) : Prop :=
  ∀ (op : Bool → Bool → Bool) (g h : (Fin N → Bool) → Bool) (S : Finset (Fin N)),
    (∀ x y : Fin N → Bool, (∀ i, i ∈ S → x i = y i) → g x = g y) →
    (∀ x y : Fin N → Bool, (∀ i, i ∉ S → x i = y i) → h x = h y) →
    (∀ x, sat3Family N x = op (g x) (h x)) →
    (∃ s₀ : Fin N, s₀ ∈ S) → (∃ t₀ : Fin N, t₀ ∉ S) →
    (∀ cIdx : Fin (sat3M N),
      (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ↔ sat3SignBit N cIdx ∈ S)) → False

/-- **THE REDUCTION (proved)**: killing sign-aligned cuts suffices for the full no-split hypothesis. -/
theorem sat3_no_split_of_sign_aligned (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hW : Sat3SignAlignedNoSplit N hm3 hk) :
    Sat3NoBipartiteSplitProper N := by
  intro op g h S hg hh hf hs ht
  classical
  by_cases hal : ∀ cIdx : Fin (sat3M N),
      (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∈ S ↔ sat3SignBit N cIdx ∈ S)
  · exact hW op g h S hg hh hf hs ht hal
  · push_neg at hal
    obtain ⟨cIdx, hciff⟩ := hal
    rcases hciff with hc | ⟨hp, hq⟩
    · exact sat3_split_killed_of_sign_separation N hv hm3 hk op g h S hg hh hf cIdx
        (Or.inl hc)
    · exact sat3_split_killed_of_sign_separation N hv hm3 hk op g h S hg hh hf cIdx
        (Or.inr ⟨hq, hp⟩)

/-- **THE CONDITIONAL RECORD (hypothesis named, not claimed)**: killing sign-aligned cuts gives the first
bound beyond connectivity. -/
theorem sat3_cbudget_2mD_of_sign_aligned (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hW : Sat3SignAlignedNoSplit N hm3 hk) :
    2 * (sat3M N * sat3D N) ≤ cbudget (sat3Family N) :=
  sat3_cbudget_2mD_of_no_proper_split N hv hm3 hk
    (sat3_no_split_of_sign_aligned N hv hm3 hk hW)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_split_killed_of_sign_separation
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_no_split_of_sign_aligned
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_2mD_of_sign_aligned
