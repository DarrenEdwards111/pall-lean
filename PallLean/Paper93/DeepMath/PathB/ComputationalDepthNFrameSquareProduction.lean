import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConstantWireKill

/-!
# N-Frame: square production I — the pin-sign identification, and the first XOR-square

The first installment of the square production for `two_squares_kill_split`.

  `sat3Context_update_pin_sign` — **PROVED, the identification**: updating the pin-sign *bit* of the
        context point IS updating `bvec` — the context family's cube structure is realized by literal
        single-coordinate updates.  This is the glue that turns `sat3Context_probe_eval`'s four values
        into engine-format squares: with it, the XOR-square for the pair (pin-sign bit of `j₀`,
        designated sign bit) is four applications of the probe eval at `bvec` and its `j₀`-flip — the
        exact `hu/hus/hust/hut` package of `two_squares_kill_split`, the named next assembly.

## Honest scope

This unblocks production of the XOR-square for one pair family; the discharge of
`Sat3NoBipartiteSplitProper` still needs (i) the odd-parity square for the same pair (the two-literal
workhorse context: designated block with slot-0 and slot-1 both selecting the pinned variable, giving
`f = A ∨ sign` — an AND-type pattern), and (ii) coverage of all remaining coordinate-type pairs, where
selector-involved pairs have no XOR-square (SAT is monotone in selectors) and need the rectangle-closure
route.  Named rungs, not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE IDENTIFICATION (proved)**: updating the pin-sign bit of the context point is updating `bvec`. -/
theorem sat3Context_update_pin_sign (N : ℕ) (cIdx : Fin (sat3M N)) {k : ℕ}
    (hk : k + 1 ≤ sat3M N) (hkv : k ≤ sat3V N)
    (bvec : Fin k → Bool) (j₀ : Fin k) (u : Fin N → Bool) (v : Bool) :
    Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec) u)
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega)) v
      = sat3Patch N cIdx (sat3Context N cIdx hk (Function.update bvec j₀ (!v))) u := by
  classical
  funext bit
  by_cases hb : bit = sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
      (by omega)
  · rw [hb, Function.update_self]
    rw [sat3Patch_out N cIdx _ u _
      (fun h => sat3PinClause_ne N cIdx hk j₀ (congrArg Fin.val h))]
    symm
    show decide _ = v
    cases v with
    | true =>
      rw [decide_eq_true_eq]
      refine Or.inl ⟨j₀, by rw [sat3Bit_clause], Or.inr ⟨?_, ?_⟩⟩
      · rw [sat3Bit_rem]
        show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
        omega
      · rw [Function.update_self]
        rfl
    | false =>
      rw [decide_eq_false_iff_not]
      rintro (⟨j, hdiv, hrem⟩ | ⟨-, -, hnp, -⟩)
      · rw [sat3Bit_clause] at hdiv
        have hj : j = j₀ := sat3PinClause_val_inj N cIdx hk hdiv.symm
        subst hj
        rcases hrem with hrem | ⟨-, hval⟩
        · rw [sat3Bit_rem] at hrem
          have : (0 : ℕ) * (sat3V N + 1) + sat3V N = j.val := hrem
          have := j.isLt
          omega
        · rw [Function.update_self] at hval
          cases hval
      · rw [sat3Bit_clause] at hnp
        exact hnp j₀ rfl
  · rw [Function.update_of_ne hb]
    unfold sat3Patch
    by_cases hown : bit.val / sat3D N = cIdx.val
    · rw [if_pos hown, if_pos hown]
    · rw [if_neg hown, if_neg hown]
      show decide _ = decide _
      rw [decide_eq_decide]
      constructor
      · rintro (⟨j, hdiv, hrem⟩ | htaut)
        · refine Or.inl ⟨j, hdiv, ?_⟩
          rcases hrem with hrem | ⟨hremv, hval⟩
          · exact Or.inl hrem
          · refine Or.inr ⟨hremv, ?_⟩
            rw [Function.update_of_ne ?_]
            · exact hval
            · intro hcon
              subst hcon
              apply hb
              apply Fin.ext
              show bit.val = (sat3PinClause N cIdx hk j).val * sat3D N
                  + 0 * (sat3V N + 1) + sat3V N
              have h4 := Nat.div_add_mod bit.val (sat3D N)
              rw [hdiv, hremv,
                Nat.mul_comm (sat3D N) ((sat3PinClause N cIdx hk j).val)] at h4
              omega
        · exact Or.inr htaut
      · rintro (⟨j, hdiv, hrem⟩ | htaut)
        · refine Or.inl ⟨j, hdiv, ?_⟩
          rcases hrem with hrem | ⟨hremv, hval⟩
          · exact Or.inl hrem
          · refine Or.inr ⟨hremv, ?_⟩
            rw [Function.update_of_ne ?_] at hval
            · exact hval
            · intro hcon
              subst hcon
              apply hb
              apply Fin.ext
              show bit.val = (sat3PinClause N cIdx hk j).val * sat3D N
                  + 0 * (sat3V N + 1) + sat3V N
              have h4 := Nat.div_add_mod bit.val (sat3D N)
              rw [hdiv, hremv,
                Nat.mul_comm (sat3D N) ((sat3PinClause N cIdx hk j).val)] at h4
              omega
        · exact Or.inr htaut

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Context_update_pin_sign
