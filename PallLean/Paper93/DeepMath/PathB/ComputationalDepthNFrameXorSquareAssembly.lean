import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSquareProduction

/-!
# N-Frame: the XOR-square assembled — engine-format corners for (pin-sign, designated sign)

Track A, rung 1: the first square of the discharge, in the exact `hu/hus/hut/hust` format of
`two_squares_kill_split`.

  `sat3_xor_square_pinSign_designatedSign` — **PROVED**: at every pin context `bvec`, the four
        engine-format corners of the pair (pin-sign bit of `j₀ = 0`, designated sign bit) take the XOR
        pattern `(α, ¬α, ¬α, α)` with `α = bvec j₀` — assembled from `sat3Context_probe_eval` at `bvec`
        and its flip, glued by `sat3Context_update_pin_sign` and update-commutation.

## Honest scope

This is the XOR half of the kill for sign/sign cuts separating this pair.  Still open for the discharge of
`Sat3NoBipartiteSplitProper`: the odd-parity square for the same pair (two-literal workhorse), and coverage
of cuts that do not separate a producible pair (selector-monotonicity blocks XOR-squares there; the
rectangle-closure route is the named alternative).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE XOR-SQUARE (proved)**: engine-format corners `(α, ¬α, ¬α, α)` for the pair
(pin-sign of `j₀ = 0`, designated sign), at every pin context. -/
theorem sat3_xor_square_pinSign_designatedSign (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (bvec : Fin (sat3M N - 2) → Bool) :
    ∃ u : Fin N → Bool,
      sat3Family N u = bvec ⟨0, by omega⟩ ∧
      sat3Family N (Function.update u
        (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
          (by omega))
        (!(u (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
          (by omega))))) = !(bvec ⟨0, by omega⟩) ∧
      sat3Family N (Function.update u (sat3SignBit N cIdx)
        (!(u (sat3SignBit N cIdx)))) = !(bvec ⟨0, by omega⟩) ∧
      sat3Family N (Function.update (Function.update u
        (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
          (by omega))
        (!(u (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
          (by omega))))) (sat3SignBit N cIdx)
        (!(u (sat3SignBit N cIdx)))) = bvec ⟨0, by omega⟩ := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have heval : ∀ (bv : Fin (sat3M N - 2) → Bool) (a : Bool),
      sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bv)
        (sat3Probe N ⟨0, hv⟩ false)) (sat3SignBit N cIdx) a)
      = xor (bv ⟨0, by omega⟩) a := by
    intro bv a
    rw [patch_probe_update]
    exact sat3Context_probe_eval N hv hk hkv cIdx bv ⟨0, by omega⟩ ⟨0, hv⟩ rfl a
  have hne_ps : (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩
      (sat3V N) (by omega) : Fin N) ≠ sat3SignBit N cIdx :=
    sat3Bit_ne_of_clause N _ _ _ _
      (fun h => sat3PinClause_ne N cIdx hk ⟨0, by omega⟩ h)
  refine ⟨Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
    (sat3Probe N ⟨0, hv⟩ false)) (sat3SignBit N cIdx) false, ?_, ?_, ?_, ?_⟩
  -- the pin-sign value at the base point, and the identified flip point
  case _ =>
    rw [heval bvec false, Bool.xor_false]
  case _ =>
    -- pin-sign flip: identify with the bvec-flipped context point
    rw [Function.update_of_ne hne_ps,
      pin_read_sign N cIdx hk hkv bvec (sat3Probe N ⟨0, hv⟩ false) ⟨0, by omega⟩]
    rw [show Function.update (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (sat3Probe N ⟨0, hv⟩ false))
        (sat3SignBit N cIdx) false)
        (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
          (by omega)) (!(decide (bvec ⟨0, by omega⟩ = false)))
      = Function.update (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (sat3Probe N ⟨0, hv⟩ false))
        (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
          (by omega)) (!(decide (bvec ⟨0, by omega⟩ = false))))
        (sat3SignBit N cIdx) false from
      Function.update_comm hne_ps.symm _ _ _]
    rw [sat3Context_update_pin_sign N cIdx hk hkv bvec ⟨0, by omega⟩
      (sat3Probe N ⟨0, hv⟩ false) (!(decide (bvec ⟨0, by omega⟩ = false)))]
    rw [heval (Function.update bvec ⟨0, by omega⟩
      (!(!(decide (bvec ⟨0, by omega⟩ = false))))) false]
    rw [Function.update_self, Bool.xor_false]
    cases hb : bvec ⟨0, by omega⟩ <;> rfl
  case _ =>
    -- designated-sign flip: idempotent update
    rw [Function.update_self, Function.update_idem, heval bvec (!false)]
    cases hb : bvec ⟨0, by omega⟩ <;> rfl
  case _ =>
    -- both flips
    rw [Function.update_self, Function.update_of_ne hne_ps,
      pin_read_sign N cIdx hk hkv bvec (sat3Probe N ⟨0, hv⟩ false) ⟨0, by omega⟩]
    rw [show Function.update (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (sat3Probe N ⟨0, hv⟩ false))
        (sat3SignBit N cIdx) false)
        (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
          (by omega)) (!(decide (bvec ⟨0, by omega⟩ = false)))
      = Function.update (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (sat3Probe N ⟨0, hv⟩ false))
        (sat3Bit N (sat3PinClause N cIdx hk ⟨0, by omega⟩) ⟨0, by omega⟩ (sat3V N)
          (by omega)) (!(decide (bvec ⟨0, by omega⟩ = false))))
        (sat3SignBit N cIdx) false from
      Function.update_comm hne_ps.symm _ _ _]
    rw [sat3Context_update_pin_sign N cIdx hk hkv bvec ⟨0, by omega⟩
      (sat3Probe N ⟨0, hv⟩ false) (!(decide (bvec ⟨0, by omega⟩ = false)))]
    rw [Function.update_idem]
    rw [heval (Function.update bvec ⟨0, by omega⟩
      (!(!(decide (bvec ⟨0, by omega⟩ = false))))) (!false)]
    rw [Function.update_self]
    cases hb : bvec ⟨0, by omega⟩ <;> rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_xor_square_pinSign_designatedSign
