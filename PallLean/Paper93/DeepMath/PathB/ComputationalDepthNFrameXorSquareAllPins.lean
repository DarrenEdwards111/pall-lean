import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCoverage

/-!
# N-Frame: XOR-squares for all pins — the square family widens

The residual-shrink step, XOR half.  The single-literal probe machinery (`sat3Probe`,
`sat3Context_probe_eval`, `patch_probe_update`, `sat3Context_update_pin_sign`) is generic in the pinned
variable — so the XOR-square exists for **every** pair (pin-sign of `j₀`, designated sign), all
`(m−2)·m` of them, not just `j₀ = 0`.

  `sat3_xor_square_all_pins` — **PROVED**: engine-format XOR corners `(α, ¬α, ¬α, α)` with `α = bvec j₀`,
        for every block `cIdx`, every pinned variable `j₀`, at every pin context.

## Honest scope

The kill for the new pairs still awaits the matching odd squares: `sat3Probe2` and the two-literal
workhorse are hardcoded to variable `0` and must be re-parameterized (`sat3Probe2 vj`, reads shifted by
`j₀`, forcing through pin clause `j₀`) — a mechanical mirror, named as the next rung.  Once done, the
residual shrinks from "every block's single sign pair aligned" to "all `(m−2)·m` sign pairs aligned",
and the hard tail remains the selector-heavy fully-aligned cut.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **XOR-SQUARES FOR ALL PINS (proved)**: engine-format corners for the pair (pin-sign of `j₀`,
designated sign), for every `j₀`, at every pin context. -/
theorem sat3_xor_square_all_pins (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j₀ : Fin (sat3M N - 2))
    (bvec : Fin (sat3M N - 2) → Bool) :
    ∃ u : Fin N → Bool,
      sat3Family N u = bvec j₀ ∧
      sat3Family N (Function.update u
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
        (!(u (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega))))) = !(bvec j₀) ∧
      sat3Family N (Function.update u (sat3SignBit N cIdx)
        (!(u (sat3SignBit N cIdx)))) = !(bvec j₀) ∧
      sat3Family N (Function.update (Function.update u
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N) (by omega))
        (!(u (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega))))) (sat3SignBit N cIdx)
        (!(u (sat3SignBit N cIdx)))) = bvec j₀ := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hjv : j₀.val < sat3V N := by
    have := j₀.isLt
    omega
  have heval : ∀ (bv : Fin (sat3M N - 2) → Bool) (a : Bool),
      sat3Family N (Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bv)
        (sat3Probe N ⟨j₀.val, hjv⟩ false)) (sat3SignBit N cIdx) a)
      = xor (bv j₀) a := by
    intro bv a
    rw [patch_probe_update]
    exact sat3Context_probe_eval N hv hk hkv cIdx bv j₀ ⟨j₀.val, hjv⟩ rfl a
  have hne_ps : (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩
      (sat3V N) (by omega) : Fin N) ≠ sat3SignBit N cIdx :=
    sat3Bit_ne_of_clause N _ _ _ _
      (fun h => sat3PinClause_ne N cIdx hk j₀ h)
  refine ⟨Function.update (sat3Patch N cIdx (sat3Context N cIdx hk bvec)
    (sat3Probe N ⟨j₀.val, hjv⟩ false)) (sat3SignBit N cIdx) false, ?_, ?_, ?_, ?_⟩
  case _ =>
    rw [heval bvec false, Bool.xor_false]
  case _ =>
    rw [Function.update_of_ne hne_ps,
      pin_read_sign N cIdx hk hkv bvec (sat3Probe N ⟨j₀.val, hjv⟩ false) j₀]
    rw [show Function.update (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (sat3Probe N ⟨j₀.val, hjv⟩ false))
        (sat3SignBit N cIdx) false)
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega)) (!(decide (bvec j₀ = false)))
      = Function.update (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (sat3Probe N ⟨j₀.val, hjv⟩ false))
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega)) (!(decide (bvec j₀ = false))))
        (sat3SignBit N cIdx) false from
      Function.update_comm hne_ps.symm _ _ _]
    rw [sat3Context_update_pin_sign N cIdx hk hkv bvec j₀
      (sat3Probe N ⟨j₀.val, hjv⟩ false) (!(decide (bvec j₀ = false)))]
    rw [heval (Function.update bvec j₀ (!(!(decide (bvec j₀ = false))))) false]
    rw [Function.update_self, Bool.xor_false]
    cases hb : bvec j₀ <;> rfl
  case _ =>
    rw [Function.update_self, Function.update_idem, heval bvec (!false)]
    cases hb : bvec j₀ <;> rfl
  case _ =>
    rw [Function.update_self, Function.update_of_ne hne_ps,
      pin_read_sign N cIdx hk hkv bvec (sat3Probe N ⟨j₀.val, hjv⟩ false) j₀]
    rw [show Function.update (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (sat3Probe N ⟨j₀.val, hjv⟩ false))
        (sat3SignBit N cIdx) false)
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega)) (!(decide (bvec j₀ = false)))
      = Function.update (Function.update (sat3Patch N cIdx
        (sat3Context N cIdx hk bvec) (sat3Probe N ⟨j₀.val, hjv⟩ false))
        (sat3Bit N (sat3PinClause N cIdx hk j₀) ⟨0, by omega⟩ (sat3V N)
          (by omega)) (!(decide (bvec j₀ = false))))
        (sat3SignBit N cIdx) false from
      Function.update_comm hne_ps.symm _ _ _]
    rw [sat3Context_update_pin_sign N cIdx hk hkv bvec j₀
      (sat3Probe N ⟨j₀.val, hjv⟩ false) (!(decide (bvec j₀ = false)))]
    rw [Function.update_idem]
    rw [heval (Function.update bvec j₀ (!(!(decide (bvec j₀ = false))))) (!false)]
    rw [Function.update_self]
    cases hb : bvec j₀ <;> rfl

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_xor_square_all_pins
