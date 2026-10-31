import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameExitSetInstantiation

/-!
# N-Frame: trace one-bit propagation — the counting arc meets cone excess

The first counting theorem at **trace strength**, and its circuit cash-out.  The slot-`t` one-bit
propagation replays verbatim against a trace-interfaced factorization — the mix/patch transfer and
the context-support arguments never used the coordinate interface, only the exclusive side `S` —
with the capacity call swapped from the coordinate engine to `trace_split_row_capacity`.

  `sat3_selT_pin_propagation_trace` — **PROVED**: for any `TraceInterfacedFactorization` of
        `sat3Family` over `S` with a `j`-bit trace: among pins whose slot-`t` selector lies in `S`,
        at most `j + 1` have their pin sign outside `S` — for every block, every slot.
  `sat3_circuit_selT_pin_bound` — **PROVED, the circuit cash-out**: for every minimal SAT circuit
        there are root children `L, R` such that for **every** block and slot, at most
        `coneExcess + 1` pins have their slot-`t` selector inside the circuit's exclusive-left
        variable side with pin sign outside it.  The first counting bound of the arc whose right
        side is **cone excess**, not an abstract interface.

## Honest scope

This demonstrates the mechanical trace upgrade for the row-capacity family.  Still open, named:
the coordinate-interning counts (sign graph, escape counts, menus) have no wire analogue, and
replacing their role at trace strength is the remaining semantic work; the swallowed-side recursion
is the remaining structural design problem.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

set_option maxHeartbeats 1600000 in
/-- **THE TRACE ONE-BIT LAW (proved)**: over any trace-interfaced factorization, among pins whose
slot-`t` selector lies in the exclusive side, at most `j + 1` have their pin sign outside it. -/
theorem sat3_selT_pin_propagation_trace (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    {S : Finset (Fin N)} {j : ℕ}
    (htf : TraceInterfacedFactorization (sat3Family N) S j)
    (c : Fin (sat3M N)) (t : Fin 3) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N c t p.val
        (by have := sat3M_pred_le_sat3V N; have := p.isLt; omega) ∈ S ∧
      sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ S)).card ≤ j + 1 := by
  classical
  obtain ⟨op, G, H, φ, hφ, hG, hH, hf⟩ := htf
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set Jf := (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
    sat3Bit N c t p.val
      (by have := sat3M_pred_le_sat3V N; have := p.isLt; omega) ∈ S ∧
    sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
      (by omega) ∉ S) with hJf
  set e : (↥Jf → Bool) → (Fin (sat3M N - 2) → Bool) :=
    fun bb p => if hmem : p ∈ Jf then bb ⟨p, hmem⟩ else false with he
  have heval : ∀ (bb : ↥Jf → Bool) (w : ↥Jf), e bb w.val = bb w := by
    intro bb w
    show (if hmem : w.val ∈ Jf then bb ⟨w.val, hmem⟩ else false) = bb w
    rw [dif_pos w.prop, Subtype.coe_eta]
  have heinj : Function.Injective e := by
    intro bb bb' heq
    funext w
    rw [← heval bb w, ← heval bb' w, heq]
  set Y : Finset (Fin N → Bool) :=
    Finset.univ.image (fun bb : ↥Jf → Bool => sat3Context N c hk (e bb)) with hY
  have hYcard : Y.card = 2 ^ Jf.card := by
    rw [hY, Finset.card_image_of_injective _
        (fun bb bb' heq => heinj (sat3Context_injective N hv hk hkv c heq)),
      Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_bool]
  have hdist : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' →
      ∃ x, sat3Family N (mixOn S x y) ≠ sat3Family N (mixOn S x y') := by
    intro y hy y' hy' hne
    rw [hY] at hy hy'
    obtain ⟨bb, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨bb', -, rfl⟩ := Finset.mem_image.mp hy'
    have hbne : e bb ≠ e bb' := fun hh' => hne (by rw [hh'])
    obtain ⟨j₀, hj₀ne⟩ := Function.ne_iff.mp hbne
    have hj₀J : j₀ ∈ Jf := by
      by_contra hmem
      apply hj₀ne
      show (if hm : j₀ ∈ Jf then bb ⟨j₀, hm⟩ else false)
        = (if hm : j₀ ∈ Jf then bb' ⟨j₀, hm⟩ else false)
      rw [dif_neg hmem, dif_neg hmem]
    have hj₀mem := Finset.mem_filter.mp (hJf ▸ hj₀J)
    have hselJ := hj₀mem.2.1
    have hjv : j₀.val < sat3V N := by
      have := j₀.isLt
      omega
    set uu : Fin N → Bool :=
      fun bit => decide (bit = sat3Bit N c t j₀.val (by omega)) with huudef
    have hpteq : ∀ bv : Fin (sat3M N - 2) → Bool,
        sat3Patch N c (sat3Context N c hk bv) uu
          = slotSignPt N c hk t j₀ hjv bv true false := by
      intro bv
      funext i
      rw [huudef]
      unfold slotSignPt
      by_cases hsig : i = sat3Bit N c t (sat3V N) (by omega)
      · rw [hsig, Function.update_self]
        show (if (sat3Bit N c t (sat3V N) (by omega)).val / sat3D N = c.val
          then decide (sat3Bit N c t (sat3V N) (by omega)
            = sat3Bit N c t j₀.val (by omega))
          else sat3Context N c hk bv (sat3Bit N c t (sat3V N) (by omega)))
          = false
        rw [if_pos (sat3Bit_div N c t (sat3V N) (by omega))]
        exact decide_eq_false (sat3Bit_ne_same_block N c t t (sat3V N) j₀.val
          (by omega) (by omega) (by rintro ⟨-, h'⟩; omega))
      · rw [Function.update_of_ne hsig]
        by_cases hsel : i = sat3Bit N c t j₀.val (by omega)
        · rw [hsel, Function.update_self]
          show (if (sat3Bit N c t j₀.val (by omega)).val / sat3D N = c.val
            then decide (sat3Bit N c t j₀.val (by omega)
              = sat3Bit N c t j₀.val (by omega))
            else sat3Context N c hk bv (sat3Bit N c t j₀.val (by omega)))
            = true
          rw [if_pos (sat3Bit_div N c t j₀.val (by omega))]
          exact decide_eq_true rfl
        · rw [Function.update_of_ne hsel]
          show (if i.val / sat3D N = c.val
            then decide (i = sat3Bit N c t j₀.val (by omega))
            else sat3Context N c hk bv i)
            = (if i.val / sat3D N = c.val then (fun _ => false) i
              else sat3Context N c hk bv i)
          by_cases hdiv : i.val / sat3D N = c.val
          · rw [if_pos hdiv, if_pos hdiv]
            exact decide_eq_false hsel
          · rw [if_neg hdiv, if_neg hdiv]
    have huu : sat3Family N (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        ≠ sat3Family N (sat3Patch N c (sat3Context N c hk (e bb')) uu) := by
      rw [hpteq (e bb), hpteq (e bb'),
        slotSignPt_eval N hv hk hkv hm3 c t j₀ hjv (e bb) true false,
        slotSignPt_eval N hv hk hkv hm3 c t j₀ hjv (e bb') true false]
      intro heq
      exact hj₀ne (and_xor_false_inj _ _ heq)
    have hprobe0 : ∀ i : Fin N, i.val / sat3D N = c.val → i ∉ S →
        uu i = false := by
      intro i hdiv hi
      rw [huudef]
      show decide _ = false
      rw [decide_eq_false_iff_not]
      intro hcon
      apply hi
      rw [hcon]
      exact hselJ
    have hagree : ∀ i : Fin N, i ∈ S →
        sat3Context N c hk (e bb) i = sat3Context N c hk (e bb') i := by
      intro i hi
      apply sat3Context_agree
      intro p hp1 hp2
      by_cases hmem : p ∈ Jf
      · exfalso
        have hπ := (Finset.mem_filter.mp (hJf ▸ hmem)).2.2
        apply hπ
        have hiπ : sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
            (by omega) = i := by
          apply Fin.ext
          show (sat3PinClause N c hk p).val * sat3D N + 0 * (sat3V N + 1)
            + sat3V N = i.val
          have hdm := Nat.div_add_mod i.val (sat3D N)
          rw [hp1, hp2] at hdm
          have hcm : sat3D N * (sat3PinClause N c hk p).val
              = (sat3PinClause N c hk p).val * sat3D N := Nat.mul_comm _ _
          omega
        rw [hiπ]
        exact hi
      · show (if hm : p ∈ Jf then bb ⟨p, hm⟩ else false)
          = (if hm : p ∈ Jf then bb' ⟨p, hm⟩ else false)
        rw [dif_neg hmem, dif_neg hmem]
    refine ⟨sat3Patch N c (sat3Context N c hk (e bb)) uu, ?_⟩
    have hmix1 : mixOn S (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        (sat3Context N c hk (e bb))
        = sat3Patch N c (sat3Context N c hk (e bb)) uu := by
      funext i
      show (if i ∈ S then sat3Patch N c (sat3Context N c hk (e bb)) uu i
        else sat3Context N c hk (e bb) i)
        = sat3Patch N c (sat3Context N c hk (e bb)) uu i
      by_cases hi : i ∈ S
      · rw [if_pos hi]
      · rw [if_neg hi]
        show sat3Context N c hk (e bb) i
          = (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb) i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, sat3Context_designated N c hk (e bb) i hdiv,
            hprobe0 i hdiv hi]
        · rw [if_neg hdiv]
    have hmix2 : mixOn S (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        (sat3Context N c hk (e bb'))
        = sat3Patch N c (sat3Context N c hk (e bb')) uu := by
      funext i
      show (if i ∈ S then sat3Patch N c (sat3Context N c hk (e bb)) uu i
        else sat3Context N c hk (e bb') i)
        = sat3Patch N c (sat3Context N c hk (e bb')) uu i
      by_cases hi : i ∈ S
      · rw [if_pos hi]
        show (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb) i)
          = (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb') i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, if_pos hdiv]
        · rw [if_neg hdiv, if_neg hdiv]
          exact hagree i hi
      · rw [if_neg hi]
        show sat3Context N c hk (e bb') i
          = (if i.val / sat3D N = c.val then uu i else sat3Context N c hk (e bb') i)
        by_cases hdiv : i.val / sat3D N = c.val
        · rw [if_pos hdiv, sat3Context_designated N c hk (e bb') i hdiv,
            hprobe0 i hdiv hi]
        · rw [if_neg hdiv]
    rw [hmix1, hmix2]
    exact huu
  have hcap := trace_split_row_capacity (sat3Family N) S op G H φ hφ hG hH hf
    Y hdist
  rw [hYcard] at hcap
  by_contra hcon
  push_neg at hcon
  have hlt : (2 : ℕ) ^ (j + 1) < 2 ^ Jf.card :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- **THE CIRCUIT CASH-OUT (proved)**: for every minimal SAT circuit there are root children `L, R`
such that for every block and slot, at most `coneExcess + 1` pins have their slot-`t` selector
inside the circuit's exclusive-left variable side with pin sign outside it — the first counting
bound of the arc priced directly in cone excess. -/
theorem sat3_circuit_selT_pin_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N)) :
    ∃ L R : ℕ, ∀ (cb : Fin (sat3M N)) (t : Fin 3),
      ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
        sat3Bit N cb t p.val
          (by have := sat3M_pred_le_sat3V N; have := p.isLt; omega)
          ∈ varsOf cc L \ varsOf cc R ∧
        sat3Bit N (sat3PinClause N cb hk p) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∉ varsOf cc L \ varsOf cc R)).card
        ≤ coneExcess cc (cc.length - 1) + 1 := by
  obtain ⟨L, R, j, hj, htf⟩ :=
    sat3_top_cut_trace_extraction N hv hm3 hk cc hcomp hmin
  refine ⟨L, R, fun cb t => ?_⟩
  have hb := sat3_selT_pin_propagation_trace N hv hm3 hk htf cb t
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selT_pin_propagation_trace
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_circuit_selT_pin_bound
