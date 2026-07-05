import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTraceOneBit

/-!
# N-Frame: trace block propagation — the sign-graph's role at trace strength

The trace-strength replacement of the sign-graph counts, with the honest structural finding stated
first.  **The sign-graph's cell machinery does not port**: a crossing square constrained `op` only
because each flip was invisible to the opposite factor, and in a trace factorization an off-`S`
flip reaches `G` *through the trace* — so the two-sided sign tension (edge rigidity, the
aligned-or-big-interface trichotomy) is a genuinely coordinate-interface phenomenon with no wire
analogue.  What replaces the sign-graph's **role** — anchoring where structure must live — is its
row-based sibling, which does port:

  `sat3_block_subset_pin_propagation_trace` — **PROVED, the ownership law**: if a whole block lies
        inside the exclusive side `S` of a trace-interfaced factorization, then at most `j + 1` of
        its pin signs lie outside `S` — block ownership drags `m − 3 − j` sign bits of **other**
        blocks into `S`.
  `sat3_circuit_block_pin_bound` — **PROVED, the circuit cash-out**: for every minimal SAT circuit
        there are root children `L, R` such that every block contained in the exclusive-left
        variable side drags all but `coneExcess + 1` of its pin signs into that side.

## Honest scope

At trace strength the counting arc now has: reading-kit drags (`sat3_selT_pin_propagation_trace`)
and ownership drags (this file).  What it cannot have is the cells' two-sided tension; the
two-sidedness that the endgame needs (`coneExcess ≥ Ω(m)`) must instead come from the structural
side — the swallowed-side recursion forcing genuine structure into `S` — which remains the open
design problem.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

set_option maxHeartbeats 1600000 in
/-- **THE TRACE OWNERSHIP LAW (proved)**: a block inside the exclusive side drags its pin signs in,
up to `j + 1` exceptions. -/
theorem sat3_block_subset_pin_propagation_trace (N : ℕ) (hv : 1 ≤ sat3V N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    {S : Finset (Fin N)} {j : ℕ}
    (htf : TraceInterfacedFactorization (sat3Family N) S j)
    (c : Fin (sat3M N)) (hsub : blockCoords N c ⊆ S) :
    ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
      sat3Bit N (sat3PinClause N c hk p) ⟨0, by omega⟩ (sat3V N)
        (by omega) ∉ S)).card ≤ j + 1 := by
  classical
  obtain ⟨op, G, H, φ, hφ, hG, hH, hf⟩ := htf
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set Jf := (Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
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
    have hjv : j₀.val < sat3V N := by
      have := j₀.isLt
      omega
    set uu := sat3Probe N ⟨j₀.val, hjv⟩ false with huudef
    have huu : sat3Family N (sat3Patch N c (sat3Context N c hk (e bb)) uu)
        ≠ sat3Family N (sat3Patch N c (sat3Context N c hk (e bb')) uu) := by
      rw [huudef,
        sat3Context_probe_eval N hv hk hkv c (e bb) j₀ ⟨j₀.val, hjv⟩ rfl false,
        sat3Context_probe_eval N hv hk hkv c (e bb') j₀ ⟨j₀.val, hjv⟩ rfl false]
      intro heq
      exact hj₀ne (xor_left_inj _ _ _ heq)
    -- the whole block lies in S, so the override is never consulted off S
    have hprobe0 : ∀ i : Fin N, i.val / sat3D N = c.val → i ∉ S →
        uu i = false := by
      intro i hdiv hi
      exact absurd (hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hdiv⟩)) hi
    have hagree : ∀ i : Fin N, i ∈ S →
        sat3Context N c hk (e bb) i = sat3Context N c hk (e bb') i := by
      intro i hi
      apply sat3Context_agree
      intro p hp1 hp2
      by_cases hmem : p ∈ Jf
      · exfalso
        have hπ := (Finset.mem_filter.mp (hJf ▸ hmem)).2
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

/-- **THE CIRCUIT CASH-OUT (proved)**: every block contained in a minimal circuit's exclusive-left
variable side drags all but `coneExcess + 1` of its pin signs into that side. -/
theorem sat3_circuit_block_pin_bound (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N)) :
    ∃ L R : ℕ, ∀ cb : Fin (sat3M N),
      blockCoords N cb ⊆ varsOf cc L \ varsOf cc R →
      ((Finset.univ : Finset (Fin (sat3M N - 2))).filter (fun p =>
        sat3Bit N (sat3PinClause N cb hk p) ⟨0, by omega⟩ (sat3V N)
          (by omega) ∉ varsOf cc L \ varsOf cc R)).card
        ≤ coneExcess cc (cc.length - 1) + 1 := by
  obtain ⟨L, R, j, hj, htf⟩ :=
    sat3_top_cut_trace_extraction N hv hm3 hk cc hcomp hmin
  refine ⟨L, R, fun cb hsub => ?_⟩
  have hb := sat3_block_subset_pin_propagation_trace N hv hk htf cb hsub
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_block_subset_pin_propagation_trace
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_circuit_block_pin_bound
