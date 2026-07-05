import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameEvasiveness

/-!
# N-Frame: the budget cash-out — `cbudget ≥ 2·(live region) + Ω(m)`

The gate-count payoff of the Track C chain.  The structural law is already in the repository
(`connectivity_fanout`: `2·|V| + coneExcess ≤ length + 1` for any set `V` of influential bits);
what this file adds is the **full live region** as the influential set and the assembly:

  `influence_pair_transport` — **PROVED**: an involutive input invariance carries an influence
        pair at bit `b` to one at `σ b`.
  `sat3_sign_influential` — **PROVED**: every slot-0 sign bit is influential (the single-probe
        eval at `sgn = false` versus `sgn = true`).
  `sat3_live_influential` — **PROVED**: EVERY live bit — all three slots, selectors and signs,
        of every block — is influential for `sat3Family`, by slot-swap transport.
  `sat3_cbudget_cashout` — **PROVED**: for every minimal circuit,
        `2·m·D + coneExcess ≤ cbudget + 1` — the reading cost of the live region plus the full
        curvature payment.
  `sat3_cbudget_omega` — **PROVED, the headline**: `64·(m·D) + m ≤ 32·cbudget + 95`, i.e.
        `cbudget ≥ 2·m·D + m/32 − 3` — the ledger's `2N + Ω(m)` shape at the live-region scale.
  `sat3_cbudget_ge_two_N` — **PROVED, the N-form**: `2N ≤ cbudget + 6v + 5`, i.e.
        `cbudget ≥ 2N − O(√N)`.

## Honest scope

The exact bound is `cbudget ≥ 2·(N − N mod D) + Ω(m) − 1`: the live region is `m·D = N − (N mod D)`
bits (the tail is genuinely non-influential — sat3 ignores it — so a literal `2N + Ω(m)` at bit
exactness is impossible, and is not claimed).  The `Ω(m) = Ω(√N)` term is the curvature payment on
top of the reading cost, and is the entire content of the Track C arc — a linear-plus-`√N` bound in
the repository's boundary-transducer wire model.  Every theorem here is unconditional given the
size conditions `1 ≤ v`, `3 ≤ m`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP` — superlinear it is
not, and the model is restricted.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **THE TRANSPORT (proved)**: an involutive input invariance carries an influence pair at `b`
to one at `σ b`. -/
theorem influence_pair_transport {n : ℕ} (f : (Fin n → Bool) → Bool)
    (σ : Fin n → Fin n) (hinv : ∀ b, σ (σ b) = b)
    (hf : ∀ x : Fin n → Bool, f (fun i => x (σ i)) = f x)
    (b : Fin n) (x y : Fin n → Bool)
    (hagree : ∀ i : Fin n, i ≠ b → x i = y i) (hne : f x ≠ f y) :
    ∃ x' y' : Fin n → Bool,
      (∀ i : Fin n, i ≠ σ b → x' i = y' i) ∧ f x' ≠ f y' := by
  refine ⟨fun i => x (σ i), fun i => y (σ i), ?_, ?_⟩
  · intro i hi
    apply hagree
    intro hcon
    apply hi
    have h1 : σ (σ i) = σ b := congrArg σ hcon
    rw [hinv] at h1
    exact h1
  · rw [hf x, hf y]
    exact hne

/-- **THE SIGN WITNESS PAIR (proved)**: every slot-0 sign bit is influential for the SAT family —
the single-probe eval at `sgn = false` versus `sgn = true`. -/
theorem sat3_sign_influential (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (c : Fin (sat3M N)) :
    ∃ x y : Fin N → Bool,
      (∀ i : Fin N, i ≠ sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega) → x i = y i)
      ∧ sat3Family N x ≠ sat3Family N y := by
  classical
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set bvec : Fin (sat3M N - 2) → Bool := fun _ => false with hbvec
  refine ⟨sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N ⟨0, hv⟩ false),
    sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N ⟨0, hv⟩ true), ?_, ?_⟩
  · intro i hi
    show (if i.val / sat3D N = c.val
        then sat3Probe N ⟨0, hv⟩ false i else sat3Context N c hk bvec i)
      = (if i.val / sat3D N = c.val
        then sat3Probe N ⟨0, hv⟩ true i else sat3Context N c hk bvec i)
    by_cases hdiv : i.val / sat3D N = c.val
    · rw [if_pos hdiv, if_pos hdiv]
      show decide (i.val % sat3D N = (⟨0, hv⟩ : Fin (sat3V N)).val
          ∨ (i.val % sat3D N = sat3V N ∧ false = true))
        = decide (i.val % sat3D N = (⟨0, hv⟩ : Fin (sat3V N)).val
          ∨ (i.val % sat3D N = sat3V N ∧ true = true))
      by_cases h0 : i.val % sat3D N = (⟨0, hv⟩ : Fin (sat3V N)).val
      · rw [decide_eq_true (Or.inl h0), decide_eq_true (Or.inl h0)]
      · by_cases hsg : i.val % sat3D N = sat3V N
        · exfalso
          apply hi
          apply Fin.ext
          show i.val = c.val * sat3D N + 0 * (sat3V N + 1) + sat3V N
          have hdm := Nat.div_add_mod i.val (sat3D N)
          rw [hdiv, hsg] at hdm
          have hcm : sat3D N * c.val = c.val * sat3D N := Nat.mul_comm _ _
          omega
        · have hfa : decide (i.val % sat3D N = (⟨0, hv⟩ : Fin (sat3V N)).val
              ∨ (i.val % sat3D N = sat3V N ∧ false = true)) = false := by
            apply decide_eq_false
            rintro (h | ⟨h, -⟩)
            · exact h0 h
            · exact hsg h
          have hfb : decide (i.val % sat3D N = (⟨0, hv⟩ : Fin (sat3V N)).val
              ∨ (i.val % sat3D N = sat3V N ∧ true = true)) = false := by
            apply decide_eq_false
            rintro (h | ⟨h, -⟩)
            · exact h0 h
            · exact hsg h
          rw [hfa, hfb]
    · rw [if_neg hdiv, if_neg hdiv]
  · rw [sat3Context_probe_eval N hv hk hkv c bvec ⟨0, by omega⟩ ⟨0, hv⟩ rfl false,
      sat3Context_probe_eval N hv hk hkv c bvec ⟨0, by omega⟩ ⟨0, hv⟩ rfl true]
    exact Bool.false_ne_true

/-- **THE LIVE-REGION INFLUENCE (proved)**: every bit of every live block — all three slots,
selectors and signs — is influential for the SAT family. -/
theorem sat3_live_influential (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (c : Fin (sat3M N)) (t : Fin 3)
    (fd : ℕ) (hfd : fd < sat3V N + 1) :
    ∃ x y : Fin N → Bool,
      (∀ i : Fin N, i ≠ sat3Bit N c t fd hfd → x i = y i)
      ∧ sat3Family N x ≠ sat3Family N y := by
  rcases Nat.lt_or_ge fd (sat3V N) with hlt | hge
  · obtain ⟨x, y, hagree, hne⟩ := sat3_selector_influential N hv hm3 hk c ⟨fd, hlt⟩
    obtain ⟨x', y', hagree', hne'⟩ := influence_pair_transport (sat3Family N)
      (slotSwapBit N t) (slotSwapBit_invol N t) (sat3Family_slotSwap N t)
      _ x y hagree hne
    refine ⟨x', y', ?_, hne'⟩
    intro i hi
    apply hagree'
    intro hcon
    apply hi
    rw [hcon, slotSwapBit_bit, swapSlotF_zero]
  · have hfv : fd = sat3V N := by omega
    subst hfv
    obtain ⟨x, y, hagree, hne⟩ := sat3_sign_influential N hv hm3 hk c
    obtain ⟨x', y', hagree', hne'⟩ := influence_pair_transport (sat3Family N)
      (slotSwapBit N t) (slotSwapBit_invol N t) (sat3Family_slotSwap N t)
      _ x y hagree hne
    refine ⟨x', y', ?_, hne'⟩
    intro i hi
    apply hagree'
    intro hcon
    apply hi
    rw [hcon, slotSwapBit_bit, swapSlotF_zero]

set_option maxHeartbeats 800000 in
/-- **THE BUDGET CASH-OUT (proved)**: every minimal circuit of the SAT family pays the reading
cost of the whole live region plus the full curvature: `2·m·D + coneExcess ≤ cbudget + 1`. -/
theorem sat3_cbudget_cashout (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N)) :
    2 * (sat3M N * sat3D N) + coneExcess cc (cc.length - 1)
      ≤ cbudget (sat3Family N) + 1 := by
  classical
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  set V : Finset (Fin N) :=
    (Finset.univ : Finset (Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1))).image
      (fun ctf => sat3Bit N ctf.1 ctf.2.1 ctf.2.2.val ctf.2.2.isLt) with hV
  have hinj : Function.Injective
      (fun ctf : Fin (sat3M N) × Fin 3 × Fin (sat3V N + 1) =>
        sat3Bit N ctf.1 ctf.2.1 ctf.2.2.val ctf.2.2.isLt) := by
    intro a b heq
    have hveq : (sat3Bit N a.1 a.2.1 a.2.2.val a.2.2.isLt).val
        = (sat3Bit N b.1 b.2.1 b.2.2.val b.2.2.isLt).val := congrArg Fin.val heq
    have hdA := sat3Bit_clause N a.1 a.2.1 a.2.2.val a.2.2.isLt
    have hdB := sat3Bit_clause N b.1 b.2.1 b.2.2.val b.2.2.isLt
    have hrA := sat3Bit_rem N a.1 a.2.1 a.2.2.val a.2.2.isLt
    have hrB := sat3Bit_rem N b.1 b.2.1 b.2.2.val b.2.2.isLt
    have hrem : a.2.1.val * (sat3V N + 1) + a.2.2.val
        = b.2.1.val * (sat3V N + 1) + b.2.2.val := by
      rw [← hrA, ← hrB, hveq]
    have hsA : (a.2.1.val * (sat3V N + 1) + a.2.2.val) / (sat3V N + 1)
        = a.2.1.val := by
      rw [Nat.mul_comm a.2.1.val (sat3V N + 1), Nat.mul_add_div (by omega),
        Nat.div_eq_of_lt a.2.2.isLt]
      omega
    have hsB : (b.2.1.val * (sat3V N + 1) + b.2.2.val) / (sat3V N + 1)
        = b.2.1.val := by
      rw [Nat.mul_comm b.2.1.val (sat3V N + 1), Nat.mul_add_div (by omega),
        Nat.div_eq_of_lt b.2.2.isLt]
      omega
    have hfA : (a.2.1.val * (sat3V N + 1) + a.2.2.val) % (sat3V N + 1)
        = a.2.2.val := by
      rw [Nat.mul_comm a.2.1.val (sat3V N + 1), Nat.mul_add_mod,
        Nat.mod_eq_of_lt a.2.2.isLt]
    have hfB : (b.2.1.val * (sat3V N + 1) + b.2.2.val) % (sat3V N + 1)
        = b.2.2.val := by
      rw [Nat.mul_comm b.2.1.val (sat3V N + 1), Nat.mul_add_mod,
        Nat.mod_eq_of_lt b.2.2.isLt]
    have hc : a.1 = b.1 := Fin.ext (by rw [← hdA, ← hdB, hveq])
    have ht : a.2.1 = b.2.1 := Fin.ext (by rw [← hsA, ← hsB, hrem])
    have hfe : a.2.2 = b.2.2 := Fin.ext (by rw [← hfA, ← hfB, hrem])
    exact Prod.ext hc (Prod.ext ht hfe)
  have hVcard : V.card = sat3M N * sat3D N := by
    rw [hV, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_fin]
    show sat3M N * (3 * (sat3V N + 1)) = sat3M N * sat3D N
    rfl
  have hess : ∀ i ∈ V, ∃ x₁ x₀ : Fin N → Bool,
      (∀ b : Fin N, x₁ b ≠ x₀ b → b = i)
      ∧ sat3Family N x₁ ≠ sat3Family N x₀ := by
    intro i hiV
    rw [hV] at hiV
    obtain ⟨ctf, -, rfl⟩ := Finset.mem_image.mp hiV
    obtain ⟨x, y, hagree, hne⟩ := sat3_live_influential N hv hm3 hk
      ctf.1 ctf.2.1 ctf.2.2.val ctf.2.2.isLt
    refine ⟨x, y, ?_, hne⟩
    intro b hb
    by_contra hbne
    exact hb (hagree b hbne)
  have hcf := connectivity_fanout (sat3Family N) V hess cc hcomp
  rw [hVcard] at hcf
  omega

/-- **THE HEADLINE (proved)**: `cbudget ≥ 2·m·D + m/32 − 3` — the reading cost of the live
region plus an `Ω(m) = Ω(√N)` curvature term, in exact ℕ form. -/
theorem sat3_cbudget_omega (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N)) :
    64 * (sat3M N * sat3D N) + sat3M N ≤ 32 * cbudget (sat3Family N) + 95 := by
  have h1 := sat3_cbudget_cashout N hv hm3 cc hcomp hmin
  have h2 := sat3_coneExcess_omega_unconditional N hv hm3 cc hcomp hmin
  omega

/-- **THE N-FORM (proved)**: `cbudget ≥ 2N − O(√N)` — exactly, `2N ≤ cbudget + 6v + 5`. -/
theorem sat3_cbudget_ge_two_N (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (cc : List (CGate N)) (hcomp : computes cc (sat3Family N))
    (hmin : cc.length = cbudget (sat3Family N)) :
    2 * N ≤ cbudget (sat3Family N) + 6 * sat3V N + 5 := by
  have h1 := sat3_cbudget_cashout N hv hm3 cc hcomp hmin
  have hNd : sat3D N * sat3M N + N % sat3D N = N := Nat.div_add_mod N (sat3D N)
  have hmd : N % sat3D N < sat3D N := Nat.mod_lt _ (sat3D_pos N)
  have hDD : sat3D N = 3 * (sat3V N + 1) := rfl
  have hcm : sat3D N * sat3M N = sat3M N * sat3D N := Nat.mul_comm _ _
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_live_influential
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_cashout
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_omega
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_ge_two_N
