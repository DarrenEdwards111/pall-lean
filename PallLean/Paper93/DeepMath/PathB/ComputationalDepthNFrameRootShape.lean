import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameReadOnceSplit

/-!
# N-Frame: the root-shape reduction — a minimal SAT circuit ends in a proper binary merge

Rung (1) of the read-once kill, complete.  Every non-proper root shape dies:

  `sat3_not_unary` — **PROVED, the semantic kill**: SAT is not `σ (x i)` for any coordinate `i` and any
        unary `σ` — one lemma covering constants, dictators, anti-dictators.  (The selector flip at `ZBase`
        pins `i` to a slot-2 selector; the sign flip at the workhorse context pins `i` to the sign bit;
        the two bits differ.)
  `shrink_last_two` — **PROVED, the fusion surgery**: if the output is a unary function `F` of the wire at
        `length − 2` and that gate is binary, fuse `F` into it and drop the root — a shorter circuit,
        contradicting minimality.
  `sat3_root_shape` — **PROVED, the reduction**: a minimal SAT circuit's root is `bin op L R` with
        `L ≠ R`, both interior.  (`var`/`cst` roots die by `sat3_not_unary`; `un` roots, degenerate
        `bin op L L` roots, and garbage-reference roots are unary-in-disguise: Normal Form IV forces the
        surviving child to be `length − 2`, and the gate there is binary — fused away — unary — Normal
        Form II — or `var`/`cst` — `sat3_not_unary` again.)

With `excess_zero_top_split`: a minimal SAT circuit with `coneExcess = 0` yields a genuine bipartite
decomposition `sat3 = op (g|_S, h|_T)` with `S, T` disjoint.  The single remaining rung of the read-once
kill is the semantic no-bipartite-split (the clash-pair certificate, spanning every cut) — the honest wall,
unchanged.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Prefix runs agree with the full run on computed positions. -/
theorem takeRun_getD_eq {n : ℕ} (c : List (CGate n)) (x : Fin n → Bool) (m q : ℕ)
    (hq : q < m) (hm : m ≤ c.length) :
    (runFrom x [] (c.take m)).getD q false = (runFrom x [] c).getD q false := by
  have hplen : (runFrom x [] (c.take m)).length = m := by
    rw [runFrom_length]
    simp only [List.length_nil, List.length_take]
    omega
  have hfull : runFrom x [] c = runFrom x (runFrom x [] (c.take m)) (c.drop m) := by
    conv_lhs => rw [← List.take_append_drop m c]
    rw [runFrom_append]
  rw [hfull, runFrom_getD_stable x (c.drop m) (runFrom x [] (c.take m)) q
    (by rw [hplen]; omega)]

/-- **THE SEMANTIC KILL (proved)**: SAT is not a unary function of any single coordinate. -/
theorem sat3_not_unary (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (i : Fin N) (σ : Bool → Bool) :
    ¬ ∀ x : Fin N → Bool, sat3Family N x = σ (x i) := by
  intro hσ
  set c₀ : Fin (sat3M N) := ⟨0, by omega⟩ with hc₀
  set j₀ : Fin (sat3V N) := ⟨0, hv⟩ with hj₀
  -- selector flip pins i to the selector
  have h1 := sat3ZBase_flip_sat N hv c₀ j₀
  have h2 := sat3ZBase_unsat N c₀
  rw [hσ] at h1 h2
  have hisel : i = sat3S2Sel N c₀ j₀ := by
    by_contra hne
    rw [Function.update_of_ne hne] at h1
    rw [h1] at h2
    cases h2
  -- sign flip pins i to the sign bit
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  have hbeh : ∀ a : Bool,
      sat3Family N (Function.update (sat3Patch N c₀
        (sat3Context N c₀ hk (fun _ => false)) (sat3Probe N ⟨0, hv⟩ false))
        (sat3SignBit N c₀) a) = xor false a := by
    intro a
    rw [patch_probe_update]
    exact sat3Context_probe_eval N hv hk hkv c₀ (fun _ => false)
      ⟨0, by omega⟩ ⟨0, hv⟩ rfl a
  have ht := hbeh true
  have hf := hbeh false
  rw [hσ] at ht hf
  have hisign : i = sat3SignBit N c₀ := by
    by_contra hne
    rw [Function.update_of_ne hne] at ht hf
    rw [ht] at hf
    cases hf
  exact sat3S2Sel_ne_signBit N c₀ j₀ c₀ (hisel ▸ hisign)

/-- **THE FUSION SURGERY (proved)**: output = `F` of the wire at `length − 2`, and that gate binary —
fuse `F` in, drop the root, contradict minimality. -/
theorem shrink_last_two {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f) (hlen2 : 2 ≤ c.length)
    (op₂ : Bool → Bool → Bool) (j k : ℕ)
    (hg2 : c.getD (c.length - 2) (CGate.cst false) = CGate.bin op₂ j k)
    (F : Bool → Bool)
    (hsem : ∀ x, f x = F ((runFrom x [] c).getD (c.length - 2) false)) : False := by
  set c' : List (CGate n) := c.take (c.length - 2)
      ++ [CGate.bin (fun a b => F (op₂ a b)) j k] with hc'
  have hlen' : c'.length = c.length - 1 := by
    rw [hc', List.length_append, List.length_take]
    simp only [List.length_cons, List.length_nil]
    omega
  have hcomp' : computes c' f := by
    intro x
    have hplen : (runFrom x [] (c.take (c.length - 2))).length = c.length - 2 := by
      rw [runFrom_length]
      simp only [List.length_nil, List.length_take]
      omega
    show (runFrom x [] c').getD (c'.length - 1) false = f x
    rw [hc', runFrom_append]
    show ((runFrom x [] (c.take (c.length - 2)))
        ++ [evalGate x (runFrom x [] (c.take (c.length - 2)))
            (CGate.bin (fun a b => F (op₂ a b)) j k)]).getD (c'.length - 1) false = f x
    rw [List.getD_append_right _ _ _ _ (by rw [hplen, hlen']; omega)]
    rw [show c'.length - 1 - (runFrom x [] (c.take (c.length - 2))).length = 0 from by
      rw [hplen, hlen']; omega]
    show F (op₂ ((runFrom x [] (c.take (c.length - 2))).getD j false)
        ((runFrom x [] (c.take (c.length - 2))).getD k false)) = f x
    rw [hsem x, output_getD_at x c (c.length - 2) (by omega), hg2]
    rfl
  have hb : cbudget f ≤ c'.length := Nat.sInf_le ⟨c', hcomp', rfl⟩
  omega

/-- The dispatcher: the output is a unary `F` of the wire at `length − 2` — every gate shape there dies. -/
theorem sat3_pseudo_unary_kill (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) (hlen2 : 2 ≤ c.length)
    (F : Bool → Bool)
    (hsem : ∀ x, sat3Family N x = F ((runFrom x [] c).getD (c.length - 2) false)) :
    False := by
  cases hg2 : c.getD (c.length - 2) (CGate.cst false) with
  | var i =>
    exact sat3_not_unary N hv hm3 hk i F
      (fun x => by rw [hsem x, wire_val_var c (c.length - 2) i hg2 x])
  | cst b =>
    apply sat3_not_unary N hv hm3 hk (sat3S2Sel N ⟨0, by omega⟩ ⟨0, hv⟩) (fun _ => F b)
    intro x
    rw [hsem x]
    have hw : (runFrom x [] c).getD (c.length - 2) false = b := by
      rw [output_getD_at x c (c.length - 2) (by omega), hg2]
      rfl
    rw [hw]
  | un op₂ j =>
    have hnc : ∃ u w : Fin N → Bool, sat3Family N u ≠ sat3Family N w := by
      refine ⟨Function.update (sat3ZBase N ⟨0, by omega⟩)
        (sat3S2Sel N ⟨0, by omega⟩ ⟨0, hv⟩) true, sat3ZBase N ⟨0, by omega⟩, ?_⟩
      rw [sat3ZBase_flip_sat N hv _ _, sat3ZBase_unsat N _]
      decide
    have h := minimal_un_last (sat3Family N) c hcomp hmin hnc (c.length - 2) op₂ j hg2
      (by omega)
    omega
  | bin op₂ j k =>
    exact shrink_last_two (sat3Family N) c hcomp hmin hlen2 op₂ j k hg2 F hsem

/-- **THE ROOT-SHAPE REDUCTION (proved)**: a minimal SAT circuit's root is a proper binary merge. -/
theorem sat3_root_shape (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    ∃ (op : Bool → Bool → Bool) (L R : ℕ),
      c.getD (c.length - 1) (CGate.cst false) = CGate.bin op L R ∧
      L < c.length - 1 ∧ R < c.length - 1 ∧ L ≠ R := by
  by_cases hcnil : c = []
  · exfalso
    apply sat3_not_unary N hv hm3 hk (sat3S2Sel N ⟨0, by omega⟩ ⟨0, hv⟩) (fun _ => false)
    intro x
    rw [← hcomp x, hcnil]
    rfl
  have hcpos : 0 < c.length :=
    Nat.pos_of_ne_zero (fun h => hcnil (List.eq_nil_of_length_eq_zero h))
  have hout : ∀ x, sat3Family N x
      = evalGate x (runFrom x [] (c.take (c.length - 1)))
          (c.getD (c.length - 1) (CGate.cst false)) := by
    intro x
    have h : (runFrom x [] c).getD (c.length - 1) false = sat3Family N x := hcomp x
    rw [← h, output_getD_at x c (c.length - 1) (by omega)]
  have hplen : ∀ x : Fin N → Bool,
      (runFrom x [] (c.take (c.length - 1))).length = c.length - 1 := by
    intro x
    rw [runFrom_length]
    simp only [List.length_nil, List.length_take]
    omega
  -- NF IV: a live interior child of the root sits at length − 2
  have hchild_pos : ∀ t : ℕ, t < c.length - 1 →
      readsWire (c.length - 2) (c.getD (c.length - 1) (CGate.cst false)) = true →
      True := fun _ _ _ => trivial
  cases hg : c.getD (c.length - 1) (CGate.cst false) with
  | var i =>
    exfalso
    apply sat3_not_unary N hv hm3 hk i (fun b => b)
    intro x
    rw [hout x, hg]
    rfl
  | cst b =>
    exfalso
    apply sat3_not_unary N hv hm3 hk (sat3S2Sel N ⟨0, by omega⟩ ⟨0, hv⟩) (fun _ => b)
    intro x
    rw [hout x, hg]
    rfl
  | un op' L =>
    exfalso
    by_cases hL : L < c.length - 1
    · have hlen2 : 2 ≤ c.length := by omega
      obtain ⟨q, hq, hread⟩ := minimal_wire_read (sat3Family N) c hcomp hmin
        (c.length - 2) (by omega)
      have hqlt : q < c.length := by
        rcases Nat.lt_or_ge q c.length with h | h
        · exact h
        · exfalso
          rw [List.getD_eq_default _ _ h] at hread
          have hfa : readsWire (c.length - 2) (CGate.cst false : CGate N) = false := rfl
          rw [hfa] at hread
          simp at hread
      have hqroot : q = c.length - 1 := by omega
      rw [hqroot, hg] at hread
      have hLeq : L = c.length - 2 := by
        have h' : (L == c.length - 2) = true := hread
        simpa using h'
      apply sat3_pseudo_unary_kill N hv hm3 hk c hcomp hmin hlen2 op'
      intro x
      rw [hout x, hg]
      show op' ((runFrom x [] (c.take (c.length - 1))).getD L false) = _
      rw [hLeq, takeRun_getD_eq c x (c.length - 1) (c.length - 2) (by omega) (by omega)]
    · apply sat3_not_unary N hv hm3 hk (sat3S2Sel N ⟨0, by omega⟩ ⟨0, hv⟩)
        (fun _ => op' false)
      intro x
      rw [hout x, hg]
      show op' ((runFrom x [] (c.take (c.length - 1))).getD L false) = op' false
      rw [List.getD_eq_default _ _ (by rw [hplen x]; omega)]
  | bin op L R =>
    by_cases hL : L < c.length - 1
    · by_cases hR : R < c.length - 1
      · by_cases hLR : L = R
        · -- degenerate bin op L L
          exfalso
          subst hLR
          have hlen2 : 2 ≤ c.length := by omega
          obtain ⟨q, hq, hread⟩ := minimal_wire_read (sat3Family N) c hcomp hmin
            (c.length - 2) (by omega)
          have hqlt : q < c.length := by
            rcases Nat.lt_or_ge q c.length with h | h
            · exact h
            · exfalso
              rw [List.getD_eq_default _ _ h] at hread
              have hfa : readsWire (c.length - 2) (CGate.cst false : CGate N) = false := rfl
              rw [hfa] at hread
              simp at hread
          have hqroot : q = c.length - 1 := by omega
          rw [hqroot, hg] at hread
          have hLeq : L = c.length - 2 := by
            have h' : (L == c.length - 2 || L == c.length - 2) = true := hread
            simp at h'
            exact h'
          apply sat3_pseudo_unary_kill N hv hm3 hk c hcomp hmin hlen2 (fun b => op b b)
          intro x
          rw [hout x, hg]
          show op ((runFrom x [] (c.take (c.length - 1))).getD L false)
              ((runFrom x [] (c.take (c.length - 1))).getD L false) = _
          rw [hLeq, takeRun_getD_eq c x (c.length - 1) (c.length - 2) (by omega) (by omega)]
        · exact ⟨op, L, R, rfl, hL, hR, hLR⟩
      · -- R is a garbage reference: unary in L
        exfalso
        have hlen2 : 2 ≤ c.length := by omega
        obtain ⟨q, hq, hread⟩ := minimal_wire_read (sat3Family N) c hcomp hmin
          (c.length - 2) (by omega)
        have hqlt : q < c.length := by
          rcases Nat.lt_or_ge q c.length with h | h
          · exact h
          · exfalso
            rw [List.getD_eq_default _ _ h] at hread
            have hfa : readsWire (c.length - 2) (CGate.cst false : CGate N) = false := rfl
            rw [hfa] at hread
            simp at hread
        have hqroot : q = c.length - 1 := by omega
        rw [hqroot, hg] at hread
        have hLeq : L = c.length - 2 := by
          have h' : (L == c.length - 2 || R == c.length - 2) = true := hread
          simp at h'
          rcases h' with h' | h'
          · exact h'
          · omega
        apply sat3_pseudo_unary_kill N hv hm3 hk c hcomp hmin hlen2 (fun b => op b false)
        intro x
        rw [hout x, hg]
        show op ((runFrom x [] (c.take (c.length - 1))).getD L false)
            ((runFrom x [] (c.take (c.length - 1))).getD R false) = _
        rw [List.getD_eq_default _ _ (show (runFrom x [] (c.take (c.length - 1))).length ≤ R
          from by rw [hplen x]; omega)]
        rw [hLeq, takeRun_getD_eq c x (c.length - 1) (c.length - 2) (by omega) (by omega)]
    · by_cases hR : R < c.length - 1
      · -- L is a garbage reference: unary in R
        exfalso
        have hlen2 : 2 ≤ c.length := by omega
        obtain ⟨q, hq, hread⟩ := minimal_wire_read (sat3Family N) c hcomp hmin
          (c.length - 2) (by omega)
        have hqlt : q < c.length := by
          rcases Nat.lt_or_ge q c.length with h | h
          · exact h
          · exfalso
            rw [List.getD_eq_default _ _ h] at hread
            have hfa : readsWire (c.length - 2) (CGate.cst false : CGate N) = false := rfl
            rw [hfa] at hread
            simp at hread
        have hqroot : q = c.length - 1 := by omega
        rw [hqroot, hg] at hread
        have hReq : R = c.length - 2 := by
          have h' : (L == c.length - 2 || R == c.length - 2) = true := hread
          simp at h'
          rcases h' with h' | h'
          · omega
          · exact h'
        apply sat3_pseudo_unary_kill N hv hm3 hk c hcomp hmin hlen2 (fun b => op false b)
        intro x
        rw [hout x, hg]
        show op ((runFrom x [] (c.take (c.length - 1))).getD L false)
            ((runFrom x [] (c.take (c.length - 1))).getD R false) = _
        rw [List.getD_eq_default _ _ (show (runFrom x [] (c.take (c.length - 1))).length ≤ L
          from by rw [hplen x]; omega)]
        rw [hReq, takeRun_getD_eq c x (c.length - 1) (c.length - 2) (by omega) (by omega)]
      · -- both garbage: constant
        exfalso
        apply sat3_not_unary N hv hm3 hk (sat3S2Sel N ⟨0, by omega⟩ ⟨0, hv⟩)
          (fun _ => op false false)
        intro x
        rw [hout x, hg]
        show op ((runFrom x [] (c.take (c.length - 1))).getD L false)
            ((runFrom x [] (c.take (c.length - 1))).getD R false) = op false false
        rw [List.getD_eq_default _ _ (show (runFrom x [] (c.take (c.length - 1))).length ≤ L
          from by rw [hplen x]; omega)]
        rw [List.getD_eq_default _ _ (show (runFrom x [] (c.take (c.length - 1))).length ≤ R
          from by rw [hplen x]; omega)]

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_not_unary
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.shrink_last_two
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_root_shape
