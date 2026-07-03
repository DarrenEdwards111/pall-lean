import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameXorFreeThreeKill

/-!
# N-Frame: the interleaved xor-free schedule — `2·m·v + 3·(m−2) + 1`, beating the general-basis record

The two schedules compose.  The xor-free cascade makes the two-kill dichotomy *simpler* at the `xbudget` level
than it was for `budget` — no `single_read_collapse` is needed, because the cascade's escape branches already
carry the top-decomposition data:

  `xbudget_twokill_all` — **PROVED**: for live, non-top-decomposable `f`, restriction kills two nodes of the
        xor-free budget for every value (occurrence `≥ 1` feeds the cascade's `occ + 1`; the bare-leaf, unarity,
        and top-shape branches each *are* a top decomposition, refuting `¬TopDecomp` directly).
  `xbudget_twokill_chain` — **PROVED**: a `TwoKillChain` peels `2·length` off `xbudget`, leaving the restricted
        function's budget intact for further scheduling — the composition hook the `budget` engine never needed.
  `sat3_selector_chain` — **PROVED**: the slot-2 selector chain (the identity/constant-true/constant-false
        behavior triple at every `(c, j)`) packaged as a standalone `TwoKillChain` of length `m·v`.
  `sat3_interleave_min_occ` — **PROVED**: after zeroing *all* slot-2 selectors and freezing any interior sign
        prefix, every remaining interior sign bit still shows both orientations — the orientation contexts have
        every slot-2 selector `false` (probe, pins, and tautologies never touch slot 2) and every interior pin
        sign `true`.
  `sat3_xorfree_interleaved_schedule` — **PROVED, the record**:

        `2·(m·v) + 3·(m−2) + 1 ≤ xbudget (sat3Family N)`

        — strictly above the general-basis `2·m·v + 1`: the first number in the arc that *beats* the `B₂` record,
        by running the selector two-kills and the sign-bit three-kills in one budget.

## Honest scope

The gain over the transferred record is the additive `3·(m−2) ≈ √N` term — the three-kill mechanism is confined
to sign bits by selector monotonicity (previous file), so this is the ceiling of the orientation route at tree
level.  The bound lives in the xor-free basis: over `B₂` the premise provably fails (read-once normal form), and
`budget (sat3Family) ≥ 2·m·v + 3·(m−2) + 1` is *not* claimed.  Superlinear needs the DAG observer (sharing-aware
wire surgery on `cbudget`), untouched here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The xor-free two-kill: the cascade already carries the dichotomy -/

/-- **The xor-free two-kill, for every value (proved)**: dependence gives occurrence `≥ 1`, the cascade gives
`occ + 1 ≥ 2` kills inside the basis, and its escape branches are top decompositions. -/
theorem xbudget_twokill_all {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (hdep : DependsOnF f i) (hnt : ¬TopDecomp f i) (b : Bool) :
    xbudget (restrictF f i b) + 2 ≤ xbudget f := by
  obtain ⟨t, hte, hxf, htv⟩ := Nat.sInf_mem (xbudget_set_nonempty f)
  have htv' : volume t = xbudget f := htv
  obtain ⟨x₁, x₀, hd, hnev⟩ := hdep
  have hvar : hasVar i t = true := by
    apply hasVar_of_depends i t x₁ x₀ (fun c hc => by
      by_contra hcc
      exact hc (hd c hcc))
    rw [show eval t = f from hte]
    exact hnev
  have hocc := hasVar_occ_pos i t hvar
  rcases cascade_collapse_xf i b t hxf with hE | hD | ⟨t', he, hxf', hcase⟩
  · omega
  · exfalso
    apply hnt
    subst hD
    refine ⟨fun a _ => a, fun _ => false, ?_, fun _ _ => rfl⟩
    intro x
    rw [← hte]
    rfl
  · have hcomp : eval t' = restrictF f i b := by
      funext x
      rw [he, substVar_eval, show eval t = f from hte]
      rfl
    have hb : xbudget (restrictF f i b) ≤ volume t' :=
      Nat.sInf_le ⟨t', hcomp, hxf', rfl⟩
    rcases hcase with hA | ⟨hle, hPc | hPu⟩
    · omega
    · exfalso
      apply hnt
      obtain ⟨-, u, hu⟩ := hPc
      refine ⟨fun a _ => u a, fun _ => false, ?_, fun _ _ => rfl⟩
      intro x
      rw [← hte]
      exact hu x
    · exfalso
      apply hnt
      obtain ⟨-, op, s, hshape, hocc₀⟩ := hPu
      rcases hshape with rfl | rfl
      · refine ⟨op, eval s, ?_, ?_⟩
        · intro x
          rw [← hte]
          rfl
        · intro x bb
          exact eval_update_of_hasVar_false i s (occ_zero_hasVar_false i s hocc₀) x bb
      · refine ⟨fun a c => op c a, eval s, ?_, ?_⟩
        · intro x
          rw [← hte]
          rfl
        · intro x bb
          exact eval_update_of_hasVar_false i s (occ_zero_hasVar_false i s hocc₀) x bb

/-- **The composable two-kill chain (proved)**: peels `2·length` off the xor-free budget and keeps the restricted
function's budget on the table for further scheduling. -/
theorem xbudget_twokill_chain {n : ℕ} (steps : List (Fin n × Bool)) :
    ∀ f : (Fin n → Bool) → Bool, TwoKillChain f steps →
      xbudget (restrictAll f steps) + 2 * steps.length ≤ xbudget f := by
  induction steps with
  | nil =>
    intro f _
    show xbudget f + 2 * 0 ≤ xbudget f
    omega
  | cons s rest ih =>
    intro f h
    have h' : DependsOnF f s.1 ∧ ¬TopDecomp f s.1 ∧
        TwoKillChain (restrictF f s.1 s.2) rest := h
    obtain ⟨hdep, hnt, hchain⟩ := h'
    have hkill := xbudget_twokill_all f s.1 hdep hnt s.2
    have hih := ih (restrictF f s.1 s.2) hchain
    show xbudget (restrictAll (restrictF f s.1 s.2) rest) + 2 * (rest.length + 1)
        ≤ xbudget f
    omega

/-! ### The selector chain as a standalone object -/

/-- The full slot-2 selector schedule: every `(c, j)` zeroed. -/
def sat3SelSteps (N : ℕ) : List (Fin N × Bool) :=
  (pairList (List.finRange (sat3M N)) (List.finRange (sat3V N))).map
    (fun p => (sat3S2Sel N p.1 p.2, false))

theorem sat3SelSteps_length (N : ℕ) :
    (sat3SelSteps N).length = sat3M N * sat3V N := by
  show ((pairList (List.finRange (sat3M N)) (List.finRange (sat3V N))).map
    (fun p => (sat3S2Sel N p.1 p.2, false))).length = _
  rw [List.length_map, pairList_length, List.length_finRange, List.length_finRange]

/-- **The selector chain (proved)**: the three-behavior witnesses at every slot-2 selector, packaged as a
`TwoKillChain` — usable by any budget engine. -/
theorem sat3_selector_chain (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    TwoKillChain (sat3Family N) (sat3SelSteps N) := by
  show TwoKillChain (sat3Family N)
    ((pairList (List.finRange (sat3M N)) (List.finRange (sat3V N))).map
      (fun p => (sat3S2Sel N p.1 p.2, false)))
  have hinj : Function.Injective
      (fun p : Fin (sat3M N) × Fin (sat3V N) => sat3S2Sel N p.1 p.2) := by
    intro p q h
    have hd : p.1.val = q.1.val := by
      rw [← sat3S2Sel_div N p.1 p.2, ← sat3S2Sel_div N q.1 q.2]
      exact congrArg (fun bit : Fin N => bit.val / sat3D N) h
    have hrp := sat3S2Sel_rem N p.1 p.2
    have hrq := sat3S2Sel_rem N q.1 q.2
    have hr : p.2.val = q.2.val := by
      have h2 : (sat3S2Sel N p.1 p.2).val % sat3D N
          = (sat3S2Sel N q.1 q.2).val % sat3D N :=
        congrArg (fun bit : Fin N => bit.val % sat3D N) h
      rw [hrp, hrq] at h2
      omega
    exact Prod.ext (Fin.ext hd) (Fin.ext hr)
  have hnd : (((pairList (List.finRange (sat3M N)) (List.finRange (sat3V N))).map
      (fun p => (sat3S2Sel N p.1 p.2, false))).map Prod.fst).Nodup := by
    rw [List.map_map]
    exact (pairList_nodup _ _ (List.nodup_finRange _) (List.nodup_finRange _)).map
      (fun a b hab => hinj (by
        have hab' : (fun p : Fin (sat3M N) × Fin (sat3V N) => sat3S2Sel N p.1 p.2) a
            = (fun p : Fin (sat3M N) × Fin (sat3V N) => sat3S2Sel N p.1 p.2) b := hab
        exact hab'))
  have hprop : ∀ s ∈ (pairList (List.finRange (sat3M N)) (List.finRange (sat3V N))).map
      (fun p => (sat3S2Sel N p.1 p.2, false)), ∃ xP y1 y0 : Fin N → Bool,
      (∀ a, sat3Family N (Function.update xP s.1 a) = a) ∧
      (∀ a, sat3Family N (Function.update y1 s.1 a) = true) ∧
      (∀ a, sat3Family N (Function.update y0 s.1 a) = false) ∧
      (∀ s' ∈ (pairList (List.finRange (sat3M N)) (List.finRange (sat3V N))).map
        (fun p => (sat3S2Sel N p.1 p.2, false)), s'.1 ≠ s.1 →
        xP s'.1 = s'.2 ∧ y1 s'.1 = s'.2 ∧ y0 s'.1 = s'.2) := by
    intro s hs
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hs
    set c' : Fin (sat3M N) := if p.1.val = 0 then ⟨1, hm2⟩ else ⟨0, by omega⟩ with hc'
    have hc'ne : c'.val ≠ p.1.val := by
      rw [hc']
      split
      · next hz =>
          rw [hz]
          show (1 : ℕ) ≠ 0
          omega
      · next hz =>
          show (0 : ℕ) ≠ p.1.val
          omega
    refine ⟨sat3ZBase N p.1, sat3AllLive N, sat3ZBase N c', ?_, ?_, ?_, ?_⟩
    · intro a
      cases a
      · have habs : Function.update (sat3ZBase N p.1) (sat3S2Sel N p.1 p.2) false
            = sat3ZBase N p.1 := by
          rw [← sat3ZBase_s2 N p.1 p.1 p.2]
          exact Function.update_eq_self _ _
        rw [habs]
        exact sat3ZBase_unsat N p.1
      · exact sat3ZBase_flip_sat N hv p.1 p.2
    · intro a
      exact sat3AllLive_flip_sat N hv p.1 p.2 a
    · intro a
      exact sat3ZBase_foreign_unsat N p.1 c' hc'ne p.2 a
    · intro s' hs' hne'
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hs'
      exact ⟨sat3ZBase_s2 N p.1 q.1 q.2, sat3AllLive_s2 N q.1 q.2,
        sat3ZBase_s2 N c' q.1 q.2⟩
  exact twoKillChain_uniform (sat3Family N) _ hnd hprop

/-! ### The orientation contexts avoid slot 2 entirely -/

theorem sat3S2Sel_ne_signBit (N : ℕ) (c₂ : Fin (sat3M N)) (j₂ : Fin (sat3V N))
    (c : Fin (sat3M N)) : sat3S2Sel N c₂ j₂ ≠ sat3SignBit N c := by
  intro h
  have hr2 := sat3S2Sel_rem N c₂ j₂
  rw [h] at hr2
  have hrs : (sat3SignBit N c).val % sat3D N = sat3V N := by
    show (sat3Bit N c ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N = sat3V N
    rw [sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
    omega
  rw [hrs] at hr2
  omega

/-- **Slot 2 is dead in every orientation context (proved)**: the probe lives in slot 0, the pins live in slot 0,
and the tautologies live in slots 0 and 1 — every slot-2 selector reads `false`. -/
theorem sat3_context_s2_false (N : ℕ)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N) (hkv : sat3M N - 2 ≤ sat3V N)
    (c : Fin (sat3M N)) (bvec : Fin (sat3M N - 2) → Bool) (vj : Fin (sat3V N))
    (sgn : Bool) (c₂ : Fin (sat3M N)) (j₂ : Fin (sat3V N)) :
    sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N vj sgn)
      (sat3S2Sel N c₂ j₂) = false := by
  by_cases hc2 : c₂ = c
  · subst hc2
    have h : sat3Patch N c₂ (sat3Context N c₂ hk bvec) (sat3Probe N vj sgn)
        (sat3S2Sel N c₂ j₂) = sat3Probe N vj sgn (sat3S2Sel N c₂ j₂) :=
      sat3Patch_own N c₂ _ _ ⟨2, by omega⟩ j₂.val (by have := j₂.isLt; omega)
    rw [h]
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (hrem | ⟨hrem, -⟩)
    · rw [sat3S2Sel_rem] at hrem
      have := vj.isLt
      omega
    · rw [sat3S2Sel_rem] at hrem
      omega
  · have h : sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N vj sgn)
        (sat3S2Sel N c₂ j₂) = sat3Context N c hk bvec (sat3S2Sel N c₂ j₂) :=
      sat3Patch_out N c _ _ c₂ hc2 ⟨2, by omega⟩ j₂.val (by have := j₂.isLt; omega)
    rw [h]
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro (⟨j, -, hrem⟩ | ⟨-, -, -, hrem⟩)
    · rcases hrem with hrem | ⟨hrem, -⟩
      · rw [sat3S2Sel_rem] at hrem
        have := j.isLt
        omega
      · rw [sat3S2Sel_rem] at hrem
        omega
    · rcases hrem with hrem | hrem | hrem <;> rw [sat3S2Sel_rem] at hrem <;> omega

/-! ### The premise survives the whole interleave -/

/-- **Both orientations after selectors and sign prefix (proved)**: with all slot-2 selectors zeroed and any
interior sign prefix frozen `true`, every remaining interior sign bit forces two reads of every xor-free tree. -/
theorem sat3_interleave_min_occ (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (S : List (Fin (sat3M N))) (hS : ∀ c' ∈ S, 1 ≤ c'.val ∧ c'.val ≤ sat3M N - 2)
    (c : Fin (sat3M N)) (hc1 : 1 ≤ c.val) (hc2 : c.val ≤ sat3M N - 2) (hcS : c ∉ S) :
    ∀ t : Trans N, XorFreeT t →
      eval t = restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S) →
      2 ≤ occCount (sat3SignBit N c) t := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvj
  set bvec₂ : Fin (sat3M N - 2) → Bool :=
    Function.update (fun _ => false) j₀ true with hbvec₂
  have hcomp : ∀ (bvec : Fin (sat3M N - 2) → Bool),
      (∀ j : Fin (sat3M N - 2), 1 ≤ j.val → bvec j = false) → ∀ a : Bool,
      ∀ p ∈ sat3SelSteps N ++ sat3SignFreeze N S,
        Function.update (sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N vj false))
          (sat3SignBit N c) a p.1 = p.2 := by
    intro bvec hbv a p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
      show Function.update (sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N vj false))
        (sat3SignBit N c) a (sat3S2Sel N q.1 q.2) = false
      rw [Function.update_of_ne (sat3S2Sel_ne_signBit N q.1 q.2 c)]
      exact sat3_context_s2_false N hk hkv c bvec vj false q.1 q.2
    · obtain ⟨c', hc'S, rfl⟩ := List.mem_map.mp hp
      obtain ⟨hc'1, hc'2⟩ := hS c' hc'S
      have hnec : c' ≠ c := fun h => hcS (h ▸ hc'S)
      show Function.update (sat3Patch N c (sat3Context N c hk bvec) (sat3Probe N vj false))
        (sat3SignBit N c) a (sat3SignBit N c') = true
      rw [Function.update_of_ne (sat3SignBit_ne N hnec)]
      exact sat3_freeze_compliant N hk hkv c c' hnec hc1 hc2 hc'1 hc'2 bvec hbv _
  have hbvA : ∀ j : Fin (sat3M N - 2), 1 ≤ j.val →
      (fun _ : Fin (sat3M N - 2) => false) j = false := fun j _ => rfl
  have hbvB : ∀ j : Fin (sat3M N - 2), 1 ≤ j.val → bvec₂ j = false := by
    intro j hj
    have hne : j ≠ j₀ := by
      rw [hj₀]
      intro he
      have hval : j.val = 0 := congrArg Fin.val he
      omega
    rw [hbvec₂]
    rw [Function.update_of_ne hne]
  have hbeh₁ : ∀ a : Bool,
      restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S)
        (Function.update (sat3Patch N c (sat3Context N c hk (fun _ => false))
          (sat3Probe N vj false)) (sat3SignBit N c) a) = a := by
    intro a
    rw [restrictAll_agree _ _ _ (hcomp (fun _ => false) hbvA a), patch_probe_update]
    have hval := sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl a
    rw [hval]
    cases a <;> rfl
  have hbeh₂ : ∀ a : Bool,
      restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S)
        (Function.update (sat3Patch N c (sat3Context N c hk bvec₂)
          (sat3Probe N vj false)) (sat3SignBit N c) a) = !a := by
    intro a
    rw [restrictAll_agree _ _ _ (hcomp bvec₂ hbvB a), patch_probe_update]
    have hval := sat3Context_probe_eval N hv hk hkv c bvec₂ j₀ vj rfl a
    rw [hval]
    have hb : bvec₂ j₀ = true := by
      rw [hbvec₂, Function.update_self]
    rw [hb]
    cases a <;> rfl
  intro t hxf hte
  refine xorfree_min_occ_of_orientations
    (restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S)) (sat3SignBit N c)
    (sat3Patch N c (sat3Context N c hk (fun _ => false)) (sat3Probe N vj false))
    (sat3Patch N c (sat3Context N c hk bvec₂) (sat3Probe N vj false))
    ?_ ?_ ?_ t hxf hte
  · rw [hbeh₁ true, hbeh₁ false]
    decide
  · rw [hbeh₂ true, hbeh₂ false]
    decide
  · rw [hbeh₁ true, hbeh₂ true]
    decide

/-! ### The sign chain on top of the zeroed selectors -/

theorem sat3_interleave_sign_chain (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N) :
    ∀ (L S : List (Fin (sat3M N))),
      (∀ c ∈ S, 1 ≤ c.val ∧ c.val ≤ sat3M N - 2) →
      (∀ c ∈ L, 1 ≤ c.val ∧ c.val ≤ sat3M N - 2) →
      (∀ c ∈ L, c ∉ S) → L.Nodup →
      3 * L.length + 1
        ≤ xbudget (restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S)) := by
  intro L
  induction L with
  | nil =>
    intro S hS hL hLS hnd
    have h := xbudget_pos
      (restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S))
    have hlen : ([] : List (Fin (sat3M N))).length = 0 := rfl
    rw [hlen]
    omega
  | cons c L' ih =>
    intro S hS hL hLS hnd
    have hc := hL c List.mem_cons_self
    have hcS : c ∉ S := hLS c List.mem_cons_self
    have hstep := xbudget_threekill_of_min_occ
      (restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S))
      (sat3SignBit N c)
      (sat3_interleave_min_occ N hv hm3 S hS c hc.1 hc.2 hcS) true
    have hres : restrictF
        (restrictAll (sat3Family N) (sat3SelSteps N ++ sat3SignFreeze N S))
        (sat3SignBit N c) true
        = restrictAll (sat3Family N)
            (sat3SelSteps N ++ sat3SignFreeze N (S ++ [c])) := by
      rw [sat3SignFreeze_append, ← List.append_assoc,
        restrictAll_append (sat3SelSteps N ++ sat3SignFreeze N S)
          (sat3SignFreeze N [c]) (sat3Family N)]
      rfl
    rw [hres] at hstep
    have hS' : ∀ c' ∈ S ++ [c], 1 ≤ c'.val ∧ c'.val ≤ sat3M N - 2 := by
      intro c' hc'
      rcases List.mem_append.mp hc' with h | h
      · exact hS c' h
      · rw [List.mem_singleton] at h
        exact h ▸ hc
    have hL' : ∀ c' ∈ L', 1 ≤ c'.val ∧ c'.val ≤ sat3M N - 2 :=
      fun c' hc' => hL c' (List.mem_cons_of_mem c hc')
    have hLS' : ∀ c' ∈ L', c' ∉ S ++ [c] := by
      intro c' hc' hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hLS c' (List.mem_cons_of_mem c hc') h
      · rw [List.mem_singleton] at h
        subst h
        exact (List.nodup_cons.mp hnd).1 hc'
    have hnd' : L'.Nodup := (List.nodup_cons.mp hnd).2
    have hih := ih (S ++ [c]) hS' hL' hLS' hnd'
    show 3 * (L'.length + 1) + 1 ≤ _
    omega

/-! ### The record -/

/-- **THE INTERLEAVED XOR-FREE SCHEDULE (proved)**: `2·(m·v) + 3·(m−2) + 1 ≤ xbudget (sat3Family N)` — the
selector two-kills and the sign-bit three-kills compose in one budget, strictly beating the transferred
general-basis record `2·m·v + 1`. -/
theorem sat3_xorfree_interleaved_schedule (N : ℕ) (hv : 1 ≤ sat3V N)
    (hm3 : 3 ≤ sat3M N) :
    2 * (sat3M N * sat3V N) + 3 * (sat3M N - 2) + 1 ≤ xbudget (sat3Family N) := by
  have hchain := sat3_selector_chain N hv (by omega)
  have h2 := xbudget_twokill_chain (sat3SelSteps N) (sat3Family N) hchain
  rw [sat3SelSteps_length] at h2
  have hinj : Function.Injective
      (fun j : Fin (sat3M N - 2) =>
        (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (sat3M N))) := by
    intro j j' h
    have hval : j.val + 1 = j'.val + 1 := congrArg Fin.val h
    exact Fin.ext (by omega)
  have h3 := sat3_interleave_sign_chain N hv hm3
    ((List.finRange (sat3M N - 2)).map
      (fun j : Fin (sat3M N - 2) =>
        (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin (sat3M N))))
    []
    (fun c hc => absurd hc List.not_mem_nil)
    (by
      intro c hc
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
      have := j.isLt
      constructor
      · show 1 ≤ j.val + 1
        omega
      · show j.val + 1 ≤ sat3M N - 2
        omega)
    (fun c _ hc => absurd hc List.not_mem_nil)
    ((List.nodup_finRange _).map hinj)
  rw [List.length_map, List.length_finRange] at h3
  have hnil : sat3SelSteps N ++ sat3SignFreeze N ([] : List (Fin (sat3M N)))
      = sat3SelSteps N := List.append_nil _
  rw [hnil] at h3
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.xbudget_twokill_all
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.xbudget_twokill_chain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_chain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_context_s2_false
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_interleave_min_occ
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_interleave_sign_chain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_xorfree_interleaved_schedule
