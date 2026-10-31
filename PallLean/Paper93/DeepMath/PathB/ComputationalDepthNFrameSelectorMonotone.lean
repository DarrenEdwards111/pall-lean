import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameXorFreeInterleave

/-!
# N-Frame: the selector-monotonicity no-go — the orientation route's ceiling is a theorem

The interleaved schedule's honest-scope note claimed the three-kill is *confined* to sign bits because sat3 is
monotone in every selector coordinate.  This file makes that a theorem — the exact anatomy of which coordinates
the polarity route can and cannot read:

  `sat3Eval_selector_mono` / `sat3Family_selector_mono` — **PROVED**: turning any selector on (any clause, any
        of the three slots, any variable index) can only help satisfiability — the slot value is an OR of
        `sel ∧ (a ⊕ sign)` terms, the flipped bit is never a sign bit (field residues mod `v+1` differ), and the
        same witness term survives.
  `sat3_selector_no_orientation_clash` — **PROVED, the no-go**: the two-orientation hypothesis package — exactly
        the hypotheses of `xorfree_min_occ_of_orientations` — is *unsatisfiable* at every one of the `3·m·v`
        selector coordinates: every sensitive point orients `true`.
  `sat3_sign_orientation_clash` — **PROVED, the contrast**: at every slot-0 sign bit the package *is* satisfied
        (the identity and negation contexts of the min-occ theorem).
  `sat3_orientation_dichotomy` — **PROVED, the anatomy**: both statements packaged — clash at every slot-0 sign
        bit, clash at no selector bit.

## Honest scope

This closes the *route*, not the question: the polarity-clash mechanism provably cannot force `min-occ ≥ 2` at
any selector coordinate, so orientation-based three-kills stop at `Θ(m) ≈ √N/3` of the `N` coordinates — the
interleave record `2·m·v + 3·(m−2) + 1` is this route's ceiling shape at tree level.  It is **not** claimed that
`min-occ ≥ 2` outright fails at selectors (that would require exhibiting a single-read xor-free tree for the whole
family), nor anything about the `2·m` slot-1/2 sign bits (the probe machinery is slot-0; they are simply not
needed).  Going past the ceiling needs a genuinely different premise — or the DAG observer.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The selector bit for variable `j` in slot `t` of clause `c` (field `j < v`). -/
def sat3SelBit (N : ℕ) (c : Fin (sat3M N)) (t : Fin 3) (j : Fin (sat3V N)) : Fin N :=
  sat3Bit N c t j.val (by have := j.isLt; omega)

/-- No sign bit is a selector bit: their field residues mod `v+1` are `v` and `j < v`. -/
theorem sat3_signbit_ne_selbit (N : ℕ) (cl c₀ : Fin (sat3M N)) (t t₀ : Fin 3)
    (j₀ : Fin (sat3V N)) :
    sat3Bit N cl t (sat3V N) (by omega) ≠ sat3SelBit N c₀ t₀ j₀ := by
  intro h
  have h1 := sat3Bit_rem N cl t (sat3V N) (by omega)
  rw [h] at h1
  have h2 : (sat3SelBit N c₀ t₀ j₀).val % sat3D N
      = t₀.val * (sat3V N + 1) + j₀.val := by
    show (sat3Bit N c₀ t₀ j₀.val (by have := j₀.isLt; omega)).val % sat3D N = _
    rw [sat3Bit_rem]
  rw [h2] at h1
  have h1' : (sat3V N + 1) * t₀.val + j₀.val = (sat3V N + 1) * t.val + sat3V N := by
    rw [Nat.mul_comm (sat3V N + 1) t₀.val, Nat.mul_comm (sat3V N + 1) t.val]
    exact h1
  have h4 : j₀.val % (sat3V N + 1) = sat3V N % (sat3V N + 1) := by
    rw [← Nat.mul_add_mod (sat3V N + 1) t₀.val j₀.val,
      ← Nat.mul_add_mod (sat3V N + 1) t.val (sat3V N), h1']
  rw [Nat.mod_eq_of_lt (by have := j₀.isLt; omega),
    Nat.mod_eq_of_lt (by omega)] at h4
  have := j₀.isLt
  omega

/-! ### Monotonicity: a selector can only help -/

/-- **Evaluation is monotone in every selector (proved)**: the satisfied witness term survives the flip — its
selector reads `true` either way, and its sign bit is untouched. -/
theorem sat3Eval_selector_mono (N : ℕ) (c₀ : Fin (sat3M N)) (t₀ : Fin 3)
    (j₀ : Fin (sat3V N)) (x : Fin N → Bool) (a : Fin (sat3V N) → Bool)
    (h : sat3Eval N (Function.update x (sat3SelBit N c₀ t₀ j₀) false) a = true) :
    sat3Eval N (Function.update x (sat3SelBit N c₀ t₀ j₀) true) a = true := by
  apply List.all_eq_true.mpr
  intro cl _
  have hall := List.all_eq_true.mp h cl (List.mem_finRange cl)
  obtain ⟨t, -, ht⟩ := List.any_eq_true.mp hall
  apply List.any_eq_true.mpr
  refine ⟨t, List.mem_finRange t, ?_⟩
  show sat3Lit N (Function.update x (sat3SelBit N c₀ t₀ j₀) true) a cl t = true
  have ht' : sat3Lit N (Function.update x (sat3SelBit N c₀ t₀ j₀) false) a cl t = true := ht
  unfold sat3Lit at ht' ⊢
  obtain ⟨jv, -, hterm⟩ := List.any_eq_true.mp ht'
  apply List.any_eq_true.mpr
  refine ⟨jv, List.mem_finRange jv, ?_⟩
  have hterm' : (Function.update x (sat3SelBit N c₀ t₀ j₀) false
        (sat3Bit N cl t jv.val (by have := jv.isLt; omega))
      && Bool.xor (a jv) (Function.update x (sat3SelBit N c₀ t₀ j₀) false
        (sat3Bit N cl t (sat3V N) (by omega)))) = true := hterm
  rw [Bool.and_eq_true] at hterm'
  obtain ⟨hsel0, hlit0⟩ := hterm'
  show (Function.update x (sat3SelBit N c₀ t₀ j₀) true
        (sat3Bit N cl t jv.val (by have := jv.isLt; omega))
      && Bool.xor (a jv) (Function.update x (sat3SelBit N c₀ t₀ j₀) true
        (sat3Bit N cl t (sat3V N) (by omega)))) = true
  have hs_ne := sat3_signbit_ne_selbit N cl c₀ t t₀ j₀
  have hsign1 : Function.update x (sat3SelBit N c₀ t₀ j₀) true
        (sat3Bit N cl t (sat3V N) (by omega))
      = Function.update x (sat3SelBit N c₀ t₀ j₀) false
        (sat3Bit N cl t (sat3V N) (by omega)) := by
    rw [Function.update_of_ne hs_ne, Function.update_of_ne hs_ne]
  have hsel1 : Function.update x (sat3SelBit N c₀ t₀ j₀) true
      (sat3Bit N cl t jv.val (by have := jv.isLt; omega)) = true := by
    by_cases hbe : sat3Bit N cl t jv.val (by have := jv.isLt; omega)
        = sat3SelBit N c₀ t₀ j₀
    · rw [hbe, Function.update_self]
    · rw [Function.update_of_ne hbe]
      rw [Function.update_of_ne hbe] at hsel0
      exact hsel0
  rw [hsel1, hsign1, hlit0]
  rfl

/-- **The family is monotone in every selector (proved).** -/
theorem sat3Family_selector_mono (N : ℕ) (c₀ : Fin (sat3M N)) (t₀ : Fin 3)
    (j₀ : Fin (sat3V N)) (x : Fin N → Bool)
    (h : sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) false) = true) :
    sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) true) = true := by
  obtain ⟨a, ha⟩ := (sat3Family_iff N _).mp h
  exact sat3Family_of_witness N _ a (sat3Eval_selector_mono N c₀ t₀ j₀ x a ha)

/-! ### The no-go and the contrast -/

/-- Every sensitive point of a selector coordinate orients `true`. -/
theorem sat3_selector_orientation_true (N : ℕ) (c₀ : Fin (sat3M N)) (t₀ : Fin 3)
    (j₀ : Fin (sat3V N)) (x : Fin N → Bool)
    (hs : sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) true)
        ≠ sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) false)) :
    sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) true) = true := by
  cases h1 : sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) true)
  · exfalso
    cases h0 : sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) false)
    · exact hs (h1.trans h0.symm)
    · have hmono := sat3Family_selector_mono N c₀ t₀ j₀ x h0
      exact Bool.noConfusion (h1.symm.trans hmono)
  · rfl

/-- **THE NO-GO (proved)**: the two-orientation hypothesis package — exactly the hypotheses of
`xorfree_min_occ_of_orientations` — is unsatisfiable at every selector coordinate. -/
theorem sat3_selector_no_orientation_clash (N : ℕ) (c₀ : Fin (sat3M N)) (t₀ : Fin 3)
    (j₀ : Fin (sat3V N)) :
    ¬ ∃ x y : Fin N → Bool,
      (sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) true)
        ≠ sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) false)) ∧
      (sat3Family N (Function.update y (sat3SelBit N c₀ t₀ j₀) true)
        ≠ sat3Family N (Function.update y (sat3SelBit N c₀ t₀ j₀) false)) ∧
      (sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) true)
        ≠ sat3Family N (Function.update y (sat3SelBit N c₀ t₀ j₀) true)) := by
  rintro ⟨x, y, hsx, hsy, hxy⟩
  apply hxy
  rw [sat3_selector_orientation_true N c₀ t₀ j₀ x hsx,
    sat3_selector_orientation_true N c₀ t₀ j₀ y hsy]

/-- **The contrast (proved)**: at every slot-0 sign bit the package is satisfied — the identity and negation
contexts of the min-occurrence theorem. -/
theorem sat3_sign_orientation_clash (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (c : Fin (sat3M N)) :
    ∃ x y : Fin N → Bool,
      (sat3Family N (Function.update x (sat3SignBit N c) true)
        ≠ sat3Family N (Function.update x (sat3SignBit N c) false)) ∧
      (sat3Family N (Function.update y (sat3SignBit N c) true)
        ≠ sat3Family N (Function.update y (sat3SignBit N c) false)) ∧
      (sat3Family N (Function.update x (sat3SignBit N c) true)
        ≠ sat3Family N (Function.update y (sat3SignBit N c) true)) := by
  have hk : (sat3M N - 2) + 1 ≤ sat3M N := by omega
  have hkv : sat3M N - 2 ≤ sat3V N := by
    have := sat3M_pred_le_sat3V N
    omega
  set j₀ : Fin (sat3M N - 2) := ⟨0, by omega⟩ with hj₀
  set vj : Fin (sat3V N) := ⟨0, hv⟩ with hvj
  set bvec₂ : Fin (sat3M N - 2) → Bool :=
    Function.update (fun _ => false) j₀ true with hbvec₂
  have hbeh₁ : ∀ a : Bool,
      sat3Family N (Function.update (sat3Patch N c (sat3Context N c hk (fun _ => false))
        (sat3Probe N vj false)) (sat3SignBit N c) a) = a := by
    intro a
    rw [patch_probe_update]
    have hval := sat3Context_probe_eval N hv hk hkv c (fun _ => false) j₀ vj rfl a
    rw [hval]
    cases a <;> rfl
  have hbeh₂ : ∀ a : Bool,
      sat3Family N (Function.update (sat3Patch N c (sat3Context N c hk bvec₂)
        (sat3Probe N vj false)) (sat3SignBit N c) a) = !a := by
    intro a
    rw [patch_probe_update]
    have hval := sat3Context_probe_eval N hv hk hkv c bvec₂ j₀ vj rfl a
    rw [hval]
    have hb : bvec₂ j₀ = true := by
      rw [hbvec₂, Function.update_self]
    rw [hb]
    cases a <;> rfl
  refine ⟨sat3Patch N c (sat3Context N c hk (fun _ => false)) (sat3Probe N vj false),
    sat3Patch N c (sat3Context N c hk bvec₂) (sat3Probe N vj false), ?_, ?_, ?_⟩
  · rw [hbeh₁ true, hbeh₁ false]
    decide
  · rw [hbeh₂ true, hbeh₂ false]
    decide
  · rw [hbeh₁ true, hbeh₂ true]
    decide

/-- **THE ANATOMY (proved)**: the orientation clash lives at every slot-0 sign bit and at no selector bit — the
polarity route reads `Θ(m)` of the `N` coordinates, and the interleave record is its ceiling shape. -/
theorem sat3_orientation_dichotomy (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N) :
    (∀ c : Fin (sat3M N), ∃ x y : Fin N → Bool,
      (sat3Family N (Function.update x (sat3SignBit N c) true)
        ≠ sat3Family N (Function.update x (sat3SignBit N c) false)) ∧
      (sat3Family N (Function.update y (sat3SignBit N c) true)
        ≠ sat3Family N (Function.update y (sat3SignBit N c) false)) ∧
      (sat3Family N (Function.update x (sat3SignBit N c) true)
        ≠ sat3Family N (Function.update y (sat3SignBit N c) true))) ∧
    (∀ (c₀ : Fin (sat3M N)) (t₀ : Fin 3) (j₀ : Fin (sat3V N)),
      ¬ ∃ x y : Fin N → Bool,
      (sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) true)
        ≠ sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) false)) ∧
      (sat3Family N (Function.update y (sat3SelBit N c₀ t₀ j₀) true)
        ≠ sat3Family N (Function.update y (sat3SelBit N c₀ t₀ j₀) false)) ∧
      (sat3Family N (Function.update x (sat3SelBit N c₀ t₀ j₀) true)
        ≠ sat3Family N (Function.update y (sat3SelBit N c₀ t₀ j₀) true))) :=
  ⟨fun c => sat3_sign_orientation_clash N hv hm3 c,
   fun c₀ t₀ j₀ => sat3_selector_no_orientation_clash N c₀ t₀ j₀⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Eval_selector_mono
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3Family_selector_mono
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_no_orientation_clash
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_orientation_clash
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_orientation_dichotomy
