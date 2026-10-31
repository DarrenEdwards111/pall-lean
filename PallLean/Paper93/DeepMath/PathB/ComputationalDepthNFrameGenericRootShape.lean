import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameGenericWireCut
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameParityEssStd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRootShape

/-!
# N-Frame: the generic root shape — condition (iii) closed

Work package 1 of the checklist (… → standard essentials → **generic root shape**).  The
sat3-specific semantic kills of the root-shape argument are replaced by ONE generic kill —
two distinct essential variables — and the whole reduction becomes family-independent:

  `not_unary_of_two_essential` — **PROVED, the generic kill**: a function with two distinct
        essential variables is not a unary function of any single coordinate.
  `pseudo_unary_kill_of_two_essential` — **PROVED, the generic dispatcher**: the output is
        not a unary `F` of the wire at `length − 2` (every gate shape there dies — `var` and
        `cst` by the kill, `un` by `minimal_un_last`, `bin` by `shrink_last_two`).
  `root_shape_of_two_essential` — **PROVED, GENERIC**: a minimal circuit computing any
        function with two distinct essential variables has a proper binary root.
  `parity_root_shape` — **PROVED**: instantiated at the standard-codebook parity family via
        `parity_essential_std` (positions `(e_{j₀}, 0)` and `(e_{j₀}, 1)` of block `0`).
  `parity_balanced_cut` — **PROVED, CONDITION (iii) CLOSED**: balanced cuts with width
        `≤ coneExcess + 1` at every band, for the parity family, unconditionally.

## Honest scope

With this, the headline's `hj`/cut package is supplied unconditionally: the remaining named
conditions are the drag-side codebook glue and the liveness/kill-accounting (the expander
long-pole).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- **The generic kill (proved)**: two distinct essential variables forbid unary form. -/
theorem not_unary_of_two_essential {n : ℕ} (f : (Fin n → Bool) → Bool)
    (p q : Fin n) (hpq : p ≠ q)
    (hessp : ∃ x₁ x₀ : Fin n → Bool, (∀ b, x₁ b ≠ x₀ b → b = p) ∧ f x₁ ≠ f x₀)
    (hessq : ∃ x₁ x₀ : Fin n → Bool, (∀ b, x₁ b ≠ x₀ b → b = q) ∧ f x₁ ≠ f x₀)
    (i : Fin n) (σ : Bool → Bool) :
    ¬ ∀ x : Fin n → Bool, f x = σ (x i) := by
  intro hσ
  rcases Classical.em (p = i) with hpi | hpi
  · obtain ⟨x₁, x₀, hd, hne⟩ := hessq
    apply hne
    rw [hσ x₁, hσ x₀]
    congr 1
    by_contra hxi
    apply hpq
    rw [hpi, hd i hxi]
  · obtain ⟨x₁, x₀, hd, hne⟩ := hessp
    apply hne
    rw [hσ x₁, hσ x₀]
    congr 1
    by_contra hxi
    exact hpi (hd i hxi).symm

theorem nonconstant_of_essential {n : ℕ} (f : (Fin n → Bool) → Bool)
    (p : Fin n)
    (hessp : ∃ x₁ x₀ : Fin n → Bool, (∀ b, x₁ b ≠ x₀ b → b = p) ∧ f x₁ ≠ f x₀) :
    ∃ u w : Fin n → Bool, f u ≠ f w := by
  obtain ⟨x₁, x₀, -, hne⟩ := hessp
  exact ⟨x₁, x₀, hne⟩

/-- **The generic dispatcher (proved)**: the output is not a unary `F` of the wire at
`length − 2`. -/
theorem pseudo_unary_kill_of_two_essential {n : ℕ} (f : (Fin n → Bool) → Bool)
    (p q : Fin n) (hpq : p ≠ q)
    (hessp : ∃ x₁ x₀ : Fin n → Bool, (∀ b, x₁ b ≠ x₀ b → b = p) ∧ f x₁ ≠ f x₀)
    (hessq : ∃ x₁ x₀ : Fin n → Bool, (∀ b, x₁ b ≠ x₀ b → b = q) ∧ f x₁ ≠ f x₀)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f)
    (hlen2 : 2 ≤ c.length) (F : Bool → Bool)
    (hsem : ∀ x, f x = F ((runFrom x [] c).getD (c.length - 2) false)) : False := by
  cases hg2 : c.getD (c.length - 2) (CGate.cst false) with
  | var i =>
    exact not_unary_of_two_essential f p q hpq hessp hessq i F
      (fun x => by rw [hsem x, wire_val_var c (c.length - 2) i hg2 x])
  | cst b =>
    apply not_unary_of_two_essential f p q hpq hessp hessq p (fun _ => F b)
    intro x
    rw [hsem x]
    have hw : (runFrom x [] c).getD (c.length - 2) false = b := by
      rw [output_getD_at x c (c.length - 2) (by omega), hg2]
      rfl
    rw [hw]
  | un op₂ j =>
    have hnc := nonconstant_of_essential f p hessp
    have h := minimal_un_last f c hcomp hmin hnc (c.length - 2) op₂ j hg2 (by omega)
    omega
  | bin op₂ j k =>
    exact shrink_last_two f c hcomp hmin hlen2 op₂ j k hg2 F hsem

set_option maxHeartbeats 1600000 in
/-- **THE GENERIC ROOT SHAPE (proved)**: a minimal circuit computing a function with two
distinct essential variables has a proper binary root. -/
theorem root_shape_of_two_essential {n : ℕ} (f : (Fin n → Bool) → Bool)
    (p q : Fin n) (hpq : p ≠ q)
    (hessp : ∃ x₁ x₀ : Fin n → Bool, (∀ b, x₁ b ≠ x₀ b → b = p) ∧ f x₁ ≠ f x₀)
    (hessq : ∃ x₁ x₀ : Fin n → Bool, (∀ b, x₁ b ≠ x₀ b → b = q) ∧ f x₁ ≠ f x₀)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f) :
    ∃ (op : Bool → Bool → Bool) (L R : ℕ),
      c.getD (c.length - 1) (CGate.cst false) = CGate.bin op L R ∧
      L < c.length - 1 ∧ R < c.length - 1 ∧ L ≠ R := by
  by_cases hcnil : c = []
  · exfalso
    apply not_unary_of_two_essential f p q hpq hessp hessq p (fun _ => false)
    intro x
    rw [← hcomp x, hcnil]
    rfl
  have hcpos : 0 < c.length :=
    Nat.pos_of_ne_zero (fun h => hcnil (List.eq_nil_of_length_eq_zero h))
  have hout : ∀ x, f x
      = evalGate x (runFrom x [] (c.take (c.length - 1)))
          (c.getD (c.length - 1) (CGate.cst false)) := by
    intro x
    have h : (runFrom x [] c).getD (c.length - 1) false = f x := hcomp x
    rw [← h, output_getD_at x c (c.length - 1) (by omega)]
  have hplen : ∀ x : Fin n → Bool,
      (runFrom x [] (c.take (c.length - 1))).length = c.length - 1 := by
    intro x
    rw [runFrom_length]
    simp only [List.length_nil, List.length_take]
    omega
  cases hg : c.getD (c.length - 1) (CGate.cst false) with
  | var i =>
    exfalso
    apply not_unary_of_two_essential f p q hpq hessp hessq i (fun b => b)
    intro x
    rw [hout x, hg]
    rfl
  | cst b =>
    exfalso
    apply not_unary_of_two_essential f p q hpq hessp hessq p (fun _ => b)
    intro x
    rw [hout x, hg]
    rfl
  | un op' L =>
    exfalso
    by_cases hL : L < c.length - 1
    · have hlen2 : 2 ≤ c.length := by omega
      obtain ⟨q', hq', hread⟩ := minimal_wire_read f c hcomp hmin
        (c.length - 2) (by omega)
      have hqlt : q' < c.length := by
        rcases Nat.lt_or_ge q' c.length with h | h
        · exact h
        · exfalso
          rw [List.getD_eq_default _ _ h] at hread
          have hfa : readsWire (c.length - 2) (CGate.cst false : CGate n) = false := rfl
          rw [hfa] at hread
          simp at hread
      have hqroot : q' = c.length - 1 := by omega
      rw [hqroot, hg] at hread
      have hLeq : L = c.length - 2 := by
        have h' : (L == c.length - 2) = true := hread
        simpa using h'
      apply pseudo_unary_kill_of_two_essential f p q hpq hessp hessq
        c hcomp hmin hlen2 op'
      intro x
      rw [hout x, hg]
      show op' ((runFrom x [] (c.take (c.length - 1))).getD L false) = _
      rw [hLeq, takeRun_getD_eq c x (c.length - 1) (c.length - 2) (by omega) (by omega)]
    · apply not_unary_of_two_essential f p q hpq hessp hessq p (fun _ => op' false)
      intro x
      rw [hout x, hg]
      show op' ((runFrom x [] (c.take (c.length - 1))).getD L false) = op' false
      rw [List.getD_eq_default _ _ (by rw [hplen x]; omega)]
  | bin op L R =>
    by_cases hL : L < c.length - 1
    · by_cases hR : R < c.length - 1
      · by_cases hLR : L = R
        · exfalso
          subst hLR
          have hlen2 : 2 ≤ c.length := by omega
          obtain ⟨q', hq', hread⟩ := minimal_wire_read f c hcomp hmin
            (c.length - 2) (by omega)
          have hqlt : q' < c.length := by
            rcases Nat.lt_or_ge q' c.length with h | h
            · exact h
            · exfalso
              rw [List.getD_eq_default _ _ h] at hread
              have hfa : readsWire (c.length - 2) (CGate.cst false : CGate n) = false := rfl
              rw [hfa] at hread
              simp at hread
          have hqroot : q' = c.length - 1 := by omega
          rw [hqroot, hg] at hread
          have hLeq : L = c.length - 2 := by
            have h' : (L == c.length - 2 || L == c.length - 2) = true := hread
            simp at h'
            exact h'
          apply pseudo_unary_kill_of_two_essential f p q hpq hessp hessq
            c hcomp hmin hlen2 (fun b => op b b)
          intro x
          rw [hout x, hg]
          show op ((runFrom x [] (c.take (c.length - 1))).getD L false)
              ((runFrom x [] (c.take (c.length - 1))).getD L false) = _
          rw [hLeq, takeRun_getD_eq c x (c.length - 1) (c.length - 2) (by omega) (by omega)]
        · exact ⟨op, L, R, rfl, hL, hR, hLR⟩
      · exfalso
        have hlen2 : 2 ≤ c.length := by omega
        obtain ⟨q', hq', hread⟩ := minimal_wire_read f c hcomp hmin
          (c.length - 2) (by omega)
        have hqlt : q' < c.length := by
          rcases Nat.lt_or_ge q' c.length with h | h
          · exact h
          · exfalso
            rw [List.getD_eq_default _ _ h] at hread
            have hfa : readsWire (c.length - 2) (CGate.cst false : CGate n) = false := rfl
            rw [hfa] at hread
            simp at hread
        have hqroot : q' = c.length - 1 := by omega
        rw [hqroot, hg] at hread
        have hLeq : L = c.length - 2 := by
          have h' : (L == c.length - 2 || R == c.length - 2) = true := hread
          simp at h'
          rcases h' with h' | h'
          · exact h'
          · omega
        apply pseudo_unary_kill_of_two_essential f p q hpq hessp hessq
          c hcomp hmin hlen2 (fun b => op b false)
        intro x
        rw [hout x, hg]
        show op ((runFrom x [] (c.take (c.length - 1))).getD L false)
            ((runFrom x [] (c.take (c.length - 1))).getD R false) = _
        rw [List.getD_eq_default _ _ (show (runFrom x [] (c.take (c.length - 1))).length ≤ R
          from by rw [hplen x]; omega)]
        rw [hLeq, takeRun_getD_eq c x (c.length - 1) (c.length - 2) (by omega) (by omega)]
    · by_cases hR : R < c.length - 1
      · exfalso
        have hlen2 : 2 ≤ c.length := by omega
        obtain ⟨q', hq', hread⟩ := minimal_wire_read f c hcomp hmin
          (c.length - 2) (by omega)
        have hqlt : q' < c.length := by
          rcases Nat.lt_or_ge q' c.length with h | h
          · exact h
          · exfalso
            rw [List.getD_eq_default _ _ h] at hread
            have hfa : readsWire (c.length - 2) (CGate.cst false : CGate n) = false := rfl
            rw [hfa] at hread
            simp at hread
        have hqroot : q' = c.length - 1 := by omega
        rw [hqroot, hg] at hread
        have hReq : R = c.length - 2 := by
          have h' : (L == c.length - 2 || R == c.length - 2) = true := hread
          simp at h'
          rcases h' with h' | h'
          · omega
          · exact h'
        apply pseudo_unary_kill_of_two_essential f p q hpq hessp hessq
          c hcomp hmin hlen2 (fun b => op false b)
        intro x
        rw [hout x, hg]
        show op ((runFrom x [] (c.take (c.length - 1))).getD L false)
            ((runFrom x [] (c.take (c.length - 1))).getD R false) = _
        rw [List.getD_eq_default _ _ (show (runFrom x [] (c.take (c.length - 1))).length ≤ L
          from by rw [hplen x]; omega)]
        rw [hReq, takeRun_getD_eq c x (c.length - 1) (c.length - 2) (by omega) (by omega)]
      · exfalso
        apply not_unary_of_two_essential f p q hpq hessp hessq p
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

namespace PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open PallLean.Paper93.DeepMath.PathB.NFrameParityLayout
open PallLean.Paper93.DeepMath.PathB.NFrameParityCodebook
open PallLean.Paper93.DeepMath.PathB.NFrameParityStdCode

variable {v m N : ℕ}

/-- **The parity root shape (proved, unconditional)**: a minimal circuit computing the
standard-codebook parity family has a proper binary root. -/
theorem parity_root_shape (hv : 0 < v) (hm : 0 < m) (hfit : m * stdL v ≤ N)
    (c : List (CGate N))
    (hcomp : computes c (parityFamilyBits (stdCode v hv) hfit))
    (hmin : c.length = cbudget (parityFamilyBits (stdCode v hv) hfit)) :
    ∃ (op : Bool → Bool → Bool) (L R : ℕ),
      c.getD (c.length - 1) (CGate.cst false) = CGate.bin op L R ∧
      L < c.length - 1 ∧ R < c.length - 1 ∧ L ≠ R := by
  have hp := parity_essential_std hv hfit ⟨0, hm⟩ ⟨0, hv⟩ 0
  have hq := parity_essential_std hv hfit ⟨0, hm⟩ ⟨0, hv⟩ 1
  have hpq : xbit hfit ⟨0, hm⟩ (sIdx v ⟨0, hv⟩ 0)
      ≠ xbit hfit ⟨0, hm⟩ (sIdx v ⟨0, hv⟩ 1) := by
    intro h
    have h2 := (sIdx_inj v (xbit_inj hfit h).2).2
    exact absurd h2 (by decide)
  exact root_shape_of_two_essential (parityFamilyBits (stdCode v hv) hfit)
    _ _ hpq hp hq c hcomp hmin

/-- **CONDITION (iii) CLOSED (proved)**: balanced cuts with width `≤ coneExcess + 1` at
every band, for the standard-codebook parity family, unconditionally. -/
theorem parity_balanced_cut (hv : 0 < v) (hm : 0 < m) (hfit : m * stdL v ≤ N)
    (c : List (CGate N))
    (hcomp : computes c (parityFamilyBits (stdCode v hv) hfit))
    (hmin : c.length = cbudget (parityFamilyBits (stdCode v hv) hfit))
    (T : ℕ) (hT : 2 ≤ T)
    (hband : 2 * T - 1 ≤ (varsOf c (c.length - 1)).card) :
    ∃ S : Finset (Fin N), T ≤ S.card ∧ S.card ≤ 2 * T - 2
    ∧ ∃ j : ℕ, j ≤ coneExcess c (c.length - 1) + 1
      ∧ CutFactorization (parityFamilyBits (stdCode v hv) hfit) S j :=
  balanced_cut_of_root_shape (parityFamilyBits (stdCode v hv) hfit) c hcomp hmin
    (parity_root_shape hv hm hfit c hcomp hmin) T hT hband

end PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.root_shape_of_two_essential
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd.parity_root_shape
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameParityEssStd.parity_balanced_cut
