import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGSurgeryToolkit

/-!
# N-Frame: the semantic DAG two-kill — Schnorr-style case analysis through sharing

The first DAG lower-bound theorem that analyzes what gates *compute*: restricting a live, non-top-decomposable
variable kills **two** gates of any circuit, sharing and fan-out fully accounted.  The case analysis is the
classical gate-elimination trichotomy, replayed on the straight-line model:

  * **two `var i` gates** — both become constants under the restriction; two constant surgeries;
  * **a unique `var i` gate with an interior reader** — the constant surgery converts the reader into an
        interior constant or unary gate, and the toolkit deletes it;
  * **a unique `var i` gate read only by the output** — then `f = op (xᵢ, h)` with `h` computed by a cone that
        provably contains no `var i` gate — a **top decomposition**, refuted by `¬TopDecomp f i`.

  `cbudget_twokill_dag` — **PROVED**: `DependsOnF f i → ¬TopDecomp f i →` (restriction non-constant) `→`
        `cbudget (restrictF f i b) + 2 ≤ cbudget f`.
  `dag_twokill_chain` / `sat3_cbudget_twokill_calibration` — **PROVED**: the chain engine and its sat3
        calibration `2·m·v − 1 ≤ cbudget (sat3Family N)` over the slot-2 selector chain.

## Honest scope

The calibration number sits *below* the connectivity record `2·m·D − 1` — rate-2 methods cap at two gates per
essential variable, which connectivity already collects globally.  The value here is the **mechanism**: the
first semantic case analysis on DAG observers, the induction step every Schnorr/Stockmeyer-style argument
iterates.  The genuine frontier — rate ≥ 2.5 per step via deeper case analysis (`2.5n`, `3n − o(n)`), and the
fan-out/cone-reuse accounting beyond — is named, not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Small helpers -/

theorem substGateC_var_self {n : ℕ} (i : Fin n) (b : Bool) :
    substGateC i b (CGate.var i) = CGate.cst b := by
  show (if i = i then CGate.cst b else CGate.var i) = CGate.cst b
  rw [if_pos rfl]

theorem getD_mem_of_lt {n : ℕ} (l : List (CGate n)) (q : ℕ) (h : q < l.length) :
    l.getD q (CGate.cst false) ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  show l[q] ∈ l
  exact List.getElem_mem h

theorem elimList_getD {n : ℕ} (c' : List (CGate n)) (p₁ p₂ : ℕ) (b : Bool)
    (h12 : p₁ < p₂) (h2 : p₂ < c'.length) :
    (c'.take p₁ ++ (c'.drop (p₁ + 1)).map (elimGate p₁ b)).getD (p₂ - 1) (CGate.cst false)
      = elimGate p₁ b (c'.getD p₂ (CGate.cst false)) := by
  have htlen : (c'.take p₁).length = p₁ := take_len c' p₁ (by omega)
  rw [List.getD_append_right _ _ _ _ (by omega : (c'.take p₁).length ≤ p₂ - 1)]
  rw [htlen]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop]
  rw [show p₁ + 1 + (p₂ - 1 - p₁) = p₂ by omega]
  rw [List.getElem?_eq_getElem h2]
  show elimGate p₁ b c'[p₂] = elimGate p₁ b (c'.getD p₂ (CGate.cst false))
  congr 1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rfl

theorem children_lt {n : ℕ} (c : List (CGate n)) (r j : ℕ) (h : j ∈ childrenOf c r) :
    j < r := by
  cases hg : c.getD r (CGate.cst false) with
  | var i =>
    rw [childrenOf_eq_var c r i hg] at h
    exact absurd h (Finset.notMem_empty j)
  | cst b =>
    rw [childrenOf_eq_cst c r b hg] at h
    exact absurd h (Finset.notMem_empty j)
  | un op j' =>
    rw [childrenOf_eq_un c r op j' hg] at h
    by_cases hj : j' < r
    · rw [if_pos hj] at h
      rw [Finset.mem_singleton] at h
      omega
    · rw [if_neg hj] at h
      exact absurd h (Finset.notMem_empty j)
  | bin op j' k' =>
    rw [childrenOf_eq_bin c r op j' k' hg] at h
    rcases Finset.mem_union.mp h with h' | h'
    · by_cases hj : j' < r
      · rw [if_pos hj] at h'
        rw [Finset.mem_singleton] at h'
        omega
      · rw [if_neg hj] at h'
        exact absurd h' (Finset.notMem_empty j)
    · by_cases hk : k' < r
      · rw [if_pos hk] at h'
        rw [Finset.mem_singleton] at h'
        omega
      · rw [if_neg hk] at h'
        exact absurd h' (Finset.notMem_empty j)

/-- The packaged constant deletion at a known interior position. -/
theorem computes_elim_at {n : ℕ} (c' : List (CGate n)) (f' : (Fin n → Bool) → Bool)
    (b : Bool) (p : ℕ) (hcomp : computes c' f')
    (hg : c'.getD p (CGate.cst false) = CGate.cst b) (hp : p < c'.length - 1) :
    computes (c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)) f'
      ∧ (c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).length = c'.length - 1 := by
  have hpL : p < c'.length := by omega
  have hsplit := circuit_split_at c' p hpL
  rw [hg] at hsplit
  have htlen : (c'.take p).length = p := take_len c' p (by omega)
  have hcomp' : computes (c'.take p ++ CGate.cst b :: c'.drop (p + 1)) f' := by
    rw [← hsplit]
    exact hcomp
  have hdne : c'.drop (p + 1) ≠ [] := by
    intro hcon
    have h := congrArg List.length hcon
    rw [List.length_drop] at h
    simp at h
    omega
  have hres := computes_elim (c'.take p) (c'.drop (p + 1)) b f' hcomp' hdne
  rw [htlen] at hres
  refine ⟨hres, ?_⟩
  rw [List.length_append, List.length_map, List.length_drop, htlen]
  omega

/-- The packaged unary shrink at a known interior position (in-range or garbage source alike). -/
theorem shrink_of_interior_un {n : ℕ} (d : List (CGate n)) (f' : (Fin n → Bool) → Bool)
    (hcomp : computes d f') (hnc : ∃ u w : Fin n → Bool, f' u ≠ f' w)
    (p : ℕ) (u : Bool → Bool) (w : ℕ)
    (hg : d.getD p (CGate.cst false) = CGate.un u w) (hp : p < d.length - 1) :
    ∃ d' : List (CGate n), computes d' f' ∧ d'.length + 1 = d.length := by
  have hpL : p < d.length := by omega
  have hsplit := circuit_split_at d p hpL
  rw [hg] at hsplit
  have htlen : (d.take p).length = p := take_len d p (by omega)
  have hcomp' : computes (d.take p ++ CGate.un u w :: d.drop (p + 1)) f' := by
    rw [← hsplit]
    exact hcomp
  have hdne : d.drop (p + 1) ≠ [] := by
    intro hcon
    have h := congrArg List.length hcon
    rw [List.length_drop] at h
    simp at h
    omega
  by_cases hw : w < p
  · have hres := computes_elim_un (d.take p) (d.drop (p + 1)) u w f' hcomp'
      (by omega) hdne
    refine ⟨_, hres, ?_⟩
    rw [List.length_append, List.length_map, List.length_drop, htlen]
    omega
  · have hrep := computes_congr_at (d.take p) (CGate.un u w) (CGate.cst (u false))
      (d.drop (p + 1)) f' (by
        intro x
        show u ((runFrom x [] (d.take p)).getD w false) = u false
        rw [List.getD_eq_default _ false (by
          rw [runFrom_length x (d.take p) []]
          show ([] : List Bool).length + (d.take p).length ≤ w
          simp only [List.length_nil]
          omega)]) hcomp'
    obtain ⟨d', hd', hlen⟩ := shrink_of_cst_mem _ f' (u false) hrep (by
      apply List.mem_append_right
      exact List.mem_cons_self) hnc
    refine ⟨d', hd', ?_⟩
    rw [List.length_append, List.length_cons, List.length_drop, htlen] at hlen
    omega

/-! ### The semantic two-kill -/

/-- **THE SEMANTIC DAG TWO-KILL (proved)**: restricting a live, non-top-decomposable variable kills two gates,
sharing and fan-out fully accounted — the classical gate-elimination trichotomy on the straight-line model. -/
theorem cbudget_twokill_dag {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (hdep : DependsOnF f i) (hnt : ¬TopDecomp f i)
    (hnc : ∃ u w : Fin n → Bool, restrictF f i b u ≠ restrictF f i b w) :
    cbudget (restrictF f i b) + 2 ≤ cbudget f := by
  classical
  obtain ⟨c, hcomp, hlen⟩ := Nat.sInf_mem (cbudget_set_nonempty f)
  have hlen' : c.length = cbudget f := hlen
  obtain ⟨x₁, x₀, hd, hnev⟩ := hdep
  have hrootvar : ∀ j : Fin n, c.getD (c.length - 1) (CGate.cst false) = CGate.var j →
      False := by
    intro j hg
    have hfx : ∀ x : Fin n → Bool, f x = x j := by
      intro x
      rw [← hcomp x]
      show (runFrom x [] c).getD (c.length - 1) false = x j
      by_cases hL : c.length - 1 < c.length
      · rw [output_getD_at x c (c.length - 1) hL, hg]
        rfl
      · exfalso
        rw [List.getD_eq_default _ _ (by omega)] at hg
        simp at hg
    by_cases hji : j = i
    · subst hji
      obtain ⟨u, w, hne'⟩ := hnc
      apply hne'
      show f (Function.update u j b) = f (Function.update w j b)
      rw [hfx, hfx, Function.update_self, Function.update_self]
    · apply hnev
      rw [hfx, hfx]
      by_contra hne'
      exact hji (hd j (fun h => hne' (by rw [h])))
  set c' : List (CGate n) := c.map (substGateC i b) with hc'
  have hc'comp : computes c' (restrictF f i b) := computes_subst c f i b hcomp
  have hc'len : c'.length = c.length := by
    rw [hc', List.length_map]
  by_cases hA : ∃ p₁ p₂ : ℕ, p₁ < p₂ ∧ c.getD p₁ (CGate.cst false) = CGate.var i ∧
      c.getD p₂ (CGate.cst false) = CGate.var i
  · -- CASE A: two variable gates, two constant surgeries
    obtain ⟨p₁, p₂, h12, hg₁, hg₂⟩ := hA
    have hp₂L : p₂ < c.length := by
      by_contra h'
      rw [List.getD_eq_default _ _ (by omega)] at hg₂
      simp at hg₂
    have hp₂int : p₂ < c.length - 1 := by
      by_cases h' : p₂ = c.length - 1
      · exact absurd (h' ▸ hg₂) (fun hh => hrootvar i hh)
      · omega
    have hg₁' : c'.getD p₁ (CGate.cst false) = CGate.cst b := by
      rw [hc', getD_map_lt c (substGateC i b) p₁ (by omega), hg₁, substGateC_var_self]
    have hg₂' : c'.getD p₂ (CGate.cst false) = CGate.cst b := by
      rw [hc', getD_map_lt c (substGateC i b) p₂ (by omega), hg₂, substGateC_var_self]
    obtain ⟨hd₁comp, hd₁len⟩ := computes_elim_at c' (restrictF f i b) b p₁ hc'comp hg₁'
      (by omega)
    have hd₁g : (c'.take p₁ ++ (c'.drop (p₁ + 1)).map (elimGate p₁ b)).getD (p₂ - 1)
        (CGate.cst false) = CGate.cst b := by
      rw [elimList_getD c' p₁ p₂ b h12 (by omega), hg₂']
      rfl
    obtain ⟨hd₂comp, hd₂len⟩ := computes_elim_at _ (restrictF f i b) b (p₂ - 1)
      hd₁comp hd₁g (by omega)
    have hb : cbudget (restrictF f i b) ≤ _ := Nat.sInf_le ⟨_, hd₂comp, rfl⟩
    omega
  · -- the variable gate is unique
    push_neg at hA
    have hpc : ∃ p ∈ coneOf c (c.length - 1),
        c.getD p (CGate.cst false) = CGate.var i := by
      by_contra hno
      push_neg at hno
      apply hnev
      rw [← hcomp x₁, ← hcomp x₀]
      show (runFrom x₁ [] c).getD (c.length - 1) false
          = (runFrom x₀ [] c).getD (c.length - 1) false
      apply cone_val_agree c (c.length - 1) x₁ x₀ ?_ (c.length - 1)
        (cone_self c (c.length - 1))
      intro p hp i' hgate
      by_cases hii : i' = i
      · exact absurd (hii ▸ hgate) (hno p hp)
      · by_contra hne'
        exact hii (hd i' hne')
    obtain ⟨p, hpcone, hpg⟩ := hpc
    have hpL : p < c.length := by
      by_contra h'
      rw [List.getD_eq_default _ _ (by omega)] at hpg
      simp at hpg
    have hpint : p < c.length - 1 := by
      by_cases h' : p = c.length - 1
      · exact absurd (h' ▸ hpg) (fun hh => hrootvar i hh)
      · omega
    have huniq : ∀ q, c.getD q (CGate.cst false) = CGate.var i → q = p := by
      intro q hq
      by_contra hne'
      rcases Nat.lt_or_ge q p with h' | h'
      · exact hA q p h' hq hpg
      · exact hA p q (by omega) hpg hq
    have hpg' : c'.getD p (CGate.cst false) = CGate.cst b := by
      rw [hc', getD_map_lt c (substGateC i b) p (by omega), hpg, substGateC_var_self]
    by_cases hB : ∃ r, r < c.length - 1 ∧ p ∈ childrenOf c r
    · -- CASE B1: an interior reader absorbs the constant and dies
      obtain ⟨r, hrint, hrchild⟩ := hB
      have hpr : p < r := children_lt c r p hrchild
      obtain ⟨hd₁comp, hd₁len⟩ := computes_elim_at c' (restrictF f i b) b p hc'comp hpg'
        (by omega)
      have hrimg : (c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).getD (r - 1)
          (CGate.cst false)
          = elimGate p b (substGateC i b (c.getD r (CGate.cst false))) := by
        rw [elimList_getD c' p r b hpr (by omega), hc',
          getD_map_lt c (substGateC i b) r (by omega)]
      have hd₁L : r - 1 < (c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).length - 1 := by
        omega
      cases hgr : c.getD r (CGate.cst false) with
      | var i' =>
        rw [childrenOf_eq_var c r i' hgr] at hrchild
        exact absurd hrchild (Finset.notMem_empty p)
      | cst b' =>
        rw [childrenOf_eq_cst c r b' hgr] at hrchild
        exact absurd hrchild (Finset.notMem_empty p)
      | un u' j =>
        rw [childrenOf_eq_un c r u' j hgr] at hrchild
        have hjp : j = p := by
          by_cases hj : j < r
          · rw [if_pos hj] at hrchild
            rw [Finset.mem_singleton] at hrchild
            omega
          · rw [if_neg hj] at hrchild
            exact absurd hrchild (Finset.notMem_empty p)
        rw [hjp] at hgr
        have himg : (c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).getD (r - 1)
            (CGate.cst false) = CGate.cst (u' b) := by
          rw [hrimg, hgr]
          show elimGate p b (CGate.un u' p) = CGate.cst (u' b)
          show (if p = p then CGate.cst (u' b) else CGate.un u' (elimRef p p))
              = CGate.cst (u' b)
          rw [if_pos rfl]
        obtain ⟨d', hd', hlen2⟩ := shrink_of_cst_mem _ (restrictF f i b) (u' b) hd₁comp
          (by
            rw [← himg]
            exact getD_mem_of_lt _ (r - 1) (by omega)) hnc
        have hb : cbudget (restrictF f i b) ≤ d'.length := Nat.sInf_le ⟨d', hd', rfl⟩
        omega
      | bin op' j k =>
        rw [childrenOf_eq_bin c r op' j k hgr] at hrchild
        have hjk : j = p ∨ k = p := by
          rcases Finset.mem_union.mp hrchild with h' | h'
          · by_cases hj : j < r
            · rw [if_pos hj] at h'
              rw [Finset.mem_singleton] at h'
              omega
            · rw [if_neg hj] at h'
              exact absurd h' (Finset.notMem_empty p)
          · by_cases hk : k < r
            · rw [if_pos hk] at h'
              rw [Finset.mem_singleton] at h'
              omega
            · rw [if_neg hk] at h'
              exact absurd h' (Finset.notMem_empty p)
        by_cases hjp : j = p
        · by_cases hkp : k = p
          · -- double read: constant image
            rw [hjp, hkp] at hgr
            have himg : (c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).getD (r - 1)
                (CGate.cst false) = CGate.cst (op' b b) := by
              rw [hrimg, hgr]
              show elimGate p b (CGate.bin op' p p) = CGate.cst (op' b b)
              show (if p = p then (if p = p then CGate.cst (op' b b)
                  else CGate.un (fun c => op' b c) (elimRef p p))
                else if p = p then CGate.un (fun a => op' a b) (elimRef p p)
                else CGate.bin op' (elimRef p p) (elimRef p p)) = CGate.cst (op' b b)
              rw [if_pos rfl, if_pos rfl]
            obtain ⟨d', hd', hlen2⟩ := shrink_of_cst_mem _ (restrictF f i b) (op' b b)
              hd₁comp (by
                rw [← himg]
                exact getD_mem_of_lt _ (r - 1) (by omega)) hnc
            have hb : cbudget (restrictF f i b) ≤ d'.length := Nat.sInf_le ⟨d', hd', rfl⟩
            omega
          · -- left read: unary image
            rw [hjp] at hgr
            have himg : (c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).getD (r - 1)
                (CGate.cst false) = CGate.un (fun c => op' b c) (elimRef p k) := by
              rw [hrimg, hgr]
              show elimGate p b (CGate.bin op' p k)
                  = CGate.un (fun c => op' b c) (elimRef p k)
              show (if p = p then (if k = p then CGate.cst (op' b b)
                  else CGate.un (fun c => op' b c) (elimRef p k))
                else if k = p then CGate.un (fun a => op' a b) (elimRef p p)
                else CGate.bin op' (elimRef p p) (elimRef p k)) = _
              rw [if_pos rfl, if_neg hkp]
            obtain ⟨d', hd', hlen2⟩ := shrink_of_interior_un _ (restrictF f i b) hd₁comp hnc
              (r - 1) (fun c => op' b c) (elimRef p k) himg hd₁L
            have hb : cbudget (restrictF f i b) ≤ d'.length := Nat.sInf_le ⟨d', hd', rfl⟩
            omega
        · have hkp : k = p := hjk.resolve_left hjp
          rw [hkp] at hgr
          -- right read: unary image
          have himg : (c'.take p ++ (c'.drop (p + 1)).map (elimGate p b)).getD (r - 1)
              (CGate.cst false) = CGate.un (fun a => op' a b) (elimRef p j) := by
            rw [hrimg, hgr]
            show elimGate p b (CGate.bin op' j p)
                = CGate.un (fun a => op' a b) (elimRef p j)
            show (if j = p then (if p = p then CGate.cst (op' b b)
                else CGate.un (fun c => op' b c) (elimRef p p))
              else if p = p then CGate.un (fun a => op' a b) (elimRef p j)
              else CGate.bin op' (elimRef p j) (elimRef p p)) = _
            rw [if_neg hjp, if_pos rfl]
          obtain ⟨d', hd', hlen2⟩ := shrink_of_interior_un _ (restrictF f i b) hd₁comp hnc
            (r - 1) (fun a => op' a b) (elimRef p j) himg hd₁L
          have hb : cbudget (restrictF f i b) ≤ d'.length := Nat.sInf_le ⟨d', hd', rfl⟩
          omega
    · -- CASE B2: only the output reads the variable — a top decomposition, refuted
      exfalso
      push_neg at hB
      have hrootchild : p ∈ childrenOf c (c.length - 1) := by
        rcases cone_parent c (c.length - 1) p hpcone with h' | ⟨r, hrcone, hrchild⟩
        · omega
        · have hrle := cone_le c (c.length - 1) r hrcone
          by_cases hr : r < c.length - 1
          · exact absurd hrchild (hB r hr)
          · have hreq : r = c.length - 1 := by omega
            exact hreq ▸ hrchild
      have hout : ∀ x : Fin n → Bool, f x
          = evalGate x (runFrom x [] (c.take (c.length - 1)))
              (c.getD (c.length - 1) (CGate.cst false)) := by
        intro x
        rw [← hcomp x]
        exact output_getD_at x c (c.length - 1) (by omega)
      have hwp : ∀ x : Fin n → Bool,
          (runFrom x [] (c.take (c.length - 1))).getD p false = x i := by
        intro x
        rw [takeRun_getD x c (c.length - 1) p (by omega) (by omega),
          output_getD_at x c p hpL, hpg]
        rfl
      cases hgroot : c.getD (c.length - 1) (CGate.cst false) with
      | var j => exact hrootvar j hgroot
      | cst b' =>
        rw [childrenOf_eq_cst c (c.length - 1) b' hgroot] at hrootchild
        exact absurd hrootchild (Finset.notMem_empty p)
      | un u' j =>
        rw [childrenOf_eq_un c (c.length - 1) u' j hgroot] at hrootchild
        have hjp : j = p := by
          by_cases hj : j < c.length - 1
          · rw [if_pos hj] at hrootchild
            rw [Finset.mem_singleton] at hrootchild
            omega
          · rw [if_neg hj] at hrootchild
            exact absurd hrootchild (Finset.notMem_empty p)
        rw [hjp] at hgroot
        obtain ⟨u, w, hne'⟩ := hnc
        apply hne'
        show f (Function.update u i b) = f (Function.update w i b)
        have hf : ∀ x : Fin n → Bool, f x = u' (x i) := by
          intro x
          have h := hout x
          rw [hgroot] at h
          rw [h]
          show u' ((runFrom x [] (c.take (c.length - 1))).getD p false) = u' (x i)
          rw [hwp x]
        rw [hf, hf, Function.update_self, Function.update_self]
      | bin op' j k =>
        rw [childrenOf_eq_bin c (c.length - 1) op' j k hgroot] at hrootchild
        have hfeq : ∀ x : Fin n → Bool, f x
            = op' ((runFrom x [] (c.take (c.length - 1))).getD j false)
                ((runFrom x [] (c.take (c.length - 1))).getD k false) := by
          intro x
          have h := hout x
          rw [hgroot] at h
          exact h
        have hjk : j = p ∨ k = p := by
          rcases Finset.mem_union.mp hrootchild with h' | h'
          · by_cases hj : j < c.length - 1
            · rw [if_pos hj] at h'
              rw [Finset.mem_singleton] at h'
              omega
            · rw [if_neg hj] at h'
              exact absurd h' (Finset.notMem_empty p)
          · by_cases hk : k < c.length - 1
            · rw [if_pos hk] at h'
              rw [Finset.mem_singleton] at h'
              omega
            · rw [if_neg hk] at h'
              exact absurd h' (Finset.notMem_empty p)
        have hother : ∀ m, m < c.length - 1 → m ≠ p →
            ∀ (x : Fin n → Bool) (b'' : Bool),
              (runFrom (Function.update x i b'') [] c).getD m false
                = (runFrom x [] c).getD m false := by
          intro m hm hmp x b''
          apply cone_val_agree c m (Function.update x i b'') x ?_ m (cone_self c m)
          intro q hq i' hgate
          have hii : i' ≠ i := by
            intro hii'
            subst hii'
            have hqp := huniq q hgate
            subst hqp
            rcases cone_parent c m q hq with h' | ⟨r', hr'cone, hr'child⟩
            · exact hmp h'.symm
            · have hr'le := cone_le c m r' hr'cone
              exact hB r' (by omega) hr'child
          rw [Function.update_of_ne hii]
        by_cases hjp : j = p
        · rw [hjp] at hfeq
          by_cases hkp2 : k = p
          · rw [hkp2] at hfeq
            obtain ⟨u, w, hne'⟩ := hnc
            apply hne'
            show f (Function.update u i b) = f (Function.update w i b)
            have hf : ∀ x : Fin n → Bool, f x = op' (x i) (x i) := by
              intro x
              rw [hfeq x, hwp x]
            rw [hf, hf, Function.update_self, Function.update_self]
          · by_cases hkL : k < c.length - 1
            · apply hnt
              refine ⟨op', fun x => (runFrom x [] c).getD k false, ?_, ?_⟩
              · intro x
                rw [hfeq x, hwp x, takeRun_getD x c (c.length - 1) k hkL (by omega)]
              · intro x b''
                exact hother k hkL hkp2 x b''
            · apply hnt
              refine ⟨op', fun _ => false, ?_, fun _ _ => rfl⟩
              intro x
              rw [hfeq x, hwp x]
              congr 1
              rw [List.getD_eq_default _ false (by
                rw [runFrom_length x (c.take (c.length - 1)) []]
                show ([] : List Bool).length + (c.take (c.length - 1)).length ≤ k
                simp only [List.length_nil]
                rw [take_len c (c.length - 1) (by omega)]
                omega)]
        · have hkp : k = p := hjk.resolve_left hjp
          rw [hkp] at hfeq
          by_cases hjL : j < c.length - 1
          · apply hnt
            refine ⟨fun a c'' => op' c'' a, fun x => (runFrom x [] c).getD j false, ?_, ?_⟩
            · intro x
              show f x = op' ((runFrom x [] c).getD j false) (x i)
              rw [hfeq x, hwp x, takeRun_getD x c (c.length - 1) j hjL (by omega)]
            · intro x b''
              exact hother j hjL hjp x b''
          · apply hnt
            refine ⟨fun a c'' => op' c'' a, fun _ => false, ?_, fun _ _ => rfl⟩
            intro x
            show f x = op' false (x i)
            rw [hfeq x, hwp x]
            congr 1
            rw [List.getD_eq_default _ false (by
              rw [runFrom_length x (c.take (c.length - 1)) []]
              show ([] : List Bool).length + (c.take (c.length - 1)).length ≤ j
              simp only [List.length_nil]
              rw [take_len c (c.length - 1) (by omega)]
              omega)]

/-! ### The chain engine and its calibration -/

/-- **The DAG two-kill chain (proved)**: a `TwoKillChain` forces two gates per step. -/
theorem dag_twokill_chain {n : ℕ} :
    ∀ (steps : List (Fin n × Bool)) (f : (Fin n → Bool) → Bool),
      TwoKillChain f steps → 2 * steps.length - 1 ≤ cbudget f := by
  intro steps
  induction steps with
  | nil => intro f _; exact Nat.zero_le _
  | cons s rest ih =>
    intro f h
    have h' : DependsOnF f s.1 ∧ ¬TopDecomp f s.1 ∧
        TwoKillChain (restrictF f s.1 s.2) rest := h
    obtain ⟨hdep, hnt, hchain⟩ := h'
    cases rest with
    | nil =>
      show 2 * 1 - 1 ≤ cbudget f
      have := cbudget_pos_of_dep f s.1 hdep
      omega
    | cons s' rest' =>
      have h'' : DependsOnF (restrictF f s.1 s.2) s'.1 ∧
          ¬TopDecomp (restrictF f s.1 s.2) s'.1 ∧
          TwoKillChain (restrictF (restrictF f s.1 s.2) s'.1 s'.2) rest' := hchain
      have hnc : ∃ u w, restrictF f s.1 s.2 u ≠ restrictF f s.1 s.2 w := by
        obtain ⟨⟨y₁, y₀, -, hnev⟩, -, -⟩ := h''
        exact ⟨y₁, y₀, hnev⟩
      have hkill := cbudget_twokill_dag f s.1 s.2 hdep hnt hnc
      have hih : 2 * (s' :: rest').length - 1 ≤ cbudget (restrictF f s.1 s.2) :=
        ih (restrictF f s.1 s.2) hchain
      have hlen : (s' :: rest').length = rest'.length + 1 := rfl
      show 2 * (rest'.length + 1 + 1) - 1 ≤ cbudget f
      omega

/-- **The calibration (proved)**: the selector chain at the two-kill rate — `2·m·v − 1 ≤ cbudget (sat3Family)`.
Below the connectivity record `2·m·D − 1`, as it must be: rate-2 methods cap at two gates per essential
variable.  The content is the mechanism, not the number. -/
theorem sat3_cbudget_twokill_calibration (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    2 * (sat3M N * sat3V N) - 1 ≤ cbudget (sat3Family N) := by
  have h := dag_twokill_chain (sat3SelSteps N) (sat3Family N)
    (sat3_selector_chain N hv hm2)
  rw [sat3SelSteps_length] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.computes_elim_at
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.shrink_of_interior_un
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_twokill_dag
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.dag_twokill_chain
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_cbudget_twokill_calibration
