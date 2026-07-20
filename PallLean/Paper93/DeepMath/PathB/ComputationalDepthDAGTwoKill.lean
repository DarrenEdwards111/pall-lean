import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDAGUnElimination
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCbudgetConeBound

/-!
# THE DAG TWO-KILL STEP THEOREM

The assembly brick.  **Statement**: if both restrictions `f|₀`, `f|₁` are nonconstant
and `f|₁` is neither `f|₀` nor its pointwise complement, then restricting kills two
gates: `cbudget (restrictF f i b) + 2 ≤ cbudget f`.

The guard is where the mathematics lives — the unconditional two-kill is *false*
(`¬(x₁ ∧ x₂)` loses exactly one gate).  Proof, on a minimal circuit:

* **two `var i` gates** — substitution leaves two constants; two constant
  eliminations (a last-position constant makes the restriction constant: contra);
* **one `var i` gate with a non-output in-range reader** — the reader absorbs the
  constant and becomes a constant (second constant kill) or a unary gate (the
  brick-1 unary kill; out-of-range sources via `computes_un_oob`);
* **one `var i` gate whose only in-range reader is the output, or none** — then
  `f = op (xᵢ, u)` with `u` independent of `xᵢ` (threshold-invariance induction), so
  the two restrictions are constant, equal, or complementary — refuting the guard.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound

/-! ### List splitting helpers -/

theorem count_two_split {α : Type} [DecidableEq α] (a : α) :
    ∀ (l : List α), 2 ≤ l.count a → ∃ A M R, l = A ++ a :: M ++ a :: R := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons g gs ih =>
    intro h
    by_cases hg : g = a
    · subst hg
      have h1 : 1 ≤ gs.count g := by
        rw [List.count_cons_self] at h
        omega
      have hmem : g ∈ gs := List.count_pos_iff.mp (by omega)
      obtain ⟨M, R, rfl⟩ := List.append_of_mem hmem
      exact ⟨[], M, R, rfl⟩
    · have h' : 2 ≤ gs.count a := by
        rw [List.count_cons_of_ne hg] at h
        exact h
      obtain ⟨A, M, R, rfl⟩ := ih h'
      exact ⟨g :: A, M, R, rfl⟩

theorem count_one_split {α : Type} [DecidableEq α] (a : α) :
    ∀ (l : List α), l.count a = 1 → ∃ A B, l = A ++ a :: B ∧ a ∉ A ∧ a ∉ B := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons g gs ih =>
    intro h
    by_cases hg : g = a
    · subst hg
      have h0 : gs.count g = 0 := by
        rw [List.count_cons_self] at h
        omega
      exact ⟨[], gs, rfl, List.not_mem_nil, List.count_eq_zero.mp h0⟩
    · have h' : gs.count a = 1 := by
        rw [List.count_cons_of_ne hg] at h
        exact h
      obtain ⟨A, B, rfl, hA, hB⟩ := ih h'
      refine ⟨g :: A, B, rfl, ?_, hB⟩
      intro hmem
      rcases List.mem_cons.mp hmem with he | hmem'
      · exact hg he.symm
      · exact hA hmem'

theorem substGateC_noop {n : ℕ} (i : Fin n) (b : Bool) :
    ∀ (l : List (CGate n)), CGate.var i ∉ l → l.map (substGateC i b) = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons g gs ih =>
    intro h
    have hg : substGateC i b g = g := by
      cases g with
      | var j =>
        have hne : j ≠ i := fun he => h (by rw [he]; exact List.mem_cons_self)
        show (if j = i then CGate.cst b else CGate.var j) = CGate.var j
        rw [if_neg hne]
      | cst c => rfl
      | un op j => rfl
      | bin op j k => rfl
    rw [List.map_cons, hg, ih (fun hmem => h (List.mem_cons_of_mem g hmem))]

theorem substGateC_var_self {n : ℕ} (i : Fin n) (b : Bool) :
    substGateC i b (CGate.var i) = CGate.cst b := by
  show (if i = i then CGate.cst b else CGate.var i) = CGate.cst b
  rw [if_pos rfl]

/-! ### Mid-circuit elimination wrappers -/

theorem cbudget_le_of_cst_mid {n : ℕ} (d₁ d₂ : List (CGate n)) (v : Bool)
    (g : (Fin n → Bool) → Bool)
    (hcomp : computes (d₁ ++ CGate.cst v :: d₂) g) (hne : d₂ ≠ []) :
    cbudget g ≤ d₁.length + d₂.length := by
  have hmem : (d₁ ++ d₂.map (elimGate d₁.length v)).length
      ∈ {s | ∃ c : List (CGate n), computes c g ∧ c.length = s} :=
    ⟨d₁ ++ d₂.map (elimGate d₁.length v), computes_elim d₁ d₂ v g hcomp hne, rfl⟩
  have h := Nat.sInf_le hmem
  rwa [List.length_append, List.length_map] at h

theorem cbudget_le_of_un_mid {n : ℕ} (d₁ d₂ : List (CGate n)) (op : Bool → Bool) (q : ℕ)
    (g : (Fin n → Bool) → Bool)
    (hcomp : computes (d₁ ++ CGate.un op q :: d₂) g) (hne : d₂ ≠ []) :
    cbudget g ≤ d₁.length + d₂.length := by
  by_cases hq : q < d₁.length
  · exact cbudget_elimUn_le d₁ d₂ op q g hcomp hne hq
  · exact cbudget_le_of_cst_mid d₁ d₂ (op false) g
      (computes_un_oob d₁ d₂ op q g hcomp (by omega)) hne

theorem output_last_cst {n : ℕ} (d : List (CGate n)) (v : Bool) (x : Fin n → Bool) :
    output (d ++ [CGate.cst v]) x = v := by
  show (runFrom x [] (d ++ [CGate.cst v])).getD ((d ++ [CGate.cst v]).length - 1) false = v
  rw [runFrom_append]
  show ((runFrom x [] d) ++ [v]).getD ((d ++ [CGate.cst v]).length - 1) false = v
  have hV : (runFrom x [] d).length = d.length := by
    rw [runFrom_length]
    simp
  have hidx : (d ++ [CGate.cst v]).length - 1 = (runFrom x [] d).length := by
    rw [List.length_append, hV]
    show d.length + 1 - 1 = d.length
    omega
  rw [hidx]
  exact getD_concat _ _

/-! ### Threshold invariance -/

theorem wire_inv {n : ℕ} (c : List (CGate n)) (i : Fin n) (p W : ℕ) (hW : W ≤ c.length)
    (hnoread : ∀ v, p < v → v < W → p ∉ gateReads (c.getD v (.cst false)))
    (hvar : ∀ v, v < W → v ≠ p → c.getD v (.cst false) ≠ CGate.var i)
    (x : Fin n → Bool) (b' : Bool) :
    ∀ w, w < W → w ≠ p → wire c (Function.update x i b') w = wire c x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwW hwp
    have hwlt : w < c.length := by omega
    have hread : ∀ j ∈ gateReads (c.getD w (.cst false)),
        (runFrom (Function.update x i b') [] (c.take w)).getD j false
          = (runFrom x [] (c.take w)).getD j false := by
      intro j hj
      by_cases hjw : j < w
      · by_cases hjp : j = p
        · exact absurd (hjp ▸ hj) (hnoread w (by omega) hwW)
        · rw [wire_prefix c _ hjw (le_of_lt hwlt), wire_prefix c x hjw (le_of_lt hwlt)]
          exact ih j hjw (by omega) hjp
      · rw [List.getD_eq_default _ _ (by
            rw [runFrom_length, List.length_take]; simp; omega),
          List.getD_eq_default _ _ (by
            rw [runFrom_length, List.length_take]; simp; omega)]
    rw [wire_eq c _ hwlt, wire_eq c x hwlt]
    cases hg : c.getD w (.cst false) with
    | var i' =>
      simp only [evalGate]
      have hne : i' ≠ i := fun he => hvar w hwW hwp (by rw [hg, he])
      exact Function.update_of_ne hne b' x
    | cst b2 => rfl
    | un op j =>
      simp only [evalGate]
      rw [hread j (by rw [hg]; simp [gateReads])]
    | bin op j k =>
      simp only [evalGate]
      rw [hread j (by rw [hg]; simp [gateReads]),
        hread k (by rw [hg]; simp [gateReads])]

/-! ### Positional bookkeeping -/

theorem getD_append_self {n : ℕ} (A B : List (CGate n)) (g : CGate n) :
    (A ++ g :: B).getD A.length (.cst false) = g := by
  rw [List.getD_append_right A _ _ A.length (le_refl _), Nat.sub_self]
  rfl

theorem getD_append_cons_right {n : ℕ} (A B : List (CGate n)) (g : CGate n) (r : ℕ) :
    (A ++ g :: B).getD (A.length + 1 + r) (.cst false) = B.getD r (.cst false) := by
  rw [List.getD_append_right A _ _ _ (by omega),
    show A.length + 1 + r - A.length = r + 1 from by omega]
  rfl

/-! ### The Boolean shape lemma and the affine refutation -/

theorem unary_shape (g : Bool → Bool) :
    (∀ y, g y = g false) ∨ (∀ y, g y = y) ∨ (∀ y, g y = !y) := by
  cases h0 : g false <;> cases h1 : g true
  · exact Or.inl (fun y => by cases y <;> simp [h0, h1])
  · exact Or.inr (Or.inl (fun y => by cases y <;> simp [h0, h1]))
  · exact Or.inr (Or.inr (fun y => by cases y <;> simp [h0, h1]))
  · exact Or.inl (fun y => by cases y <;> simp [h0, h1])

/-- The affine refutation: `f|ᵦ = op b ∘ u` forces the restrictions constant, equal,
or complementary — contradicting the two-kill guard. -/
theorem affine_refute {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (op : Bool → Bool → Bool) (u : (Fin n → Bool) → Bool)
    (hrep : ∀ (b' : Bool) (x : Fin n → Bool), restrictF f i b' x = op b' (u x))
    (h0 : ∃ x y, restrictF f i false x ≠ restrictF f i false y)
    (h1 : ∃ x y, restrictF f i true x ≠ restrictF f i true y)
    (hne : restrictF f i true ≠ restrictF f i false)
    (hnc : restrictF f i true ≠ fun x => !(restrictF f i false x)) : False := by
  rcases unary_shape (fun y => op false y) with hc0 | hid0 | hnot0
  · obtain ⟨x, y, hxy⟩ := h0
    exact hxy (by rw [hrep, hrep, hc0 (u x), hc0 (u y)])
  · rcases unary_shape (fun y => op true y) with hc1 | hid1 | hnot1
    · obtain ⟨x, y, hxy⟩ := h1
      exact hxy (by rw [hrep, hrep, hc1 (u x), hc1 (u y)])
    · exact hne (funext fun x => by rw [hrep, hrep, hid1 (u x), hid0 (u x)])
    · exact hnc (funext fun x => by rw [hrep, hrep, hnot1 (u x), hid0 (u x)])
  · rcases unary_shape (fun y => op true y) with hc1 | hid1 | hnot1
    · obtain ⟨x, y, hxy⟩ := h1
      exact hxy (by rw [hrep, hrep, hc1 (u x), hc1 (u y)])
    · exact hnc (funext fun x => by
        rw [hrep, hrep, hid1 (u x), hnot0 (u x), Bool.not_not])
    · exact hne (funext fun x => by rw [hrep, hrep, hnot1 (u x), hnot0 (u x)])

/-! ### THE TWO-KILL -/

/-- **THE DAG TWO-KILL STEP THEOREM (proved).**  If both restrictions of `f` at `xᵢ`
are nonconstant, and they are neither equal nor pointwise complementary, then fixing
`xᵢ` (to either constant) kills two gates. -/
theorem cbudget_twokill {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (h0 : ∃ x y, restrictF f i false x ≠ restrictF f i false y)
    (h1 : ∃ x y, restrictF f i true x ≠ restrictF f i true y)
    (hne : restrictF f i true ≠ restrictF f i false)
    (hnc : restrictF f i true ≠ fun x => !(restrictF f i false x)) :
    cbudget (restrictF f i b) + 2 ≤ cbudget f := by
  classical
  obtain ⟨c, hcomp, hclen⟩ := Nat.sInf_mem (cbudget_set_nonempty f)
  have hclen' : c.length = cbudget f := hclen
  have hgnc : ∃ x y, restrictF f i b x ≠ restrictF f i b y := by
    cases b
    · exact h0
    · exact h1
  have hxne : ∃ x, restrictF f i true x ≠ restrictF f i false x := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  obtain ⟨z, hz⟩ := hxne
  have hvar_mem : CGate.var i ∈ c :=
    depends_var_mem c f hcomp i (Function.update z i true) (Function.update z i false)
      (fun c' hc' => by
        by_contra hcne
        exact hc' (by rw [Function.update_of_ne hcne, Function.update_of_ne hcne]))
      hz
  have hcount : 1 ≤ c.count (CGate.var i) := List.count_pos_iff.mpr hvar_mem
  rcases Nat.lt_or_ge (c.count (CGate.var i)) 2 with hone | htwo
  · -- == CASE B: exactly one var-i gate ==
    have h1c : c.count (CGate.var i) = 1 := by omega
    obtain ⟨A, B, rfl, hAno, hBno⟩ := count_one_split (CGate.var i) c h1c
    by_cases hBnil : B = []
    · -- the var gate is the output: the restriction is constant, contra
      subst hBnil
      exfalso
      obtain ⟨x, y, hxy⟩ := hgnc
      apply hxy
      show f (Function.update x i b) = f (Function.update y i b)
      rw [← hcomp (Function.update x i b), ← hcomp (Function.update y i b),
        output_last_var, output_last_var, Function.update_self, Function.update_self]
    · have hlen_c : (A ++ CGate.var i :: B).length = A.length + 1 + B.length := by
        rw [List.length_append, List.length_cons]
        omega
      have hBpos : 1 ≤ B.length := by
        cases B with
        | nil => exact absurd rfl hBnil
        | cons gB restB => show 1 ≤ restB.length + 1; omega
      -- substitute
      have hsubst := computes_subst (A ++ CGate.var i :: B) f i b hcomp
      rw [show (A ++ CGate.var i :: B).map (substGateC i b) = A ++ CGate.cst b :: B from by
        rw [List.map_append, List.map_cons, substGateC_noop i b A hAno,
          substGateC_noop i b B hBno, substGateC_var_self]] at hsubst
      -- reader dichotomy below the output
      by_cases hR : ∃ w, A.length < w ∧ w + 1 < (A ++ CGate.var i :: B).length ∧
          A.length ∈ gateReads ((A ++ CGate.var i :: B).getD w (.cst false))
      · -- non-output reader: two kills
        obtain ⟨w₀, hw₀p, hw₀lt, hw₀mem⟩ := hR
        rw [hlen_c] at hw₀lt
        have hw₀ : w₀ = A.length + 1 + (w₀ - A.length - 1) := by omega
        set r := w₀ - A.length - 1 with hrdef
        have hrB : r + 1 < B.length := by omega
        rw [hw₀, getD_append_cons_right A B (CGate.var i) r] at hw₀mem
        have hBsplit : B = B.take r ++ B.getD r (.cst false) :: B.drop (r + 1) := by
          conv_lhs => rw [← List.take_append_drop r B]
          rw [List.drop_eq_getElem_cons (by omega),
            List.getD_eq_getElem B (CGate.cst false) (by omega)]
        have helim := computes_elim A B b (restrictF f i b) hsubst hBnil
        rw [hBsplit, List.map_append, List.map_cons] at helim
        have htake_len : ((B.take r).map (elimGate A.length b)).length = r := by
          rw [List.length_map, List.length_take]
          omega
        have hdrop_ne : ((B.drop (r + 1)).map (elimGate A.length b)) ≠ [] := by
          intro hnil
          have := congrArg List.length hnil
          rw [List.length_map, List.length_drop] at this
          simp at this
          omega
        rw [← List.append_assoc] at helim
        cases hrgshape : B.getD r (.cst false) with
        | var j =>
          rw [hrgshape] at hw₀mem
          simp [gateReads] at hw₀mem
        | cst v =>
          rw [hrgshape] at hw₀mem
          simp [gateReads] at hw₀mem
        | un op j =>
          rw [hrgshape] at hw₀mem
          have hj : j = A.length := by
            have := hw₀mem
            simp [gateReads] at this
            omega
          rw [hrgshape, hj] at helim
          rw [show elimGate (n := n) A.length b (CGate.un op A.length)
              = CGate.cst (op b) from by
            show (if A.length = A.length then CGate.cst (op b)
              else CGate.un op (elimRef A.length A.length)) = CGate.cst (op b)
            rw [if_pos rfl]] at helim
          have hfinal := cbudget_le_of_cst_mid _ _ (op b) (restrictF f i b) helim hdrop_ne
          rw [List.length_append, htake_len, List.length_map, List.length_drop] at hfinal
          omega
        | bin op j k =>
          rw [hrgshape] at hw₀mem
          have hjk : j = A.length ∨ k = A.length := by
            have := hw₀mem
            simp [gateReads] at this
            omega
          rw [hrgshape] at helim
          by_cases hj : j = A.length
          · by_cases hk : k = A.length
            · rw [show elimGate (n := n) A.length b (CGate.bin op j k)
                  = CGate.cst (op b b) from by
                show (if j = A.length then
                    (if k = A.length then CGate.cst (op b b)
                     else CGate.un (fun c => op b c) (elimRef A.length k))
                  else if k = A.length then CGate.un (fun a => op a b) (elimRef A.length j)
                  else CGate.bin op (elimRef A.length j) (elimRef A.length k))
                  = CGate.cst (op b b)
                rw [if_pos hj, if_pos hk]] at helim
              have hfinal := cbudget_le_of_cst_mid _ _ (op b b) (restrictF f i b) helim hdrop_ne
              rw [List.length_append, htake_len, List.length_map, List.length_drop] at hfinal
              omega
            · rw [show elimGate (n := n) A.length b (CGate.bin op j k)
                  = CGate.un (fun c => op b c) (elimRef A.length k) from by
                show (if j = A.length then
                    (if k = A.length then CGate.cst (op b b)
                     else CGate.un (fun c => op b c) (elimRef A.length k))
                  else if k = A.length then CGate.un (fun a => op a b) (elimRef A.length j)
                  else CGate.bin op (elimRef A.length j) (elimRef A.length k))
                  = CGate.un (fun c => op b c) (elimRef A.length k)
                rw [if_pos hj, if_neg hk]] at helim
              have hfinal := cbudget_le_of_un_mid _ _ (fun c => op b c) (elimRef A.length k)
                (restrictF f i b) helim hdrop_ne
              rw [List.length_append, htake_len, List.length_map, List.length_drop] at hfinal
              omega
          · have hk : k = A.length := by
              rcases hjk with he | he
              · exact absurd he hj
              · exact he
            rw [show elimGate (n := n) A.length b (CGate.bin op j k)
                = CGate.un (fun a => op a b) (elimRef A.length j) from by
              show (if j = A.length then
                  (if k = A.length then CGate.cst (op b b)
                   else CGate.un (fun c => op b c) (elimRef A.length k))
                else if k = A.length then CGate.un (fun a => op a b) (elimRef A.length j)
                else CGate.bin op (elimRef A.length j) (elimRef A.length k))
                = CGate.un (fun a => op a b) (elimRef A.length j)
              rw [if_neg hj, if_pos hk]] at helim
            have hfinal := cbudget_le_of_un_mid _ _ (fun a => op a b) (elimRef A.length j)
              (restrictF f i b) helim hdrop_ne
            rw [List.length_append, htake_len, List.length_map, List.length_drop] at hfinal
            omega
      · -- no in-range reader below the output: the semantic cases
        exfalso
        push_neg at hR
        have hvar_getD : ∀ v, v < (A ++ CGate.var i :: B).length → v ≠ A.length →
            (A ++ CGate.var i :: B).getD v (.cst false) ≠ CGate.var i := by
          intro v hv hvp he
          rcases Nat.lt_trichotomy v A.length with hlt | heq | hgt
          · have hmem : (A ++ CGate.var i :: B).getD v (.cst false) ∈ A := by
              rw [List.getD_append A _ _ v hlt, List.getD_eq_getElem A _ hlt]
              exact List.getElem_mem _
            exact hAno (he ▸ hmem)
          · exact hvp heq
          · have hv' : v - A.length - 1 < B.length := by
              rw [hlen_c] at hv
              omega
            have hmem : (A ++ CGate.var i :: B).getD v (.cst false) ∈ B := by
              have hgetd := getD_append_cons_right A B (CGate.var i) (v - A.length - 1)
              rw [show A.length + 1 + (v - A.length - 1) = v from by omega] at hgetd
              rw [hgetd, List.getD_eq_getElem B _ hv']
              exact List.getElem_mem _
            exact hBno (he ▸ hmem)
        by_cases hOut : A.length ∈ gateReads
            ((A ++ CGate.var i :: B).getD ((A ++ CGate.var i :: B).length - 1) (.cst false))
        · -- the output reads the var wire: the affine refutation
          have hlen1 : (A ++ CGate.var i :: B).length - 1 < (A ++ CGate.var i :: B).length := by
            rw [hlen_c]
            omega
          have hwire_p : ∀ x : Fin n → Bool,
              wire (A ++ CGate.var i :: B) x A.length = x i := by
            intro x
            rw [wire_eq _ _ (by rw [hlen_c]; omega), getD_append_self]
            rfl
          have hfout : ∀ x : Fin n → Bool, f x
              = evalGate x (runFrom x [] ((A ++ CGate.var i :: B).take
                  ((A ++ CGate.var i :: B).length - 1)))
                ((A ++ CGate.var i :: B).getD
                  ((A ++ CGate.var i :: B).length - 1) (.cst false)) := by
            intro x
            rw [← hcomp x, output_eq_wire, wire_eq _ _ hlen1]
          have hinv : ∀ (x : Fin n → Bool) (b' : Bool) (w : ℕ),
              w < (A ++ CGate.var i :: B).length - 1 → w ≠ A.length →
              wire (A ++ CGate.var i :: B) (Function.update x i b') w
                = wire (A ++ CGate.var i :: B) x w :=
            fun x b' => wire_inv (A ++ CGate.var i :: B) i A.length
              ((A ++ CGate.var i :: B).length - 1) (by omega)
              (fun v hv1 hv2 => hR v hv1 (by omega))
              (fun v hv hvp => hvar_getD v (by omega) hvp) x b'
          cases hg : (A ++ CGate.var i :: B).getD
              ((A ++ CGate.var i :: B).length - 1) (.cst false) with
          | var j =>
            rw [hg] at hOut
            simp [gateReads] at hOut
          | cst v =>
            rw [hg] at hOut
            simp [gateReads] at hOut
          | un op j =>
            rw [hg] at hOut
            have hj : j = A.length := by
              simp [gateReads] at hOut
              omega
            subst hj
            have hfeq : ∀ x : Fin n → Bool, f x = op (x i) := by
              intro x
              rw [hfout x, hg]
              show op ((runFrom x [] _).getD A.length false) = op (x i)
              rw [wire_prefix _ _ (by rw [hlen_c]; omega) (by omega), hwire_p]
            exact affine_refute f i (fun b' _ => op b') (fun _ => false)
              (fun b' x => by
                show f (Function.update x i b') = op b'
                rw [hfeq, Function.update_self]) h0 h1 hne hnc
          | bin op j k =>
            rw [hg] at hOut
            have hjk : j = A.length ∨ k = A.length := by
              simp [gateReads] at hOut
              omega
            by_cases hj : j = A.length
            · subst hj
              by_cases hk : k = A.length
              · subst hk
                have hfeq : ∀ x : Fin n → Bool, f x = op (x i) (x i) := by
                  intro x
                  rw [hfout x, hg]
                  show op ((runFrom x [] _).getD A.length false)
                    ((runFrom x [] _).getD A.length false) = op (x i) (x i)
                  rw [wire_prefix _ _ (by rw [hlen_c]; omega) (by omega), hwire_p]
                exact affine_refute f i (fun b' _ => op b' b') (fun _ => false)
                  (fun b' x => by
                    show f (Function.update x i b') = op b' b'
                    rw [hfeq, Function.update_self]) h0 h1 hne hnc
              · by_cases hkr : k < (A ++ CGate.var i :: B).length - 1
                · have hfeq : ∀ x : Fin n → Bool,
                      f x = op (x i) (wire (A ++ CGate.var i :: B) x k) := by
                    intro x
                    rw [hfout x, hg]
                    show op ((runFrom x [] _).getD A.length false)
                      ((runFrom x [] _).getD k false)
                      = op (x i) (wire (A ++ CGate.var i :: B) x k)
                    rw [wire_prefix _ _ (by rw [hlen_c]; omega) (by omega),
                      wire_prefix _ _ hkr (by omega), hwire_p]
                  exact affine_refute f i op
                    (fun x => wire (A ++ CGate.var i :: B) x k)
                    (fun b' x => by
                      show f (Function.update x i b') = _
                      rw [hfeq, Function.update_self, hinv x b' k hkr hk]) h0 h1 hne hnc
                · have hfeq : ∀ x : Fin n → Bool, f x = op (x i) false := by
                    intro x
                    rw [hfout x, hg]
                    show op ((runFrom x [] _).getD A.length false)
                      ((runFrom x [] _).getD k false) = op (x i) false
                    rw [wire_prefix _ _ (by rw [hlen_c]; omega) (by omega), hwire_p,
                      List.getD_eq_default _ _ (by
                        rw [runFrom_length, List.length_take]
                        simp
                        omega)]
                  exact affine_refute f i (fun b' _ => op b' false) (fun _ => false)
                    (fun b' x => by
                      show f (Function.update x i b') = op b' false
                      rw [hfeq, Function.update_self]) h0 h1 hne hnc
            · have hk : k = A.length := by
                rcases hjk with he | he
                · exact absurd he hj
                · exact he
              subst hk
              by_cases hjr : j < (A ++ CGate.var i :: B).length - 1
              · have hfeq : ∀ x : Fin n → Bool,
                    f x = op (wire (A ++ CGate.var i :: B) x j) (x i) := by
                  intro x
                  rw [hfout x, hg]
                  show op ((runFrom x [] _).getD j false)
                    ((runFrom x [] _).getD A.length false)
                    = op (wire (A ++ CGate.var i :: B) x j) (x i)
                  rw [wire_prefix _ _ (j := j) hjr (by omega),
                    wire_prefix _ _ (j := A.length) (by rw [hlen_c]; omega) (by omega),
                    hwire_p]
                exact affine_refute f i (fun b' y => op y b')
                  (fun x => wire (A ++ CGate.var i :: B) x j)
                  (fun b' x => by
                    show f (Function.update x i b') = _
                    rw [hfeq, Function.update_self, hinv x b' j hjr hj]) h0 h1 hne hnc
              · have hfeq : ∀ x : Fin n → Bool, f x = op false (x i) := by
                  intro x
                  rw [hfout x, hg]
                  show op ((runFrom x [] _).getD j false)
                    ((runFrom x [] _).getD A.length false) = op false (x i)
                  rw [List.getD_eq_default _ _ (by
                      rw [runFrom_length, List.length_take]
                      simp
                      omega),
                    wire_prefix _ _ (j := A.length) (by rw [hlen_c]; omega) (by omega),
                    hwire_p]
                exact affine_refute f i (fun b' _ => op false b') (fun _ => false)
                  (fun b' x => by
                    show f (Function.update x i b') = op false b'
                    rw [hfeq, Function.update_self]) h0 h1 hne hnc
        · -- nothing reads the var wire: f is blind to x i, contra hne
          have hinvall : ∀ (x : Fin n → Bool) (b' : Bool),
              f (Function.update x i b') = f x := by
            intro x b'
            rw [← hcomp (Function.update x i b'), ← hcomp x, output_eq_wire, output_eq_wire]
            exact wire_inv (A ++ CGate.var i :: B) i A.length
              ((A ++ CGate.var i :: B).length) (le_refl _)
              (fun v hv1 hv2 => by
                by_cases hvlast : v + 1 < (A ++ CGate.var i :: B).length
                · exact hR v hv1 hvlast
                · have hveq : v = (A ++ CGate.var i :: B).length - 1 := by omega
                  rw [hveq]
                  exact hOut)
              (fun v hv hvp => hvar_getD v hv hvp) x b'
              ((A ++ CGate.var i :: B).length - 1) (by rw [hlen_c]; omega)
              (by rw [hlen_c]; omega)
          exact hne (funext fun x => by
            show f (Function.update x i true) = f (Function.update x i false)
            rw [hinvall x true, hinvall x false])
  · -- == CASE A: at least two var-i gates: two constant kills ==
    obtain ⟨A, M, R, rfl⟩ := count_two_split (CGate.var i) c htwo
    have hlen_c : (A ++ CGate.var i :: M ++ CGate.var i :: R).length
        = A.length + 1 + M.length + 1 + R.length := by
      rw [List.length_append, List.length_cons, List.length_append, List.length_cons]
      omega
    have hsubst := computes_subst (A ++ CGate.var i :: M ++ CGate.var i :: R) f i b hcomp
    rw [show (A ++ CGate.var i :: M ++ CGate.var i :: R).map (substGateC i b)
        = A.map (substGateC i b) ++ CGate.cst b :: (M.map (substGateC i b)
          ++ CGate.cst b :: R.map (substGateC i b)) from by
      simp [substGateC_var_self]] at hsubst
    have hMR_ne : M.map (substGateC i b) ++ CGate.cst b :: R.map (substGateC i b) ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      rw [List.length_append, List.length_cons] at hlen
      simp at hlen
    have helim := computes_elim (A.map (substGateC i b))
      (M.map (substGateC i b) ++ CGate.cst b :: R.map (substGateC i b)) b
      (restrictF f i b) hsubst hMR_ne
    rw [List.map_append, List.map_cons,
      show elimGate (n := n) (A.map (substGateC i b)).length b (CGate.cst b)
        = CGate.cst b from rfl] at helim
    by_cases hRnil : R = []
    · -- the second constant is the output: the restriction is constant, contra
      subst hRnil
      exfalso
      obtain ⟨x, y, hxy⟩ := hgnc
      apply hxy
      simp only [List.map_nil] at helim
      rw [← List.append_assoc] at helim
      rw [← helim x, ← helim y, output_last_cst, output_last_cst]
    · have hR_ne : (R.map (substGateC i b)).map
          (elimGate (A.map (substGateC i b)).length b) ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        rw [List.length_map, List.length_map] at hlen
        cases R with
        | nil => exact hRnil rfl
        | cons a as => simp at hlen
      rw [← List.append_assoc] at helim
      have hfinal := cbudget_le_of_cst_mid _ _ b (restrictF f i b) helim hR_ne
      simp only [List.length_append, List.length_map] at hfinal
      omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.wire_inv
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.affine_refute
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.cbudget_twokill
