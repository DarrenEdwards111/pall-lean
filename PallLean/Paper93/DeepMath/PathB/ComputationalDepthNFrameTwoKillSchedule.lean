import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTwoKill

/-!
# N-Frame: the iterated two-kill schedule — `2N/3`, doubling the record on the SAT target

Iterating the two-kill dichotomy needs dependence *and* non-top-decomposability preserved along restrictions.  Two
structural facts make it compose:

  * **the dichotomy is value-free** (`budget_twokill_all`): the collapse analysis never used the restriction
    value, so the two-kill holds for *every* `b` — the schedule may choose its own values;
  * **slot-2 selectors are the right bits**: at value `false` they are inert in every construction, and each
    carries three behaviors — identity (empty-clause base: off = unsat, on = sat), constant-true (all-live base),
    constant-false (foreign empty clause) — so non-top-decomposability survives every prefix of restrictions.

  `TwoKillChain` / `twokill_schedule` — **PROVED, the engine**: a chain of live, non-top-decomposable steps gives
        `2·length + 1 ≤ budget f`.
  `twoKillChain_uniform` — **PROVED, the builder**: per-step behavior witnesses agreeing with every step's value
        off their own bit yield a chain in any order.
  `sat3_twokill_schedule` — **PROVED, the record**: `2·(sat3M N · sat3V N) + 1 ≤ budget (sat3Family N)` —
        roughly `2N/3`, doubling the previous `N/3` bound by killing two gates per step over all `m·v` slot-2
        selector bits.

## Honest scope

This is the classical `2n − O(1)` shape realized on the true target in the tree model.  Pushing the constant
further needs three-kills (deeper case analysis) and superlinear needs the DAG analogue with wire surgery — the
remaining rungs of W2, named and not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The value-free dichotomy -/

/-- **The dichotomy, for every restriction value (proved)**: the collapse never used the value. -/
theorem budget_twokill_all {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (hdep : DependsOnF f i) (hnt : ¬TopDecomp f i) (b : Bool) :
    budget (restrictF f i b) + 2 ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, hte, htv⟩ := Nat.sInf_mem hne
  have hbud : volume t = budget f := htv
  obtain ⟨x₁, x₀, hd, hnev⟩ := hdep
  have hvar : hasVar i t = true := by
    apply hasVar_of_depends i t x₁ x₀ (fun c hc => by
      by_contra hcc
      exact hc (hd c hcc))
    rw [show eval t = f from hte]
    exact hnev
  have hocc := hasVar_occ_pos i t hvar
  by_cases h1 : occCount i t = 1
  · obtain ⟨t', he, hcase⟩ := single_read_collapse i b t h1
    rcases hcase with hA | ⟨hB, op₂, s₂, hshape⟩ | ⟨u, hu⟩
    · have hcomp : eval t' = restrictF f i b := by
        funext x
        rw [he, substVar_eval, show eval t = f from hte]
        rfl
      have hb : budget (restrictF f i b) ≤ volume t' :=
        Nat.sInf_le ⟨t', hcomp, rfl⟩
      omega
    · exfalso
      apply hnt
      rcases hshape with rfl | rfl
      · have hocc₂ : occCount i s₂ = 0 := by
          have h' : (if i = i then 1 else 0) + occCount i s₂ = 1 := h1
          rw [if_pos rfl] at h'
          omega
        refine ⟨op₂, eval s₂, ?_, ?_⟩
        · intro x
          rw [← hte]
          rfl
        · intro x bb
          exact eval_update_of_hasVar_false i s₂ (occ_zero_hasVar_false i s₂ hocc₂) x bb
      · have hocc₂ : occCount i s₂ = 0 := by
          have h' : occCount i s₂ + (if i = i then 1 else 0) = 1 := h1
          rw [if_pos rfl] at h'
          omega
        refine ⟨fun a c => op₂ c a, eval s₂, ?_, ?_⟩
        · intro x
          rw [← hte]
          rfl
        · intro x bb
          exact eval_update_of_hasVar_false i s₂ (occ_zero_hasVar_false i s₂ hocc₂) x bb
    · exfalso
      apply hnt
      refine ⟨fun a _ => u a, fun _ => false, ?_, fun _ _ => rfl⟩
      intro x
      rw [← hte]
      exact hu x
  · have h2 : 2 ≤ occCount i t := by omega
    rcases subst_reduce_many i b t with hvart | ⟨t', he, hv⟩
    · exfalso
      subst hvart
      have h' : occCount i (Trans.var i) = 1 := by
        show (if i = i then 1 else 0) = 1
        rw [if_pos rfl]
      omega
    · have hcomp : eval t' = restrictF f i b := by
        funext x
        rw [he, substVar_eval, show eval t = f from hte]
        rfl
      have hb : budget (restrictF f i b) ≤ volume t' :=
        Nat.sInf_le ⟨t', hcomp, rfl⟩
      omega

/-! ### The chain and the engine -/

/-- A two-kill schedule: each step's variable is live and non-top-decomposable for the current function. -/
def TwoKillChain {n : ℕ} : ((Fin n → Bool) → Bool) → List (Fin n × Bool) → Prop
  | _, [] => True
  | f, s :: rest => DependsOnF f s.1 ∧ ¬TopDecomp f s.1 ∧
      TwoKillChain (restrictF f s.1 s.2) rest

/-- **THE ITERATED TWO-KILL ENGINE (proved)**: `2·length + 1 ≤ budget f`. -/
theorem twokill_schedule {n : ℕ} (f : (Fin n → Bool) → Bool)
    (steps : List (Fin n × Bool)) (h : TwoKillChain f steps) :
    2 * steps.length + 1 ≤ budget f := by
  induction steps generalizing f with
  | nil =>
    have := budget_pos f
    show 2 * 0 + 1 ≤ budget f
    omega
  | cons s rest ih =>
    have h' : DependsOnF f s.1 ∧ ¬TopDecomp f s.1 ∧
        TwoKillChain (restrictF f s.1 s.2) rest := h
    obtain ⟨hdep, hnt, hchain⟩ := h'
    have hkill := budget_twokill_all f s.1 hdep hnt s.2
    have hih := ih (restrictF f s.1 s.2) hchain
    show 2 * (rest.length + 1) + 1 ≤ budget f
    omega

/-- Restriction commutes past an update at a compliant point. -/
theorem restrict_update_eq {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (i' : Fin n) (a : Bool) (x : Fin n → Bool) (hne : i' ≠ i) (hx : x i = b) :
    restrictF f i b (Function.update x i' a) = f (Function.update x i' a) := by
  show f (Function.update (Function.update x i' a) i b) = f (Function.update x i' a)
  rw [Function.update_comm hne, ← hx, Function.update_eq_self]

/-- Three behaviors refute top decomposition. -/
theorem notTopDecomp_of_behaviors {n : ℕ} (g : (Fin n → Bool) → Bool) (i : Fin n)
    (xP y1 y0 : Fin n → Bool)
    (hP : ∀ a, g (Function.update xP i a) = a)
    (h1 : ∀ a, g (Function.update y1 i a) = true)
    (h0 : ∀ a, g (Function.update y0 i a) = false) :
    ¬TopDecomp g i := by
  rintro ⟨op, h, hfeq, hfree⟩
  have hgen : ∀ (y : Fin n → Bool) (a : Bool),
      g (Function.update y i a) = op a (h y) := by
    intro y a
    rw [hfeq (Function.update y i a)]
    congr 1
    · exact Function.update_self _ _ _
    · exact hfree y a
  have F1 : op false (h xP) = false := (hgen xP false).symm.trans (hP false)
  have F2 : op true (h xP) = true := (hgen xP true).symm.trans (hP true)
  have F3 : op false (h y1) = true := (hgen y1 false).symm.trans (h1 false)
  have F4 : op true (h y1) = true := (hgen y1 true).symm.trans (h1 true)
  have F5 : op false (h y0) = false := (hgen y0 false).symm.trans (h0 false)
  have F6 : op true (h y0) = false := (hgen y0 true).symm.trans (h0 true)
  cases hv1 : h xP <;> cases hv2 : h y1 <;> cases hv3 : h y0 <;>
    rw [hv1] at F1 F2 <;> rw [hv2] at F3 F4 <;> rw [hv3] at F5 F6 <;>
    first
      | exact Bool.noConfusion (F1.symm.trans F3)
      | exact Bool.noConfusion (F2.symm.trans F6)
      | exact Bool.noConfusion (F3.symm.trans F5)

/-- **The chain builder (proved)**: per-step behavior witnesses agreeing with every step's value off their own bit
yield a two-kill chain in any order. -/
theorem twoKillChain_uniform {n : ℕ} (f : (Fin n → Bool) → Bool)
    (steps : List (Fin n × Bool)) (hnd : (steps.map Prod.fst).Nodup)
    (hprop : ∀ s ∈ steps, ∃ xP y1 y0 : Fin n → Bool,
      (∀ a, f (Function.update xP s.1 a) = a) ∧
      (∀ a, f (Function.update y1 s.1 a) = true) ∧
      (∀ a, f (Function.update y0 s.1 a) = false) ∧
      (∀ s' ∈ steps, s'.1 ≠ s.1 →
        xP s'.1 = s'.2 ∧ y1 s'.1 = s'.2 ∧ y0 s'.1 = s'.2)) :
    TwoKillChain f steps := by
  induction steps generalizing f with
  | nil => trivial
  | cons s rest ih =>
    have hnd' := List.nodup_cons.mp (by
      show (s.1 :: rest.map Prod.fst).Nodup
      exact hnd)
    obtain ⟨xP, y1, y0, hP, h1, h0, hagree⟩ := hprop s List.mem_cons_self
    refine ⟨?_, ?_, ?_⟩
    · -- dependence from the identity behavior
      refine ⟨Function.update xP s.1 true, Function.update xP s.1 false, ?_, ?_⟩
      · intro c hc
        by_contra hcc
        apply hc
        rw [Function.update_of_ne hcc, Function.update_of_ne hcc]
      · rw [hP true, hP false]
        decide
    · exact notTopDecomp_of_behaviors f s.1 xP y1 y0 hP h1 h0
    · apply ih
      · exact hnd'.2
      · intro s' hs'
        obtain ⟨xP', y1', y0', hP', h1', h0', hagree'⟩ :=
          hprop s' (List.mem_cons_of_mem s hs')
        have hne_heads : s.1 ≠ s'.1 := by
          intro hcc
          apply hnd'.1
          rw [hcc]
          exact List.mem_map_of_mem hs'
        have hag := hagree' s List.mem_cons_self hne_heads
        refine ⟨xP', y1', y0', ?_, ?_, ?_, ?_⟩
        · intro a
          rw [restrict_update_eq f s.1 s.2 s'.1 a xP' (Ne.symm hne_heads) hag.1]
          exact hP' a
        · intro a
          rw [restrict_update_eq f s.1 s.2 s'.1 a y1' (Ne.symm hne_heads) hag.2.1]
          exact h1' a
        · intro a
          rw [restrict_update_eq f s.1 s.2 s'.1 a y0' (Ne.symm hne_heads) hag.2.2]
          exact h0' a
        · intro s'' hs'' hne''
          exact hagree' s'' (List.mem_cons_of_mem s hs'') hne''

/-! ### The SAT slot-2 witnesses -/

/-- The empty-clause base for block `c`: every other clause carries a live variable-0 selector. -/
def sat3ZBase (N : ℕ) (c : Fin (sat3M N)) : Fin N → Bool :=
  fun bb => decide (bb.val % sat3D N = 0 ∧ bb.val / sat3D N ≠ c.val ∧
    bb.val / sat3D N < sat3M N)

/-- The all-live base: every clause carries a live variable-0 selector. -/
def sat3AllLive (N : ℕ) : Fin N → Bool :=
  fun bb => decide (bb.val % sat3D N = 0 ∧ bb.val / sat3D N < sat3M N)

/-- The slot-2 selector bit for `(c, jv)`. -/
def sat3S2Sel (N : ℕ) (c : Fin (sat3M N)) (jv : Fin (sat3V N)) : Fin N :=
  sat3Bit N c ⟨2, by omega⟩ jv.val (by have := jv.isLt; omega)

theorem sat3S2Sel_rem (N : ℕ) (c : Fin (sat3M N)) (jv : Fin (sat3V N)) :
    (sat3S2Sel N c jv).val % sat3D N = 2 * (sat3V N + 1) + jv.val := by
  show (sat3Bit N c ⟨2, by omega⟩ jv.val (by have := jv.isLt; omega)).val % sat3D N = _
  rw [sat3Bit_rem]

theorem sat3S2Sel_div (N : ℕ) (c : Fin (sat3M N)) (jv : Fin (sat3V N)) :
    (sat3S2Sel N c jv).val / sat3D N = c.val :=
  sat3Bit_clause N c ⟨2, by omega⟩ jv.val (by have := jv.isLt; omega)

/-- Bases vanish on every slot-2 selector. -/
theorem sat3ZBase_s2 (N : ℕ) (c c₂ : Fin (sat3M N)) (j₂ : Fin (sat3V N)) :
    sat3ZBase N c (sat3S2Sel N c₂ j₂) = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨hmod, -, -⟩
  rw [sat3S2Sel_rem] at hmod
  omega

theorem sat3AllLive_s2 (N : ℕ) (c₂ : Fin (sat3M N)) (j₂ : Fin (sat3V N)) :
    sat3AllLive N (sat3S2Sel N c₂ j₂) = false := by
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨hmod, -⟩
  rw [sat3S2Sel_rem] at hmod
  omega

/-- The flipped base is satisfiable: clause `c` becomes the positive literal on `jv`. -/
theorem sat3ZBase_flip_sat (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (jv : Fin (sat3V N)) :
    sat3Family N (Function.update (sat3ZBase N c) (sat3S2Sel N c jv) true) = true := by
  apply decide_eq_true
  refine ⟨fun _ => true, sat3Eval_true_of_all N _ _ ?_⟩
  intro cl
  by_cases hcl : cl = c
  · subst hcl
    refine ⟨⟨2, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨2, by omega⟩ jv ?_ ?_⟩
    · show Function.update (sat3ZBase N cl) (sat3S2Sel N cl jv) true
          (sat3S2Sel N cl jv) = true
      rw [Function.update_self]
    · have hne : sat3Bit N cl ⟨2, by omega⟩ (sat3V N) (by omega) ≠ sat3S2Sel N cl jv := by
        intro hcontra
        have hr := sat3S2Sel_rem N cl jv
        rw [← hcontra] at hr
        rw [sat3Bit_rem] at hr
        have hv' : (2 : ℕ) * (sat3V N + 1) + sat3V N = 2 * (sat3V N + 1) + jv.val := hr
        have := jv.isLt
        omega
      rw [Function.update_of_ne hne]
      have hz : sat3ZBase N cl (sat3Bit N cl ⟨2, by omega⟩ (sat3V N) (by omega)) = false := by
        show decide _ = false
        rw [decide_eq_false_iff_not]
        rintro ⟨hmod, -, -⟩
        rw [sat3Bit_rem] at hmod
        have hv' : (2 : ℕ) * (sat3V N + 1) + sat3V N = 0 := hmod
        omega
      rw [hz]
      rfl
  · refine ⟨⟨0, by omega⟩,
      sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
    · have hne : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)
          ≠ sat3S2Sel N c jv := by
        intro hcontra
        have hr := sat3S2Sel_rem N c jv
        rw [← hcontra] at hr
        rw [sat3Bit_rem] at hr
        have hv' : (0 : ℕ) * (sat3V N + 1) + 0 = 2 * (sat3V N + 1) + jv.val := hr
        omega
      rw [Function.update_of_ne hne]
      show decide _ = true
      rw [decide_eq_true_eq]
      refine ⟨?_, ?_, ?_⟩
      · rw [sat3Bit_rem]
        show (0 : ℕ) * (sat3V N + 1) + 0 = 0
        omega
      · rw [sat3Bit_clause]
        exact fun h => hcl (Fin.ext h)
      · rw [sat3Bit_clause]
        exact cl.isLt
    · have hne : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega) ≠ sat3S2Sel N c jv := by
        intro hcontra
        have hr := sat3S2Sel_rem N c jv
        rw [← hcontra] at hr
        rw [sat3Bit_rem] at hr
        have hv' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 2 * (sat3V N + 1) + jv.val := hr
        omega
      rw [Function.update_of_ne hne]
      have hz : sat3ZBase N c (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
        show decide _ = false
        rw [decide_eq_false_iff_not]
        rintro ⟨hmod, -, -⟩
        rw [sat3Bit_rem] at hmod
        have hv' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 0 := hmod
        omega
      rw [hz]
      rfl

/-- The base is unsatisfiable: clause `c` is empty. -/
theorem sat3ZBase_unsat (N : ℕ) (c : Fin (sat3M N)) :
    sat3Family N (sat3ZBase N c) = false := by
  apply sat3Family_false_of_empty_clause N _ c
  intro t i
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨-, hdiv, -⟩
  exact hdiv (sat3Bit_clause N c t i.val (by have := i.isLt; omega))

/-- The all-live base is satisfiable whatever the slot-2 selector does. -/
theorem sat3AllLive_flip_sat (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (jv : Fin (sat3V N)) (a : Bool) :
    sat3Family N (Function.update (sat3AllLive N) (sat3S2Sel N c jv) a) = true := by
  apply decide_eq_true
  refine ⟨fun _ => true, sat3Eval_true_of_all N _ _ ?_⟩
  intro cl
  refine ⟨⟨0, by omega⟩,
    sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
  · have hne : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega)
        ≠ sat3S2Sel N c jv := by
      intro hcontra
      have hr := sat3S2Sel_rem N c jv
      rw [← hcontra] at hr
      rw [sat3Bit_rem] at hr
      have hv' : (0 : ℕ) * (sat3V N + 1) + 0 = 2 * (sat3V N + 1) + jv.val := hr
      omega
    rw [Function.update_of_ne hne]
    show decide _ = true
    rw [decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + 0 = 0
      omega
    · rw [sat3Bit_clause]
      exact cl.isLt
  · have hne : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega) ≠ sat3S2Sel N c jv := by
      intro hcontra
      have hr := sat3S2Sel_rem N c jv
      rw [← hcontra] at hr
      rw [sat3Bit_rem] at hr
      have hv' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 2 * (sat3V N + 1) + jv.val := hr
      omega
    rw [Function.update_of_ne hne]
    have hz : sat3AllLive N (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
      show decide _ = false
      rw [decide_eq_false_iff_not]
      rintro ⟨hmod, -⟩
      rw [sat3Bit_rem] at hmod
      have hv' : (0 : ℕ) * (sat3V N + 1) + sat3V N = 0 := hmod
      omega
    rw [hz]
    rfl

/-- A foreign empty clause survives the slot-2 flip: constant-false behavior. -/
theorem sat3ZBase_foreign_unsat (N : ℕ) (c c' : Fin (sat3M N)) (hcc : c'.val ≠ c.val)
    (jv : Fin (sat3V N)) (a : Bool) :
    sat3Family N (Function.update (sat3ZBase N c') (sat3S2Sel N c jv) a) = false := by
  apply sat3Family_false_of_empty_clause N _ c'
  intro t i
  have hne : sat3Bit N c' t i.val (by have := i.isLt; omega) ≠ sat3S2Sel N c jv := by
    intro hcontra
    apply hcc
    rw [← sat3Bit_clause N c' t i.val (by have := i.isLt; omega), hcontra]
    exact sat3S2Sel_div N c jv
  rw [Function.update_of_ne hne]
  show decide _ = false
  rw [decide_eq_false_iff_not]
  rintro ⟨-, hdiv, -⟩
  exact hdiv (sat3Bit_clause N c' t i.val (by have := i.isLt; omega))

/-! ### The record -/

/-- **THE ITERATED TWO-KILL ON SAT (proved)**: `2·m·v + 1 ≤ budget (sat3Family N)` — roughly `2N/3`, doubling the
previous record by killing two gates at every one of the `m·v` slot-2 selector bits. -/
theorem sat3_twokill_schedule (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N) :
    2 * (sat3M N * sat3V N) + 1 ≤ budget (sat3Family N) := by
  set steps : List (Fin N × Bool) :=
    (pairList (List.finRange (sat3M N)) (List.finRange (sat3V N))).map
      (fun p => (sat3S2Sel N p.1 p.2, false)) with hsteps
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
  have hnd : (steps.map Prod.fst).Nodup := by
    rw [hsteps, List.map_map]
    exact (pairList_nodup _ _ (List.nodup_finRange _) (List.nodup_finRange _)).map
      (fun a b hab => hinj (by
        have hab' : (fun p : Fin (sat3M N) × Fin (sat3V N) => sat3S2Sel N p.1 p.2) a
            = (fun p : Fin (sat3M N) × Fin (sat3V N) => sat3S2Sel N p.1 p.2) b := hab
        exact hab'))
  have hprop : ∀ s ∈ steps, ∃ xP y1 y0 : Fin N → Bool,
      (∀ a, sat3Family N (Function.update xP s.1 a) = a) ∧
      (∀ a, sat3Family N (Function.update y1 s.1 a) = true) ∧
      (∀ a, sat3Family N (Function.update y0 s.1 a) = false) ∧
      (∀ s' ∈ steps, s'.1 ≠ s.1 →
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
  have hchain := twoKillChain_uniform (sat3Family N) steps hnd hprop
  have hbound := twokill_schedule (sat3Family N) steps hchain
  have hlen : steps.length = sat3M N * sat3V N := by
    rw [hsteps, List.length_map, pairList_length, List.length_finRange,
      List.length_finRange]
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_twokill_all
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.twokill_schedule
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.twoKillChain_uniform
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_twokill_schedule
