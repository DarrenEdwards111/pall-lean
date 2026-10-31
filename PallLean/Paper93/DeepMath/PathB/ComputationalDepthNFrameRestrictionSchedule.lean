import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameGateElimination

/-!
# N-Frame: the dependence-preserving restriction schedule — gate elimination, iterated at scale

The single strict step (`budget_restrict_lt`) becomes a lower-bound engine only when iterated along a schedule of
variables each still live after the earlier fixings.  This file builds the schedule calculus and runs it on the SAT
target at scale `m·(v−1) ≈ N/3`.

**The calculus (proved).**
  `LiveChain` — the schedule predicate: each step's variable is live for the currently restricted function.
  `depends_lift` / `depends_two_budget` — liveness of the *next* step lifts to the unrestricted function, so any
        chain with a successor step has two distinct live variables, hence budget `≥ 2`: the strict step's
        hypothesis is self-supplied by the chain.
  `budget_schedule` — **the engine**: `LiveChain f steps → budget (restrictAll f steps) + steps.length ≤ budget f + 1`.
  `liveChain_uniform` — **the schedule builder**: a family of dependence pairs, one per step, all *agreeing with
        every step's restriction value off their own bit*, yields a live chain in any order (nodup firsts).

**The SAT schedule (proved).**  The selector-pair construction is zero on *every* slot-0 selector with variable
index `≥ 1` — so all `m·(v−1)` such bits form one mutually compatible schedule: `sat3_schedule_lb`:
`m·(v−1) ≤ budget (sat3Family N)` — the linear bound re-derived through the strict engine, composition validated
end-to-end on the true target.

## Honest scope

In the tree model each step kills exactly one node, so schedules cap at linear — consistent with the dependency
bound already proved.  Superlinear gate elimination needs per-step **multi-kills** (basis-specific, DAG-model, with
the wire surgery this tree formulation sidesteps): that is the open rung of W2, named and not claimed.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The schedule calculus -/

/-- Restrict one variable. -/
def restrictF {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool) :
    (Fin n → Bool) → Bool :=
  fun x => f (Function.update x i b)

/-- Dependence in pair form. -/
def DependsOnF {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ x₁ x₀ : Fin n → Bool, (∀ c, x₁ c ≠ x₀ c → c = i) ∧ f x₁ ≠ f x₀

/-- Apply a whole schedule of restrictions. -/
def restrictAll {n : ℕ} : ((Fin n → Bool) → Bool) → List (Fin n × Bool) →
    ((Fin n → Bool) → Bool)
  | f, [] => f
  | f, s :: rest => restrictAll (restrictF f s.1 s.2) rest

/-- The schedule predicate: each step's variable is live for the currently restricted function. -/
def LiveChain {n : ℕ} : ((Fin n → Bool) → Bool) → List (Fin n × Bool) → Prop
  | _, [] => True
  | f, s :: rest => DependsOnF f s.1 ∧ LiveChain (restrictF f s.1 s.2) rest

theorem budget_pos {n : ℕ} (f : (Fin n → Bool) → Bool) : 1 ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, -, hv⟩ := Nat.sInf_mem hne
  show 1 ≤ sInf {v | ∃ t : Trans n, eval t = f ∧ volume t = v}
  rw [← hv]
  exact volume_pos t

/-- Restriction never increases the budget. -/
theorem budget_restrict_le {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool) :
    budget (restrictF f i b) ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, hte, htv⟩ := Nat.sInf_mem hne
  have hcomp : eval (substVar i b t) = restrictF f i b := by
    funext x
    rw [substVar_eval, show eval t = f from hte]
    rfl
  have hb : budget (restrictF f i b) ≤ volume (substVar i b t) :=
    Nat.sInf_le ⟨substVar i b t, hcomp, rfl⟩
  rw [substVar_volume] at hb
  have hEq : budget f = sInf {v | ∃ t : Trans n, eval t = f ∧ volume t = v} := rfl
  omega

theorem two_hasVar_volume {n : ℕ} (t : Trans n) (i i' : Fin n) (hii : i ≠ i')
    (h1 : hasVar i t = true) (h2 : hasVar i' t = true) : 2 ≤ volume t := by
  cases t with
  | var j =>
    exfalso
    have h1' : decide (j = i) = true := h1
    have h2' : decide (j = i') = true := h2
    have e1 := of_decide_eq_true h1'
    have e2 := of_decide_eq_true h2'
    exact hii (e1 ▸ e2)
  | cst c => exact absurd h1 (by simp [hasVar])
  | un op s =>
    show 2 ≤ volume s + 1
    have := volume_pos s
    omega
  | bin op s t =>
    show 2 ≤ volume s + volume t + 1
    have := volume_pos s
    have := volume_pos t
    omega

/-- Two distinct live variables force budget `≥ 2`. -/
theorem depends_two_budget {n : ℕ} (f : (Fin n → Bool) → Bool) (i i' : Fin n)
    (hii : i ≠ i') (hi : DependsOnF f i) (hi' : DependsOnF f i') : 2 ≤ budget f := by
  have hne : {v | ∃ t : Trans n, eval t = f ∧ volume t = v}.Nonempty :=
    ⟨volume (dnfFor f), dnfFor f, eval_dnfFor f, rfl⟩
  obtain ⟨t, hte, htv⟩ := Nat.sInf_mem hne
  obtain ⟨x₁, x₀, hd, hnev⟩ := hi
  obtain ⟨y₁, y₀, hd', hnev'⟩ := hi'
  have hv1 : hasVar i t = true := by
    apply hasVar_of_depends i t x₁ x₀ (fun c hc => by
      by_contra hcc
      exact hc (hd c hcc))
    rw [show eval t = f from hte]
    exact hnev
  have hv2 : hasVar i' t = true := by
    apply hasVar_of_depends i' t y₁ y₀ (fun c hc => by
      by_contra hcc
      exact hc (hd' c hcc))
    rw [show eval t = f from hte]
    exact hnev'
  have := two_hasVar_volume t i i' hii hv1 hv2
  have hEq : budget f = sInf {v | ∃ t : Trans n, eval t = f ∧ volume t = v} := rfl
  omega

/-- Liveness after a restriction lifts to the unrestricted function, on a distinct variable. -/
theorem depends_lift {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) (b : Bool)
    (i' : Fin n) (h : DependsOnF (restrictF f i b) i') :
    i' ≠ i ∧ DependsOnF f i' := by
  obtain ⟨x₁, x₀, hd, hne⟩ := h
  have hii : i' ≠ i := by
    intro hcc
    apply hne
    show f (Function.update x₁ i b) = f (Function.update x₀ i b)
    congr 1
    funext c
    by_cases hc : c = i
    · rw [hc, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hc, Function.update_of_ne hc]
      by_contra hcv
      exact hc ((hd c hcv).trans hcc)
  refine ⟨hii, Function.update x₁ i b, Function.update x₀ i b, ?_, hne⟩
  intro c hcv
  by_cases hc : c = i
  · exfalso
    apply hcv
    rw [hc, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hc, Function.update_of_ne hc] at hcv
    exact hd c hcv

/-- **THE SCHEDULE ENGINE (proved)**: a live chain of restrictions strictly kills one gate per step (except
possibly the last): `budget (restrictAll f steps) + steps.length ≤ budget f + 1`. -/
theorem budget_schedule {n : ℕ} (f : (Fin n → Bool) → Bool)
    (steps : List (Fin n × Bool)) (h : LiveChain f steps) :
    budget (restrictAll f steps) + steps.length ≤ budget f + 1 := by
  induction steps generalizing f with
  | nil =>
    show budget f + 0 ≤ budget f + 1
    omega
  | cons s rest ih =>
    have h' : DependsOnF f s.1 ∧ LiveChain (restrictF f s.1 s.2) rest := h
    obtain ⟨hdep, hchain⟩ := h'
    cases rest with
    | nil =>
      have h1 := budget_restrict_le f s.1 s.2
      show budget (restrictF f s.1 s.2) + (0 + 1) ≤ budget f + 1
      omega
    | cons s' rest' =>
      have hchain' : DependsOnF (restrictF f s.1 s.2) s'.1 ∧
          LiveChain (restrictF (restrictF f s.1 s.2) s'.1 s'.2) rest' := hchain
      obtain ⟨hii, hdep'⟩ := depends_lift f s.1 s.2 s'.1 hchain'.1
      have h2 : 2 ≤ budget f := depends_two_budget f s.1 s'.1 (Ne.symm hii) hdep hdep'
      obtain ⟨x₁, x₀, hd, hnev⟩ := hdep
      have hstrict : budget (restrictF f s.1 s.2) + 1 ≤ budget f :=
        budget_restrict_lt f s.1 s.2 x₁ x₀ (fun c hc => by
          by_contra hcc
          exact hc (hd c hcc)) hnev h2
      have hih := ih (restrictF f s.1 s.2) hchain
      show budget (restrictAll (restrictF f s.1 s.2) (s' :: rest'))
          + ((s' :: rest').length + 1) ≤ budget f + 1
      have hlen : (s' :: rest').length = rest'.length + 1 := rfl
      omega

/-- **The schedule builder (proved)**: dependence pairs agreeing with every step's value off their own bit yield a
live chain, in any order. -/
theorem liveChain_uniform {n : ℕ} (f : (Fin n → Bool) → Bool)
    (steps : List (Fin n × Bool)) (hnd : (steps.map Prod.fst).Nodup)
    (hpairs : ∀ s ∈ steps, ∃ x₁ x₀ : Fin n → Bool,
      (∀ c, x₁ c ≠ x₀ c → c = s.1) ∧ f x₁ ≠ f x₀ ∧
      (∀ s' ∈ steps, s'.1 ≠ s.1 → x₁ s'.1 = s'.2 ∧ x₀ s'.1 = s'.2)) :
    LiveChain f steps := by
  induction steps generalizing f with
  | nil => trivial
  | cons s rest ih =>
    have hnd' := List.nodup_cons.mp (by
      show (s.1 :: rest.map Prod.fst).Nodup
      exact hnd)
    refine ⟨?_, ?_⟩
    · obtain ⟨x₁, x₀, hd, hne, -⟩ := hpairs s List.mem_cons_self
      exact ⟨x₁, x₀, hd, hne⟩
    · apply ih
      · exact hnd'.2
      · intro s' hs'
        obtain ⟨x₁, x₀, hd, hne, hagree⟩ := hpairs s' (List.mem_cons_of_mem s hs')
        have hne_heads : s.1 ≠ s'.1 := by
          intro hcc
          apply hnd'.1
          rw [hcc]
          exact List.mem_map_of_mem hs'
        have hag := hagree s List.mem_cons_self hne_heads
        refine ⟨x₁, x₀, hd, ?_, ?_⟩
        · show f (Function.update x₁ s.1 s.2) ≠ f (Function.update x₀ s.1 s.2)
          rw [show Function.update x₁ s.1 s.2 = x₁ from by
              rw [← hag.1]
              exact Function.update_eq_self s.1 x₁,
            show Function.update x₀ s.1 s.2 = x₀ from by
              rw [← hag.2]
              exact Function.update_eq_self s.1 x₀]
          exact hne
        · intro s'' hs'' hne''
          exact hagree s'' (List.mem_cons_of_mem s hs'') hne''

/-! ### Product-list helpers -/

def pairList {α β : Type} : List α → List β → List (α × β)
  | [], _ => []
  | a :: as, l₂ => (l₂.map (fun b => (a, b))) ++ pairList as l₂

theorem pairList_length {α β : Type} (l₁ : List α) (l₂ : List β) :
    (pairList l₁ l₂).length = l₁.length * l₂.length := by
  induction l₁ with
  | nil =>
    show ([] : List (α × β)).length = ([] : List α).length * l₂.length
    simp
  | cons a as ih =>
    show ((l₂.map (fun b => (a, b))) ++ pairList as l₂).length = (as.length + 1) * l₂.length
    rw [List.length_append, List.length_map, ih]
    ring

theorem pairList_fst_mem {α β : Type} (l₁ : List α) (l₂ : List β) :
    ∀ q : α × β, q ∈ pairList l₁ l₂ → q.1 ∈ l₁ := by
  induction l₁ with
  | nil =>
    intro q hq
    exact absurd hq List.not_mem_nil
  | cons a as ih =>
    intro q hq
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (ih q h)

theorem pairList_nodup {α β : Type} (l₁ : List α) (l₂ : List β)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) : (pairList l₁ l₂).Nodup := by
  induction l₁ with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    have h₁' := List.nodup_cons.mp h₁
    show ((l₂.map (fun b => (a, b))) ++ pairList as l₂).Nodup
    refine List.Nodup.append ?_ (ih h₁'.2) ?_
    · exact h₂.map (fun b b' hb => congrArg Prod.snd hb)
    · intro q hq hq'
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hq
      exact h₁'.1 (pairList_fst_mem as l₂ (a, b) hq')

/-! ### The schedule-compatible SAT pair: zero on the whole schedule -/

/-- **The schedule-compatible pair (proved)**: the empty-clause base and one-flip corner for `(c, jv)` — with both
components `false` on every slot-0 selector of variable index `≥ 1` other than the flip itself. -/
theorem sat3_selector_pair_zeroD (N : ℕ) (hv : 1 ≤ sat3V N) (c : Fin (sat3M N))
    (jv : Fin (sat3V N)) :
    ∃ x₁ x₀ : Fin N → Bool, sat3Family N x₁ = true ∧ sat3Family N x₀ = false ∧
      (∀ b : Fin N, x₁ b ≠ x₀ b →
        b = sat3Bit N c ⟨0, by omega⟩ jv.val (by have := jv.isLt; omega)) ∧
      (∀ (c'' : Fin (sat3M N)) (j'' : Fin (sat3V N)), 1 ≤ j''.val →
        sat3Bit N c'' ⟨0, by omega⟩ j''.val (by have := j''.isLt; omega)
          ≠ sat3Bit N c ⟨0, by omega⟩ jv.val (by have := jv.isLt; omega) →
        x₁ (sat3Bit N c'' ⟨0, by omega⟩ j''.val (by have := j''.isLt; omega)) = false ∧
        x₀ (sat3Bit N c'' ⟨0, by omega⟩ j''.val (by have := j''.isLt; omega)) = false) := by
  have hDpos : 0 < sat3D N := sat3D_pos N
  set flip : Fin N := sat3Bit N c ⟨0, by omega⟩ jv.val (by have := jv.isLt; omega) with hflip
  set z : Fin N → Bool := fun b =>
    decide (b.val % sat3D N = 0 ∧ b.val / sat3D N ≠ c.val ∧ b.val / sat3D N < sat3M N)
    with hz
  have hflip_rem : flip.val % sat3D N = jv.val := by
    rw [hflip, sat3Bit_rem]
    show (0 : ℕ) * (sat3V N + 1) + jv.val = jv.val
    omega
  have hflip_div : flip.val / sat3D N = c.val := by
    rw [hflip]
    exact sat3Bit_clause N c ⟨0, by omega⟩ jv.val (by have := jv.isLt; omega)
  refine ⟨Function.update z flip true, z, ?_, ?_, ?_, ?_⟩
  · -- the flipped corner is satisfiable by the all-true assignment
    apply decide_eq_true
    refine ⟨fun _ => true, sat3Eval_true_of_all N _ _ ?_⟩
    intro cl
    by_cases hcl : cl = c
    · subst hcl
      refine ⟨⟨0, by omega⟩, sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ jv ?_ ?_⟩
      · rw [Function.update_self]
      · have hr1 : (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
            = sat3V N := by
          rw [sat3Bit_rem]
          show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
          omega
        have hne : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega) ≠ flip := by
          intro hcontra
          rw [hcontra, hflip_rem] at hr1
          have := jv.isLt
          omega
        rw [Function.update_of_ne hne]
        have hzs : z (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
          show decide _ = false
          rw [decide_eq_false_iff_not]
          rintro ⟨hmod, -, -⟩
          rw [hr1] at hmod
          omega
        rw [hzs]
        rfl
    · refine ⟨⟨0, by omega⟩,
        sat3Lit_true_of_selected N _ _ cl ⟨0, by omega⟩ ⟨0, hv⟩ ?_ ?_⟩
      · have hne : sat3Bit N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val
            (by omega) ≠ flip := by
          intro hcontra
          apply hcl
          apply Fin.ext
          rw [← sat3Bit_clause N cl ⟨0, by omega⟩ (⟨0, hv⟩ : Fin (sat3V N)).val (by omega),
            hcontra, hflip_div]
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
      · have hr1 : (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)).val % sat3D N
            = sat3V N := by
          rw [sat3Bit_rem]
          show (0 : ℕ) * (sat3V N + 1) + sat3V N = sat3V N
          omega
        have hne : sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega) ≠ flip := by
          intro hcontra
          rw [hcontra, hflip_rem] at hr1
          have := jv.isLt
          omega
        rw [Function.update_of_ne hne]
        have hzs : z (sat3Bit N cl ⟨0, by omega⟩ (sat3V N) (by omega)) = false := by
          show decide _ = false
          rw [decide_eq_false_iff_not]
          rintro ⟨hmod, -, -⟩
          rw [hr1] at hmod
          omega
        rw [hzs]
        rfl
  · -- the base is unsatisfiable: clause c is empty
    apply sat3Family_false_of_empty_clause N z c
    intro t i
    show decide _ = false
    rw [decide_eq_false_iff_not]
    rintro ⟨-, hdiv, -⟩
    exact hdiv (sat3Bit_clause N c t i.val (by have := i.isLt; omega))
  · -- the pair differs only at the flip
    intro b hb
    by_contra hcon
    exact hb (Function.update_of_ne hcon true z)
  · -- zero on the whole schedule
    intro c'' j'' hj1 hnef
    have hr : (sat3Bit N c'' ⟨0, by omega⟩ j''.val
        (by have := j''.isLt; omega)).val % sat3D N = j''.val := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + j''.val = j''.val
      omega
    have hz0 : z (sat3Bit N c'' ⟨0, by omega⟩ j''.val (by have := j''.isLt; omega))
        = false := by
      show decide _ = false
      rw [decide_eq_false_iff_not]
      rintro ⟨hmod, -, -⟩
      rw [hr] at hmod
      omega
    refine ⟨?_, hz0⟩
    rw [Function.update_of_ne hnef]
    exact hz0

/-! ### The SAT schedule at scale m·(v−1) -/

/-- The schedule: every slot-0 selector with variable index `≥ 1`, restricted to `false`. -/
def sat3Sched (N : ℕ) : List (Fin N × Bool) :=
  (pairList (List.finRange (sat3M N)) (List.finRange (sat3V N - 1))).map
    (fun p => (sat3Bit N p.1 ⟨0, by omega⟩ (p.2.val + 1) (by have := p.2.isLt; omega), false))

theorem sat3Sched_length (N : ℕ) :
    (sat3Sched N).length = sat3M N * (sat3V N - 1) := by
  unfold sat3Sched
  rw [List.length_map, pairList_length, List.length_finRange, List.length_finRange]

/-- **The SAT schedule is live end-to-end (proved)**, hence the linear bound through the strict engine. -/
theorem sat3_schedule_lb (N : ℕ) (hv : 1 ≤ sat3V N) :
    sat3M N * (sat3V N - 1) ≤ budget (sat3Family N) := by
  -- the schedule's bits are pairwise distinct
  have hinj : Function.Injective
      (fun p : Fin (sat3M N) × Fin (sat3V N - 1) =>
        sat3Bit N p.1 ⟨0, by omega⟩ (p.2.val + 1) (by have := p.2.isLt; omega)) := by
    intro a b h
    have h' : sat3Bit N a.1 ⟨0, by omega⟩ (a.2.val + 1) (by have := a.2.isLt; omega)
        = sat3Bit N b.1 ⟨0, by omega⟩ (b.2.val + 1) (by have := b.2.isLt; omega) := h
    have hr1 : (sat3Bit N a.1 ⟨0, by omega⟩ (a.2.val + 1)
        (by have := a.2.isLt; omega)).val % sat3D N = a.2.val + 1 := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + (a.2.val + 1) = a.2.val + 1
      omega
    have hr2 : (sat3Bit N b.1 ⟨0, by omega⟩ (b.2.val + 1)
        (by have := b.2.isLt; omega)).val % sat3D N = b.2.val + 1 := by
      rw [sat3Bit_rem]
      show (0 : ℕ) * (sat3V N + 1) + (b.2.val + 1) = b.2.val + 1
      omega
    have hdiv : a.1.val = b.1.val := by
      rw [← sat3Bit_clause N a.1 ⟨0, by omega⟩ (a.2.val + 1) (by have := a.2.isLt; omega),
        ← sat3Bit_clause N b.1 ⟨0, by omega⟩ (b.2.val + 1) (by have := b.2.isLt; omega)]
      exact congrArg (fun bit : Fin N => bit.val / sat3D N) h'
    have hrem : a.2.val = b.2.val := by
      have h2 : (sat3Bit N a.1 ⟨0, by omega⟩ (a.2.val + 1)
            (by have := a.2.isLt; omega)).val % sat3D N
          = (sat3Bit N b.1 ⟨0, by omega⟩ (b.2.val + 1)
            (by have := b.2.isLt; omega)).val % sat3D N :=
        congrArg (fun bit : Fin N => bit.val % sat3D N) h'
      rw [hr1, hr2] at h2
      omega
    exact Prod.ext (Fin.ext hdiv) (Fin.ext hrem)
  have hnd : ((sat3Sched N).map Prod.fst).Nodup := by
    unfold sat3Sched
    rw [List.map_map]
    exact (pairList_nodup _ _ (List.nodup_finRange _) (List.nodup_finRange _)).map
      (fun a b hab => hinj (by
        have hab' : (fun p : Fin (sat3M N) × Fin (sat3V N - 1) =>
            sat3Bit N p.1 ⟨0, by omega⟩ (p.2.val + 1) (by have := p.2.isLt; omega)) a
            = (fun p : Fin (sat3M N) × Fin (sat3V N - 1) =>
            sat3Bit N p.1 ⟨0, by omega⟩ (p.2.val + 1) (by have := p.2.isLt; omega)) b := hab
        exact hab'))
  -- the pairs are schedule-compatible
  have hpairs : ∀ s ∈ sat3Sched N, ∃ x₁ x₀ : Fin N → Bool,
      (∀ c, x₁ c ≠ x₀ c → c = s.1) ∧ sat3Family N x₁ ≠ sat3Family N x₀ ∧
      (∀ s' ∈ sat3Sched N, s'.1 ≠ s.1 → x₁ s'.1 = s'.2 ∧ x₀ s'.1 = s'.2) := by
    intro s hs
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hs
    obtain ⟨x₁, x₀, h1, h0, hforce, hD⟩ := sat3_selector_pair_zeroD N hv p.1
      ⟨p.2.val + 1, by have := p.2.isLt; omega⟩
    refine ⟨x₁, x₀, hforce, ?_, ?_⟩
    · rw [h1, h0]
      decide
    · intro s' hs' hne'
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hs'
      exact hD q.1 ⟨q.2.val + 1, by have := q.2.isLt; omega⟩
        (by
          show 1 ≤ q.2.val + 1
          omega)
        hne'
  have hchain := liveChain_uniform (sat3Family N) (sat3Sched N) hnd hpairs
  have hsched := budget_schedule (sat3Family N) (sat3Sched N) hchain
  have hres := budget_pos (restrictAll (sat3Family N) (sat3Sched N))
  have hlen := sat3Sched_length N
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.budget_schedule
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.liveChain_uniform
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_pair_zeroD
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_schedule_lb
