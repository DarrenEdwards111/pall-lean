import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPrefixTransfer

/-!
# Brick G2b of the ∀m finish: the chain-bottleneck kill

A gadget whose three variables all funnel through one wire on reconvergence-free
chains is contradictory: the wire's function restricts to `±allEq3`, but the
prefix unwinding at that wire has leaf count 1 at the triple, so the restriction
would split:

* **`chain_bottleneck_kill` (proved)** — the mediation at `j` (swap +
  chain-soleness blindness) gives `allEq3 = U' ∘ (wire j)` with `U'` unary and
  nonconstant; the prefix `c.take (j+1)` computes `wire j`; its unwinding has
  count 1 at the triple (`extractG_cnt_spec` with the reconvergence-avoidance
  built from the three G2a transfer lemmas); `gtree_split_cnt` refutes.

Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

open PallLean.Paper93.DeepMath.PathB.CbudgetConeBound
open PallLean.Paper93.DeepMath.PathB.SATFamilyCircuitFloor
open PallLean.Paper93.DeepMath.PathB.SATSlackSeed

/-- **THE CHAIN-BOTTLENECK KILL (proved).** -/
theorem chain_bottleneck_kill (m : ℕ) (c : List (CGate (3 * m)))
    (hcomp : computes c (AEm m)) (hs : 0 < c.length)
    (g : ℕ) (hg : g < m)
    (ha : 3 * g < 3 * m) (hb : 3 * g + 1 < 3 * m) (hc2 : 3 * g + 2 < 3 * m)
    (j : ℕ) (hjc : j ∈ cone c) (hjroot : j ≠ c.length - 1)
    (q₀ q₁ q₂ : ℕ) (hq₀c : q₀ ∈ cone c) (hq₁c : q₁ ∈ cone c) (hq₂c : q₂ ∈ cone c)
    (hg₀ : c.getD q₀ (.cst false) = CGate.var ⟨3 * g, ha⟩)
    (hg₁ : c.getD q₁ (.cst false) = CGate.var ⟨3 * g + 1, hb⟩)
    (hg₂ : c.getD q₂ (.cst false) = CGate.var ⟨3 * g + 2, hc2⟩)
    (hu₀ : ∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var ⟨3 * g, ha⟩ → q' = q₀)
    (hu₁ : ∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var ⟨3 * g + 1, hb⟩ → q' = q₁)
    (hu₂ : ∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var ⟨3 * g + 2, hc2⟩ → q' = q₂)
    (hch₀ : Chain c q₀ j) (hch₁ : Chain c q₁ j) (hch₂ : Chain c q₂ j) : False := by
  classical
  have hjlt : j < c.length := (mem_cone.mp hjc).1
  have hsole₀ := chain_sole_var₀ c hs hq₀c hch₀ hu₀
  have hsole₁ := chain_sole_var₀ c hs hq₁c hch₁ hu₁
  have hsole₂ := chain_sole_var₀ c hs hq₂c hch₂ hu₂
  -- the prefix computes the wire
  have hlen' : (c.take (j + 1)).length = j + 1 := by
    rw [List.length_take]
    omega
  have hroot' : (c.take (j + 1)).length - 1 = j := by omega
  have hcomp' : computes (c.take (j + 1)) (fun x => wire c x j) := fun x =>
    wire_take_output_g c hjlt x
  have hs' : 0 < (c.take (j + 1)).length := by omega
  -- gates, cone membership and uniqueness inside the prefix
  have hqle : ∀ {q : ℕ}, Chain c q j → q < j + 1 := by
    intro q hch
    have := chain_le hch
    omega
  have hcone' : ∀ {q : ℕ}, Chain c q j → q ∈ cone (c.take (j + 1)) := by
    intro q hch
    refine mem_cone.mpr ⟨by rw [hlen']; exact hqle hch, ?_⟩
    exact reach_inCone_take c hjlt (chain_reach hch)
  have hmemc : ∀ {q' : ℕ}, q' ∈ cone (c.take (j + 1)) → q' ∈ cone c := by
    intro q' hq'
    have hr := inCone_take_reach_g hjlt q' (mem_cone.mp hq').2
    have := reach_le hr
    exact mem_cone.mpr ⟨by omega, reach_inCone (mem_cone.mp hjc).2 hr⟩
  have hgd' : ∀ {q : ℕ}, Chain c q j →
      (c.take (j + 1)).getD q (.cst false) = c.getD q (.cst false) := by
    intro q hch
    exact getD_take_eq_g (hqle hch)
  have huniq' : ∀ (i : Fin (3 * m)) (q : ℕ),
      (∀ q' ∈ cone c, c.getD q' (.cst false) = CGate.var i → q' = q) →
      ∀ q' ∈ cone (c.take (j + 1)),
        (c.take (j + 1)).getD q' (.cst false) = CGate.var i → q' = q := by
    intro i q hu q' hq' hg'
    have hq'le : q' < j + 1 := by
      have := (mem_cone.mp hq').1
      rw [hlen'] at this
      exact this
    rw [getD_take_eq_g hq'le] at hg'
    exact hu q' (hmemc hq') hg'
  -- reconvergence avoidance inside the prefix
  have hRq : ∀ {q : ℕ}, Chain c q j → q ∈ cone c →
      ∀ u' ∈ reconvR (c.take (j + 1)), ¬ Reach (c.take (j + 1)) u' q := by
    intro q hch hqc u' hu'R hr'
    have hu'Rc : u' ∈ reconvR c := reconvR_take_subset c hjc hjroot hu'R
    have hu'facts := Finset.mem_erase.mp (Finset.mem_filter.mp hu'R).1
    have hu'lt : u' < j + 1 := by
      have := (mem_cone.mp hu'facts.2).1
      rw [hlen'] at this
      exact this
    have hu'j : u' ≠ j := by
      have := hu'facts.1
      rw [hroot'] at this
      exact this
    have hu'ltj : u' < j := by omega
    have hu'conec : u' ∈ cone c :=
      (Finset.mem_erase.mp (Finset.mem_filter.mp hu'Rc).1).2
    have hrc : Reach c u' q := reach_of_take c hjlt (by omega) hr'
    rcases reach_chain_dichotomy c hs c.length q j (by omega) hqc hch
        u' hu'conec hrc with hchu | hru
    · exact chain_extend_not_reconv c hs c.length q u' j (by omega) hqc
        hchu hch hu'ltj hu'Rc
    · have := reach_le hru
      omega
  -- the root of the prefix reaches each var gate
  have hroot'' : (c.take (j + 1)).length - 1 ∈ cone (c.take (j + 1)) :=
    mem_cone.mpr ⟨by omega, InCone.root⟩
  have hreachroot : ∀ {q : ℕ}, Chain c q j →
      Reach (c.take (j + 1)) ((c.take (j + 1)).length - 1) q := by
    intro q hch
    rw [hroot']
    exact reach_take_of_reach c hjlt (chain_reach hch)
  -- the counts are 1 at the triple
  have hcnt₀ : (extractG (c.take (j + 1)) (c.take (j + 1)).length
      ((c.take (j + 1)).length - 1)).cnt ⟨3 * g, ha⟩ = 1 :=
    (extractG_cnt_spec (c.take (j + 1)) hs' ⟨3 * g, ha⟩ q₀ (hcone' hch₀)
      (by rw [hgd' hch₀]; exact hg₀) (huniq' ⟨3 * g, ha⟩ q₀ hu₀) (hRq hch₀ hq₀c)
      (c.take (j + 1)).length ((c.take (j + 1)).length - 1) (by omega)
      hroot'').1 (hreachroot hch₀)
  have hcnt₁ : (extractG (c.take (j + 1)) (c.take (j + 1)).length
      ((c.take (j + 1)).length - 1)).cnt ⟨3 * g + 1, hb⟩ = 1 :=
    (extractG_cnt_spec (c.take (j + 1)) hs' ⟨3 * g + 1, hb⟩ q₁ (hcone' hch₁)
      (by rw [hgd' hch₁]; exact hg₁) (huniq' ⟨3 * g + 1, hb⟩ q₁ hu₁) (hRq hch₁ hq₁c)
      (c.take (j + 1)).length ((c.take (j + 1)).length - 1) (by omega)
      hroot'').1 (hreachroot hch₁)
  have hcnt₂ : (extractG (c.take (j + 1)) (c.take (j + 1)).length
      ((c.take (j + 1)).length - 1)).cnt ⟨3 * g + 2, hc2⟩ = 1 :=
    (extractG_cnt_spec (c.take (j + 1)) hs' ⟨3 * g + 2, hc2⟩ q₂ (hcone' hch₂)
      (by rw [hgd' hch₂]; exact hg₂) (huniq' ⟨3 * g + 2, hc2⟩ q₂ hu₂) (hRq hch₂ hq₂c)
      (c.take (j + 1)).length ((c.take (j + 1)).length - 1) (by omega)
      hroot'').1 (hreachroot hch₂)
  -- the split disjunction at the prefix root
  have hsp := gtree_split_cnt (extractG (c.take (j + 1)) (c.take (j + 1)).length
      ((c.take (j + 1)).length - 1))
    ⟨3 * g, ha⟩ ⟨3 * g + 1, hb⟩ ⟨3 * g + 2, hc2⟩
    (by intro he; have h' : 3 * g = 3 * g + 1 := congrArg Fin.val he; omega)
    (by intro he; have h' : 3 * g = 3 * g + 2 := congrArg Fin.val he; omega)
    (by intro he; have h' : 3 * g + 1 = 3 * g + 2 := congrArg Fin.val he; omega)
    (fun _ => true) hcnt₀ hcnt₁ hcnt₂
  have hroot_eval : (extractG (c.take (j + 1)) (c.take (j + 1)).length
      ((c.take (j + 1)).length - 1)).eval = fun x => wire c x j :=
    extractG_root (c.take (j + 1)) (fun x => wire c x j) hcomp' hs'
  -- the mediation at j: allEq3 = U' ∘ (wire j)
  have hmed : ∀ a b cv : Bool,
      allEq3 a b cv
        = output (swapG c j (wire c (Function.update (Function.update
            (Function.update (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a)
            ⟨3 * g + 1, hb⟩ b) ⟨3 * g + 2, hc2⟩ cv) j))
          (fun _ : Fin (3 * m) => true) := by
    intro a b cv
    have hg' : AEm m (Function.update (Function.update (Function.update
        (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
        ⟨3 * g + 2, hc2⟩ cv) = allEq3 a b cv :=
      congrFun (congrFun (congrFun (AEm_gadget_g m g hg ha hb hc2) a) b) cv
    rw [← hg', ← hcomp (Function.update (Function.update (Function.update
        (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
        ⟨3 * g + 2, hc2⟩ cv),
      ← output_swapG c hjlt (Function.update (Function.update (Function.update
        (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
        ⟨3 * g + 2, hc2⟩ cv)]
    exact eval_agree_of_blind
      (output (swapG c j (wire c (Function.update (Function.update
          (Function.update (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a)
          ⟨3 * g + 1, hb⟩ b) ⟨3 * g + 2, hc2⟩ cv) j)))
      (fun i' => i' ≠ (⟨3 * g, ha⟩ : Fin (3 * m))
        ∧ i' ≠ (⟨3 * g + 1, hb⟩ : Fin (3 * m))
        ∧ i' ≠ (⟨3 * g + 2, hc2⟩ : Fin (3 * m)))
      (fun i' hi' z b' => by
        rw [not_and_or, not_and_or, not_not, not_not, not_not] at hi'
        rcases hi' with hi' | hi' | hi'
        · subst hi'
          exact swapG_blind_clean c hs hjlt _ _ hsole₀ z b'
        · subst hi'
          exact swapG_blind_clean c hs hjlt _ _ hsole₁ z b'
        · subst hi'
          exact swapG_blind_clean c hs hjlt _ _ hsole₂ z b')
      _ _ (fun i' hi' => by
        obtain ⟨h1', h2', h3'⟩ := hi'
        rw [Function.update_of_ne h3' cv (Function.update (Function.update
            (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b),
          Function.update_of_ne h2' b (Function.update
            (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a),
          Function.update_of_ne h1' a (fun _ : Fin (3 * m) => true)])
  -- the unary trichotomy for the mediator
  have hU : ∀ U : Bool → Bool,
      (∀ y, U y = U false) ∨ (∀ y, U y = y) ∨ (∀ y, U y = !y) := by decide
  rcases hU (fun w => output (swapG c j w) (fun _ : Fin (3 * m) => true)) with
    hcst | hid | hnot
  · -- constant mediator: allEq3 would be constant
    have e1 : output (swapG c j (wire c (Function.update (Function.update
        (Function.update (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ true)
        ⟨3 * g + 1, hb⟩ true) ⟨3 * g + 2, hc2⟩ true) j))
        (fun _ : Fin (3 * m) => true)
        = output (swapG c j false) (fun _ : Fin (3 * m) => true) := hcst _
    have e2 : output (swapG c j (wire c (Function.update (Function.update
        (Function.update (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ false)
        ⟨3 * g + 1, hb⟩ true) ⟨3 * g + 2, hc2⟩ true) j))
        (fun _ : Fin (3 * m) => true)
        = output (swapG c j false) (fun _ : Fin (3 * m) => true) := hcst _
    have h1 : allEq3 true true true
        = output (swapG c j false) (fun _ : Fin (3 * m) => true) :=
      (hmed true true true).trans e1
    have h2 : allEq3 false true true
        = output (swapG c j false) (fun _ : Fin (3 * m) => true) :=
      (hmed false true true).trans e2
    have hcontra : allEq3 true true true = allEq3 false true true :=
      h1.trans h2.symm
    exact absurd hcontra (by decide)
  · -- identity mediator: the wire restriction IS allEq3, which cannot split
    have hF : (fun a b cv => (extractG (c.take (j + 1)) (c.take (j + 1)).length
        ((c.take (j + 1)).length - 1)).eval
          (Function.update (Function.update (Function.update
            (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
            ⟨3 * g + 2, hc2⟩ cv)) = allEq3 := by
      funext a b cv
      have h1 : (extractG (c.take (j + 1)) (c.take (j + 1)).length
          ((c.take (j + 1)).length - 1)).eval
            (Function.update (Function.update (Function.update
              (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
              ⟨3 * g + 2, hc2⟩ cv)
          = wire c (Function.update (Function.update (Function.update
              (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
              ⟨3 * g + 2, hc2⟩ cv) j := congrFun hroot_eval _
      have h2 : output (swapG c j (wire c (Function.update (Function.update
          (Function.update (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a)
          ⟨3 * g + 1, hb⟩ b) ⟨3 * g + 2, hc2⟩ cv) j))
          (fun _ : Fin (3 * m) => true)
          = wire c (Function.update (Function.update (Function.update
              (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
              ⟨3 * g + 2, hc2⟩ cv) j := hid _
      exact h1.trans ((hmed a b cv).trans h2).symm
    rw [hF] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a h
    · exact allEq3_no_split_b h
    · exact allEq3_no_split_c h
  · -- negation mediator: the wire restriction is ¬allEq3, splits transfer back
    have hF' : (fun a b cv => (extractG (c.take (j + 1)) (c.take (j + 1)).length
        ((c.take (j + 1)).length - 1)).eval
          (Function.update (Function.update (Function.update
            (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
            ⟨3 * g + 2, hc2⟩ cv))
        = (fun a b cv => !(allEq3 a b cv)) := by
      funext a b cv
      have h1 : (extractG (c.take (j + 1)) (c.take (j + 1)).length
          ((c.take (j + 1)).length - 1)).eval
            (Function.update (Function.update (Function.update
              (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
              ⟨3 * g + 2, hc2⟩ cv)
          = wire c (Function.update (Function.update (Function.update
              (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
              ⟨3 * g + 2, hc2⟩ cv) j := congrFun hroot_eval _
      have h2 : output (swapG c j (wire c (Function.update (Function.update
          (Function.update (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a)
          ⟨3 * g + 1, hb⟩ b) ⟨3 * g + 2, hc2⟩ cv) j))
          (fun _ : Fin (3 * m) => true)
          = !(wire c (Function.update (Function.update (Function.update
              (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
              ⟨3 * g + 2, hc2⟩ cv) j) := hnot _
      have h4 : allEq3 a b cv
          = !(wire c (Function.update (Function.update (Function.update
              (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
              ⟨3 * g + 2, hc2⟩ cv) j) := (hmed a b cv).trans h2
      have h3 : wire c (Function.update (Function.update (Function.update
          (fun _ : Fin (3 * m) => true) ⟨3 * g, ha⟩ a) ⟨3 * g + 1, hb⟩ b)
          ⟨3 * g + 2, hc2⟩ cv) j = !(allEq3 a b cv) := by
        rw [h4, Bool.not_not]
      exact h1.trans h3
    rw [hF'] at hsp
    rcases hsp with h | h | h
    · exact allEq3_no_split_a (split1_of_not h)
    · exact allEq3_no_split_b (split2_of_not h)
    · exact allEq3_no_split_c (split3_of_not h)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.chain_bottleneck_kill
