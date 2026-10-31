import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCostedPorts

/-!
# N-Frame: recursive port-computation cost — slices inside the budget, and the adjusted decomposition

The recursive accounting, in its provable entirety.  Three facts turn "ports determine the selector cube"
into "port computation lives inside the same budget":

  `recursive_port_accounting` — **PROVED, the covering**: for a simultaneously mediated family there is a
        port-indexed slice family `Φ` with (i) **every slice computable within the same budget** —
        `cbudget (Φ v) ≤ cbudget f` — because the pinned circuit itself computes it; (ii) every slice blind
        to every mediated selector; (iii) `f` covered through the ports: `f x = Φ (ports x) x`.  The
        recursion is exact: a lower bound for `f` follows from a lower bound for any *forced* slice.
  `ports_top_decomposition` — **PROVED, the adjusted sum**: shared-cone port cost plus top-cone cost minus
        their overlap fits in one budget —
        `|portCones| + |topCone| − |portCones ∩ topCone| ≤ cbudget f` — double-counting handled exactly, by
        the union identity.

## Honest scope

The recursion's engine is complete; its open step is unchanged and now maximally exposed: the slices are
budget-bounded and selector-blind, `f` selects among at most `2^{#ports}` of them by the port bits, and a
gain requires exhibiting a mediated family whose slices or ports *cannot* all be cheap — the self-referential
charge isolated by the uniformity file.  For sat3 the candidate ammunition remains the context-dependent
remainder structure against the fixed slice family.  Open, not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The adjusted decomposition -/

/-- **THE ADJUSTED SUM (proved)**: port cost plus top cost minus overlap fits in one budget. -/
theorem ports_top_decomposition {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (S : List (Fin n × ℕ × ℕ)) (hne : S ≠ [])
    (hS : ∀ t ∈ S, MediatedAt c t.1 t.2.1 t.2.2) (v : ℕ → Bool) :
    (portCones c S).card + (coneOf (pinAll v S c) (c.length - 1)).card
      - (portCones c S ∩ coneOf (pinAll v S c) (c.length - 1)).card ≤ cbudget f := by
  have hSlen : ∀ t ∈ S, t.2.2 < c.length := by
    intro t ht
    have h := (hS t ht).2.2.2.1
    omega
  have hpos : 1 ≤ c.length := by
    cases S with
    | nil => exact absurd rfl hne
    | cons t rest =>
      have h := (hS t List.mem_cons_self).2.2.2.1
      omega
  have hU := portCones_subset_range c S hSlen
  have hT : coneOf (pinAll v S c) (c.length - 1) ⊆ Finset.range c.length := by
    intro q hq
    have h1 := cone_le (pinAll v S c) (c.length - 1) q hq
    rw [Finset.mem_range]
    omega
  have hcup := Finset.card_le_card (Finset.union_subset hU hT)
  rw [Finset.card_range] at hcup
  have hid := Finset.card_union_add_card_inter (portCones c S)
    (coneOf (pinAll v S c) (c.length - 1))
  omega

/-! ### The recursive covering -/

/-- **THE RECURSIVE COVERING (proved)**: a port-indexed family of budget-bounded, selector-blind slices
covers `f` through the ports — port computation lives inside the same budget, and a lower bound for `f`
follows from a lower bound for any forced slice. -/
theorem recursive_port_accounting {n : ℕ} (f : (Fin n → Bool) → Bool)
    (c : List (CGate n)) (hcomp : computes c f) (hmin : c.length = cbudget f)
    (S : List (Fin n × ℕ × ℕ)) (hS : ∀ t ∈ S, MediatedAt c t.1 t.2.1 t.2.2) :
    ∃ Φ : (ℕ → Bool) → (Fin n → Bool) → Bool,
      (∀ v : ℕ → Bool, cbudget (Φ v) ≤ cbudget f) ∧
      (∀ (v : ℕ → Bool) (x : Fin n → Bool) (t : Fin n × ℕ × ℕ), t ∈ S → ∀ b : Bool,
        Φ v (Function.update x t.1 b) = Φ v x) ∧
      (∀ x, f x = Φ (fun r => (runFrom x [] c).getD r false) x) := by
  have hSlen : ∀ t ∈ S, t.2.2 < c.length := by
    intro t ht
    have h := (hS t ht).2.2.2.1
    omega
  refine ⟨fun v x => output (pinAll v S c) x, ?_, ?_, ?_⟩
  · -- every slice is computed by the pinned circuit — inside the same budget
    intro v
    show cbudget (fun x => output (pinAll v S c) x) ≤ cbudget f
    have hb : cbudget (fun x => output (pinAll v S c) x) ≤ (pinAll v S c).length :=
      Nat.sInf_le ⟨pinAll v S c, fun _ => rfl, rfl⟩
    rw [pinAll_length v S c hSlen] at hb
    omega
  · -- every slice is blind to every mediated selector
    intro v x t ht b
    have hmed := hS t ht
    have hdlen : (pinAll v S c).length = c.length := pinAll_length v S c hSlen
    show output (pinAll v S c) (Function.update x t.1 b) = output (pinAll v S c) x
    show (runFrom (Function.update x t.1 b) [] (pinAll v S c)).getD
        ((pinAll v S c).length - 1) false
      = (runFrom x [] (pinAll v S c)).getD ((pinAll v S c).length - 1) false
    apply cone_val_agree (pinAll v S c) ((pinAll v S c).length - 1)
      (Function.update x t.1 b) x ?_ _ (cone_self _ _)
    intro q hq i' hgate
    have hii : i' ≠ t.1 := by
      intro hii'
      rw [hii'] at hgate
      obtain ⟨hgc, hqpins⟩ := pinAll_getD_var v S c q t.1 hSlen hgate
      have hqp : q = t.2.1 := hmed.2.1 q hgc
      have hrint := hmed.2.2.2.1
      have hplr : t.2.1 < t.2.2 := children_lt c t.2.2 t.2.1 hmed.2.2.1
      rcases cone_parent _ _ q hq with h' | ⟨r', hr'cone, hr'child⟩
      · rw [hdlen] at h'
        omega
      · by_cases hr'pin : ∃ t' ∈ S, r' = t'.2.2
        · obtain ⟨t', ht', rfl⟩ := hr'pin
          rw [pinAll_children_pinned v S c t' ht' hSlen] at hr'child
          exact absurd hr'child (Finset.notMem_empty q)
        · push_neg at hr'pin
          rw [pinAll_children v S c r' hSlen (fun t' ht' => hr'pin t' ht')] at hr'child
          rw [hqp] at hr'child
          have hr'r := hmed.2.2.2.2 r' hr'child
          exact (hr'pin t ht) hr'r
    rw [Function.update_of_ne hii]
  · -- reconstruction through the ports
    intro x
    have hrun := pinAll_run_eq x (runFrom x [] c) S c hSlen rfl (fun t _ => rfl)
      (fun r => (runFrom x [] c).getD r false) (fun t _ => rfl)
    show f x = (runFrom x [] (pinAll (fun r => (runFrom x [] c).getD r false) S c)).getD
        ((pinAll (fun r => (runFrom x [] c).getD r false) S c).length - 1) false
    rw [hrun, pinAll_length _ S c hSlen]
    exact (hcomp x).symm

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.ports_top_decomposition
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.recursive_port_accounting
