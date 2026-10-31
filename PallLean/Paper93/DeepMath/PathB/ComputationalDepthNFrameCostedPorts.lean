import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameContextUniformity

/-!
# N-Frame: costed ports — the terminal map of the mediation campaign

The arc's terminal file: what is proved, packaged, and the exact form of what a further gain must charge.

**Proved below this file** (the campaign, all clean): the selector trichotomy (duplication / reuse /
mediation), the fan-out kill engine (`cbudget_fanout_kill`), the joint top map with port-locality
(`joint_top_map_full`), the K-port capacity count with its proved-tight ceiling
(`selector_count_le_two_mul_ports`, `xor_mediates_pair`), and the determination identity
(`joint_cube_factor`).  **Proved here**:

  `sat3_selector_terminal` — **the terminal map**: every circuit computing SAT, at every slot-2 selector,
        lands in exactly the three-way split — duplication, reuse, or a full `MediatedAt` configuration
        carrying the determination identity.
  `portCones` / `ports_cost_le_cbudget` — **the no-free-port base**: the mediator ports' *shared-cone* cost
        — the union of their cones, overlap counted once — sits inside the same budget:
        `(portCones c S).card ≤ cbudget f` for minimal `c`.

## Honest scope — the terminal reading

Branches one and two pay through the kill engine.  Branch three now carries three proved facts at once: the
selectors' influence passes through the ports (determination), the ports number at least half the selectors
(capacity), and the ports' shared cones are paid for inside the budget (this file).  What no theorem yet does
— and what any further gain must do — is charge the ports' *computation* beyond their footprint: the cones
may be shallow, shared, or equal to the whole circuit, and bounding what cheap cones can feed into one
selector-blind top is the self-referential accounting isolated by the uniformity file.  The route below this
point is theorem-closed; the route above it is the mountain, open and not claimed.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The shared-cone cost of a port family -/

/-- The shared-cone footprint of the mediator ports — overlap counted once. -/
def portCones {n : ℕ} (c : List (CGate n)) : List (Fin n × ℕ × ℕ) → Finset ℕ
  | [] => ∅
  | t :: rest => coneOf c t.2.2 ∪ portCones c rest

theorem portCones_subset_range {n : ℕ} (c : List (CGate n)) :
    ∀ S : List (Fin n × ℕ × ℕ), (∀ t ∈ S, t.2.2 < c.length) →
      portCones c S ⊆ Finset.range c.length := by
  intro S
  induction S with
  | nil =>
    intro _ q hq
    exact absurd hq (Finset.notMem_empty q)
  | cons t rest ih =>
    intro hS q hq
    rcases Finset.mem_union.mp hq with h | h
    · rw [Finset.mem_range]
      have h1 := cone_le c t.2.2 q h
      have h2 := hS t List.mem_cons_self
      omega
    · exact ih (fun t' ht' => hS t' (List.mem_cons_of_mem t ht')) h

/-- **THE NO-FREE-PORT BASE (proved)**: the mediator ports' shared-cone cost sits inside the budget —
overlap counted once, double-counting impossible by construction. -/
theorem ports_cost_le_cbudget {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (S : List (Fin n × ℕ × ℕ)) (hS : ∀ t ∈ S, MediatedAt c t.1 t.2.1 t.2.2) :
    (portCones c S).card ≤ cbudget f := by
  have hlen : ∀ t ∈ S, t.2.2 < c.length := by
    intro t ht
    have h := (hS t ht).2.2.2.1
    omega
  have h := Finset.card_le_card (portCones_subset_range c S hlen)
  rw [Finset.card_range] at h
  omega

/-! ### The terminal map -/

/-- **THE TERMINAL MAP (proved)**: every circuit computing SAT, at every slot-2 selector — duplication,
reuse, or the full mediation configuration carrying the determination identity. -/
theorem sat3_selector_terminal (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N))
    (c : List (CGate N)) (hcomp : computes c (sat3Family N)) :
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ c.getD p₁ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      c.getD p₂ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j)) ∨
    (∃ p r₁ r₂, r₁ ≠ r₂ ∧ c.getD p (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      p ∈ childrenOf c r₁ ∧ p ∈ childrenOf c r₂) ∨
    (∃ p r, MediatedAt c (sat3S2Sel N cIdx j) p r) := by
  by_cases hmed : ∃ p r, MediatedAt c (sat3S2Sel N cIdx j) p r
  · exact Or.inr (Or.inr hmed)
  · rcases unmediated_dup_or_reuse N hv hm2 cIdx j c hcomp hmed with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.ports_cost_le_cbudget
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_terminal
