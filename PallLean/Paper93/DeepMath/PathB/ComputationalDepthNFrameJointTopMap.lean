import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATTopSideAccounting

/-!
# N-Frame: the joint top map — simultaneous mediation composes through position

The gap named by the top-side file, closed: a circuit whose mediators sit at fixed positions induces one
**joint** top map over all re-entry ports — not a family of remainders reading each other raw.

  `pinAll` / `run_pin_eq` / `pinAll_run_eq` — the multi-pin calculus: pinning any set of wires to their own
        values preserves the *entire* run, port by port.
  `joint_top_map` — **PROVED, the theorem**: if every selector in `S` is `MediatedAt` in `c`, then there is a
        single `H` with

        `f x = H (fun r => wire r's value at x) x`   and
        `H v` insensitive to **every** mediated selector simultaneously.

        Proof: pin all mediator wires at once; each selector's unique reader is pinned, so its variable gate
        is readerless in the pinned circuit and falls out of the output cone — jointly.  No distinctness
        hypotheses are needed.

## Honest scope

The joint form now exists, extracted from position exactly as required.  What remains — the mountain face in
final form — is **K-port compression**: the ports of `H` are the mediator wires, capacity two selectors per
wire (`mediator_capacity_two`), so `K` mediated selectors compress `f`'s selector-cube restrictions through
`≥ K/2` port bits and an off-`S`-context; against that stands SAT's context-dependent remainder structure
(`sat3_reentry_not_rigid`, the subfunction counts).  Making that count is open and not claimed.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The multi-pin calculus -/

theorem run_congr_point {n : ℕ} (c₁ : List (CGate n)) (g g' : CGate n)
    (c₂ : List (CGate n)) (x : Fin n → Bool)
    (heq : evalGate x (runFrom x [] c₁) g = evalGate x (runFrom x [] c₁) g') :
    runFrom x [] (c₁ ++ g' :: c₂) = runFrom x [] (c₁ ++ g :: c₂) := by
  rw [show c₁ ++ g' :: c₂ = (c₁ ++ [g']) ++ c₂ by simp,
    show c₁ ++ g :: c₂ = (c₁ ++ [g]) ++ c₂ by simp,
    runFrom_append x [] (c₁ ++ [g']) c₂, runFrom_append x [] c₁ [g'],
    runFrom_append x [] (c₁ ++ [g]) c₂, runFrom_append x [] c₁ [g]]
  show runFrom x (runFrom x [] c₁ ++ [evalGate x (runFrom x [] c₁) g']) c₂
      = runFrom x (runFrom x [] c₁ ++ [evalGate x (runFrom x [] c₁) g]) c₂
  rw [heq]

/-- Pinning a wire to its own value preserves the whole run. -/
theorem run_pin_eq {n : ℕ} (d : List (CGate n)) (r : ℕ) (hr : r < d.length)
    (x : Fin n → Bool) :
    runFrom x [] (d.take r ++ CGate.cst ((runFrom x [] d).getD r false) :: d.drop (r + 1))
      = runFrom x [] d := by
  conv_rhs => rw [circuit_split_at d r hr]
  exact run_congr_point (d.take r) (d.getD r (CGate.cst false))
    (CGate.cst ((runFrom x [] d).getD r false)) (d.drop (r + 1)) x
    (output_getD_at x d r hr).symm

/-- Pin every listed mediator wire to the given port values. -/
def pinAll {n : ℕ} (v : ℕ → Bool) : List (Fin n × ℕ × ℕ) → List (CGate n) → List (CGate n)
  | [], d => d
  | t :: rest, d =>
      pinAll v rest (d.take t.2.2 ++ CGate.cst (v t.2.2) :: d.drop (t.2.2 + 1))

theorem pinAll_length {n : ℕ} (v : ℕ → Bool) :
    ∀ (S : List (Fin n × ℕ × ℕ)) (d : List (CGate n)),
      (∀ t ∈ S, t.2.2 < d.length) → (pinAll v S d).length = d.length := by
  intro S
  induction S with
  | nil => intro d _; rfl
  | cons t rest ih =>
    intro d hS
    show (pinAll v rest (d.take t.2.2 ++ CGate.cst (v t.2.2) :: d.drop (t.2.2 + 1))).length
        = d.length
    have hsl := splice_length d t.2.2 (CGate.cst (v t.2.2)) (hS t List.mem_cons_self)
    rw [ih _ (by
      intro t' ht'
      rw [hsl]
      exact hS t' (List.mem_cons_of_mem t ht')), hsl]

/-- Pinning to own values preserves the run — iterated. -/
theorem pinAll_run_eq {n : ℕ} (x : Fin n → Bool) (W : List Bool) :
    ∀ (S : List (Fin n × ℕ × ℕ)) (d : List (CGate n)),
      (∀ t ∈ S, t.2.2 < d.length) → runFrom x [] d = W →
      (∀ t ∈ S, (fun r => W.getD r false) t.2.2 = W.getD t.2.2 false) →
      ∀ v : ℕ → Bool, (∀ t ∈ S, v t.2.2 = W.getD t.2.2 false) →
      runFrom x [] (pinAll v S d) = W := by
  intro S
  induction S with
  | nil => intro d _ hW _ v _; exact hW
  | cons t rest ih =>
    intro d hS hW _ v hv
    show runFrom x []
        (pinAll v rest (d.take t.2.2 ++ CGate.cst (v t.2.2) :: d.drop (t.2.2 + 1))) = W
    have hrd : t.2.2 < d.length := hS t List.mem_cons_self
    have hval : v t.2.2 = (runFrom x [] d).getD t.2.2 false := by
      rw [hv t List.mem_cons_self, hW]
    have hpin : runFrom x []
        (d.take t.2.2 ++ CGate.cst (v t.2.2) :: d.drop (t.2.2 + 1)) = W := by
      rw [hval, run_pin_eq d t.2.2 hrd x]
      exact hW
    have hsl := splice_length d t.2.2 (CGate.cst (v t.2.2)) hrd
    exact ih _ (by
        intro t' ht'
        rw [hsl]
        exact hS t' (List.mem_cons_of_mem t ht'))
      hpin (fun t' _ => rfl) v (fun t' ht' => hv t' (List.mem_cons_of_mem t ht'))

/-! ### Gate lookups through the pinning -/

theorem pinAll_getD_var {n : ℕ} (v : ℕ → Bool) :
    ∀ (S : List (Fin n × ℕ × ℕ)) (d : List (CGate n)) (q : ℕ) (i : Fin n),
      (∀ t ∈ S, t.2.2 < d.length) →
      (pinAll v S d).getD q (CGate.cst false) = CGate.var i →
      d.getD q (CGate.cst false) = CGate.var i ∧ ∀ t ∈ S, q ≠ t.2.2 := by
  intro S
  induction S with
  | nil =>
    intro d q i _ h
    exact ⟨h, fun t ht => absurd ht List.not_mem_nil⟩
  | cons t rest ih =>
    intro d q i hS h
    have hrd : t.2.2 < d.length := hS t List.mem_cons_self
    have hsl := splice_length d t.2.2 (CGate.cst (v t.2.2)) hrd
    obtain ⟨h1, h2⟩ := ih _ q i (by
      intro t' ht'
      rw [hsl]
      exact hS t' (List.mem_cons_of_mem t ht')) h
    have hqt : q ≠ t.2.2 := by
      intro hq
      rw [hq, splice_getD_self d t.2.2 (CGate.cst (v t.2.2)) hrd] at h1
      simp at h1
    rw [splice_getD d t.2.2 (CGate.cst (v t.2.2)) hrd q hqt] at h1
    refine ⟨h1, ?_⟩
    intro t' ht'
    rcases List.mem_cons.mp ht' with rfl | ht''
    · exact hqt
    · exact h2 t' ht''

theorem pinAll_children {n : ℕ} (v : ℕ → Bool) :
    ∀ (S : List (Fin n × ℕ × ℕ)) (d : List (CGate n)) (q : ℕ),
      (∀ t ∈ S, t.2.2 < d.length) → (∀ t ∈ S, q ≠ t.2.2) →
      childrenOf (pinAll v S d) q = childrenOf d q := by
  intro S
  induction S with
  | nil => intro d q _ _; rfl
  | cons t rest ih =>
    intro d q hS hq
    have hrd : t.2.2 < d.length := hS t List.mem_cons_self
    have hsl := splice_length d t.2.2 (CGate.cst (v t.2.2)) hrd
    show childrenOf (pinAll v rest
        (d.take t.2.2 ++ CGate.cst (v t.2.2) :: d.drop (t.2.2 + 1))) q = childrenOf d q
    rw [ih _ q (by
        intro t' ht'
        rw [hsl]
        exact hS t' (List.mem_cons_of_mem t ht'))
      (fun t' ht' => hq t' (List.mem_cons_of_mem t ht'))]
    unfold childrenOf
    rw [splice_getD d t.2.2 (CGate.cst (v t.2.2)) hrd q (hq t List.mem_cons_self)]

theorem pinAll_children_pinned {n : ℕ} (v : ℕ → Bool) :
    ∀ (S : List (Fin n × ℕ × ℕ)) (d : List (CGate n)) (t₀ : Fin n × ℕ × ℕ),
      t₀ ∈ S → (∀ t ∈ S, t.2.2 < d.length) →
      childrenOf (pinAll v S d) t₀.2.2 = ∅ := by
  intro S
  induction S with
  | nil => intro d t₀ h _; exact absurd h List.not_mem_nil
  | cons t rest ih =>
    intro d t₀ ht₀ hS
    have hrd : t.2.2 < d.length := hS t List.mem_cons_self
    have hsl := splice_length d t.2.2 (CGate.cst (v t.2.2)) hrd
    have hrest : ∀ t' ∈ rest,
        t'.2.2 < (d.take t.2.2 ++ CGate.cst (v t.2.2) :: d.drop (t.2.2 + 1)).length := by
      intro t' ht'
      rw [hsl]
      exact hS t' (List.mem_cons_of_mem t ht')
    rcases List.mem_cons.mp ht₀ with rfl | ht₀'
    · by_cases hq : ∀ t' ∈ rest, t₀.2.2 ≠ t'.2.2
      · show childrenOf (pinAll v rest _) t₀.2.2 = ∅
        rw [pinAll_children v rest _ t₀.2.2 hrest hq]
        exact childrenOf_eq_cst _ t₀.2.2 (v t₀.2.2)
          (splice_getD_self d t₀.2.2 (CGate.cst (v t₀.2.2)) hrd)
      · push_neg at hq
        obtain ⟨t', ht', hqt⟩ := hq
        have h := ih _ t' ht' hrest
        rw [← hqt] at h
        exact h
    · exact ih _ t₀ ht₀' hrest

/-! ### The joint top map -/

/-- **THE JOINT TOP MAP (proved)**: simultaneously mediated selectors compose through position — one `H`
serves every re-entry port, insensitive to all mediated selectors at once. -/
theorem joint_top_map {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (S : List (Fin n × ℕ × ℕ))
    (hS : ∀ t ∈ S, MediatedAt c t.1 t.2.1 t.2.2) :
    ∃ H : (ℕ → Bool) → (Fin n → Bool) → Bool,
      (∀ x, f x = H (fun r => (runFrom x [] c).getD r false) x) ∧
      (∀ (v : ℕ → Bool) (x : Fin n → Bool) (t : Fin n × ℕ × ℕ), t ∈ S → ∀ b : Bool,
        H v (Function.update x t.1 b) = H v x) := by
  have hSlen : ∀ t ∈ S, t.2.2 < c.length := by
    intro t ht
    have h := (hS t ht).2.2.2.1
    omega
  refine ⟨fun v x => output (pinAll v S c) x, ?_, ?_⟩
  · intro x
    show f x = output (pinAll (fun r => (runFrom x [] c).getD r false) S c) x
    have hrun := pinAll_run_eq x (runFrom x [] c) S c hSlen rfl (fun t _ => rfl)
      (fun r => (runFrom x [] c).getD r false) (fun t _ => rfl)
    show f x = (runFrom x [] (pinAll (fun r => (runFrom x [] c).getD r false) S c)).getD
        ((pinAll (fun r => (runFrom x [] c).getD r false) S c).length - 1) false
    rw [hrun, pinAll_length _ S c hSlen]
    exact (hcomp x).symm
  · intro v x t ht b
    have hmed := hS t ht
    have hplr : t.2.1 < t.2.2 := children_lt c t.2.2 t.2.1 hmed.2.2.1
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
      -- the variable gate is readerless in the pinned circuit
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

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.run_pin_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.pinAll_run_eq
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.joint_top_map
