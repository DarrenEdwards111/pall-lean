import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFramePositionalMediation

/-!
# N-Frame: simultaneous mediation — the object, the capacity baseline, and the conversion

The mountain face made into definite objects.  `MediatedAt` packages the trichotomy's third branch as a
configuration (unique variable gate, unique reader); the results here calibrate exactly what aggregate
accounting can and cannot do:

  `MediatedAt` / `MediatedAt.factor` — the simultaneous-mediation object: each mediated variable carries the
        positional 1-bit factorization.
  `mediator_capacity_two` — **PROVED, the aggregate baseline**: one wire is the mediator configuration for at
        most **two** variables (fan-in), so `K` simultaneously mediated selectors need `≥ K/2` distinct
        mediator wires.  By the xor no-go this is *tight locally* — pairs share freely — so the baseline caps
        at edge-counting strength, and any aggregate bound beyond it must use position and cone-locality.
  `and_topDecomp` — **PROVED, calibration**: AND is top-decomposable at every variable — the trichotomy
        short-circuits before mediation, no false pressure.  (Parity's calibration is `xor_mediates_pair`:
        genuine xor mediators exist, and no accounting may falsely exclude them.)
  `unmediated_dup_or_reuse` — **PROVED, the conversion**: an unmediated selector duplicates its gate or its
        wire is read twice — the interface that turns any future "many selectors unmediated" theorem into
        extra kills via `cbudget_fanout_kill`.

## Honest scope

The face itself — *simultaneous positional one-bit mediation cannot service `Ω(m·v)` SAT selectors cheaply* —
is **open** and is not claimed.  What stands: its refutation cannot be local (xor no-go), cannot be counting
(capacity baseline = edge strength), and must charge many bottom-cones against the wire budget at once.  Any
proof of the face converts, through this file and the fan-out engine, into kills beyond the `≈ 2N`
connectivity record — the first strictly-beyond-connectivity number.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The simultaneous-mediation object -/

/-- The trichotomy's third branch as a configuration: unique variable gate `p`, unique reader `r`. -/
def MediatedAt {n : ℕ} (c : List (CGate n)) (i : Fin n) (p r : ℕ) : Prop :=
  c.getD p (CGate.cst false) = CGate.var i ∧
  (∀ q, c.getD q (CGate.cst false) = CGate.var i → q = p) ∧
  p ∈ childrenOf c r ∧ r < c.length - 1 ∧
  (∀ r', p ∈ childrenOf c r' → r' = r)

/-- Every mediated variable carries the positional 1-bit factorization. -/
theorem MediatedAt.factor {n : ℕ} {c : List (CGate n)} {f : (Fin n → Bool) → Bool}
    {i : Fin n} {p r : ℕ} (hcomp : computes c f) (h : MediatedAt c i p r) :
    ∃ G : Bool → (Fin n → Bool) → Bool,
      (∀ x, f x = G ((runFrom x [] c).getD r false) x) ∧
      (∀ (v : Bool) (x : Fin n → Bool) (b' : Bool),
        G v (Function.update x i b') = G v x) :=
  mediation_of_single_reader f i c hcomp p r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-! ### The aggregate capacity baseline -/

/-- **THE CAPACITY BASELINE (proved)**: one wire is the mediator configuration for at most two variables —
`K` simultaneously mediated selectors need `≥ K/2` distinct mediator wires.  Tight locally by the xor no-go:
this is edge-counting strength, and nothing more. -/
theorem mediator_capacity_two {n : ℕ} (c : List (CGate n)) (r : ℕ)
    (i₁ i₂ i₃ : Fin n) (p₁ p₂ p₃ : ℕ)
    (h₁ : MediatedAt c i₁ p₁ r) (h₂ : MediatedAt c i₂ p₂ r) (h₃ : MediatedAt c i₃ p₃ r)
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) : False := by
  have hp12 : p₁ ≠ p₂ := fun h =>
    h12 (CGate.var.inj ((h ▸ h₁.1).symm.trans h₂.1))
  have hp13 : p₁ ≠ p₃ := fun h =>
    h13 (CGate.var.inj ((h ▸ h₁.1).symm.trans h₃.1))
  have hp23 : p₂ ≠ p₃ := fun h =>
    h23 (CGate.var.inj ((h ▸ h₂.1).symm.trans h₃.1))
  exact three_children_impossible c r p₁ p₂ p₃ h₁.2.2.1 h₂.2.2.1 h₃.2.2.1 hp12 hp13 hp23

/-! ### Calibration: AND short-circuits before mediation -/

/-- **Calibration (proved)**: AND is top-decomposable at every variable — the trichotomy never reaches the
mediation question, so the accounting exerts no false pressure on easy functions. -/
theorem and_topDecomp {n : ℕ} (i : Fin n) :
    TopDecomp (fun x : Fin n → Bool => decide (∀ j, x j = true)) i := by
  classical
  refine ⟨(· && ·), fun x => decide (∀ j, j ≠ i → x j = true), ?_, ?_⟩
  · intro x
    show decide (∀ j, x j = true) = (x i && decide (∀ j, j ≠ i → x j = true))
    cases hxi : x i
    · rw [Bool.false_and]
      apply decide_eq_false
      intro hall
      rw [hall i] at hxi
      exact Bool.noConfusion hxi
    · rw [Bool.true_and]
      apply decide_eq_decide.mpr
      constructor
      · intro hall j _
        exact hall j
      · intro hres j
        by_cases hj : j = i
        · rw [hj]
          exact hxi
        · exact hres j hj
  · intro x b
    apply decide_eq_decide.mpr
    constructor
    · intro hall j hj
      have h := hall j hj
      rwa [Function.update_of_ne hj] at h
    · intro hall j hj
      rw [Function.update_of_ne hj]
      exact hall j hj

/-! ### The conversion: unmediated selectors feed the kill engine -/

/-- **THE CONVERSION (proved)**: an unmediated selector duplicates its variable gate or its wire is read
twice — any future "many selectors unmediated" theorem becomes kills beyond connectivity through
`cbudget_fanout_kill`. -/
theorem unmediated_dup_or_reuse (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N))
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hno : ¬∃ p r, MediatedAt c (sat3S2Sel N cIdx j) p r) :
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ c.getD p₁ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      c.getD p₂ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j)) ∨
    (∃ p r₁ r₂, r₁ ≠ r₂ ∧ c.getD p (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      p ∈ childrenOf c r₁ ∧ p ∈ childrenOf c r₂) := by
  by_cases hdup : ∃ p₁ p₂, p₁ ≠ p₂ ∧
      c.getD p₁ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      c.getD p₂ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j)
  · exact Or.inl hdup
  · push_neg at hdup
    rcases sat3_fanout_forcing N hv hm2 cIdx j c hcomp with hd | ⟨p, r, hp, hrint, hchild⟩
    · exact Or.inl hd
    · by_cases hsec : ∃ r', r' ≠ r ∧ p ∈ childrenOf c r'
      · obtain ⟨r', hne, hch'⟩ := hsec
        exact Or.inr ⟨p, r', r, hne, hp, hch', hchild⟩
      · exfalso
        push_neg at hsec
        apply hno
        refine ⟨p, r, hp, ?_, hchild, hrint, ?_⟩
        · intro q hq
          by_contra hne
          exact (hdup q p hne hq) hp
        · intro r' hch'
          by_contra hne
          exact (hsec r' hne) hch'

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.MediatedAt.factor
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.mediator_capacity_two
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.and_topDecomp
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.unmediated_dup_or_reuse
