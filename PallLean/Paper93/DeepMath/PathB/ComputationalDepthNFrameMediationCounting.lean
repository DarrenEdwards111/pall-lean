import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATMediation

/-!
# N-Frame: mediation counting is closed — one wire can mediate everything

The counting route through the trichotomy's third branch, settled negatively.  Two facts:

  `sat3_mediation_counting_nogo` — **PROVED, the no-go**: there is a circuit computing `sat3Family` in which a
        **single interior wire 1-bit-mediates every one of the `N` input coordinates simultaneously** — any
        wire whose value determines the output mediates all variables at once (`G v x := v`).  The mediation
        factorization, as a predicate, is free to share: counting mediators cannot force anything.
  `three_children_impossible` / `children_card_le_two` — **PROVED, the capacity fact**: the only per-gate
        limit is fan-in — a gate reads at most two wires — and counting *adjacent* mediators (the unique
        readers of the variable gates) is therefore edge-counting, which the connectivity bound already
        collects in full.

## Honest scope — what this closes and what it leaves

Closed: no counting argument over the mediation predicate, nor over reader adjacency, can beat the `≈ 2N`
connectivity record.  Left, sharpened: refuting branch three of the trichotomy must use *where* the mediator
sits — the unique reader's value is computed at its position, from wires below it, before the downstream
context acts — an information-flow property of the specific factorization, not its number.  That is the
formal content of "one shared subcircuit cannot service too many independent witness constraints", and it is
open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The capacity fact: fan-in two -/

theorem gateWeight_le_two {n : ℕ} (c : List (CGate n)) (p : ℕ) : gateWeight c p ≤ 2 := by
  unfold gateWeight
  cases c.getD p (CGate.cst false) with
  | var i => show (0 : ℕ) ≤ 2; omega
  | cst b => show (0 : ℕ) ≤ 2; omega
  | un op j => show (1 : ℕ) ≤ 2; omega
  | bin op j k => show (2 : ℕ) ≤ 2; omega

theorem children_card_le_two {n : ℕ} (c : List (CGate n)) (r : ℕ) :
    (childrenOf c r).card ≤ 2 :=
  le_trans (childrenOf_card_le c r) (gateWeight_le_two c r)

/-- **A reader serves at most two wires (proved)** — adjacency counting is edge counting. -/
theorem three_children_impossible {n : ℕ} (c : List (CGate n)) (r : ℕ)
    (p₁ p₂ p₃ : ℕ) (h₁ : p₁ ∈ childrenOf c r) (h₂ : p₂ ∈ childrenOf c r)
    (h₃ : p₃ ∈ childrenOf c r) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) :
    False := by
  have hsub : ({p₁, p₂, p₃} : Finset ℕ) ⊆ childrenOf c r := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · exact h₁
    · rcases Finset.mem_insert.mp hq' with rfl | hq''
      · exact h₂
      · rw [Finset.mem_singleton] at hq''
        exact hq'' ▸ h₃
  have hcard : ({p₁, p₂, p₃} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      intro hmem
      rcases Finset.mem_insert.mp hmem with h | h
      · exact h12 h
      · rw [Finset.mem_singleton] at h
        exact h13 h)]
    rw [Finset.card_insert_of_notMem (by
      intro hmem
      rw [Finset.mem_singleton] at hmem
      exact h23 hmem)]
    rfl
  have h := Finset.card_le_card hsub
  have h2 := children_card_le_two c r
  omega

/-! ### The universal mediator -/

/-- **The universal mediator (proved)**: every Boolean function has a circuit with an interior wire carrying
the output value itself. -/
theorem universal_mediator {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∃ (d : List (CGate n)) (r : ℕ), computes d f ∧ r < d.length - 1 ∧
      ∀ x, (runFrom x [] d).getD r false = f x := by
  have hcomp : computes (compile 0 (dnfFor f)) f := by
    have := compile_computes (dnfFor f)
    rwa [show (fun x => eval (dnfFor f) x) = f from
      funext (fun x => by rw [eval_dnfFor])] at this
  set c : List (CGate n) := compile 0 (dnfFor f) with hc
  have hcpos : 1 ≤ c.length := by
    rw [hc, compile_length]
    exact volume_pos _
  refine ⟨c ++ [CGate.un (fun a => a) (c.length - 1)], c.length - 1, ?_, ?_, ?_⟩
  · intro x
    show (runFrom x [] (c ++ [CGate.un (fun a => a) (c.length - 1)])).getD
        ((c ++ [CGate.un (fun a => a) (c.length - 1)]).length - 1) false = f x
    rw [runFrom_append]
    show ((runFrom x [] c) ++ [evalGate x (runFrom x [] c)
        (CGate.un (fun a => a) (c.length - 1))]).getD
        ((c ++ [CGate.un (fun a => a) (c.length - 1)]).length - 1) false = f x
    have hV : (runFrom x [] c).length = c.length := by
      rw [runFrom_length]
      simp
    rw [show (c ++ [(CGate.un (fun a => a) (c.length - 1) : CGate n)]).length - 1
        = (runFrom x [] c).length by
      rw [List.length_append, hV]
      show c.length + 1 - 1 = c.length
      omega]
    rw [getD_concat]
    show (runFrom x [] c).getD (c.length - 1) false = f x
    exact hcomp x
  · rw [List.length_append]
    show c.length - 1 < c.length + 1 - 1
    omega
  · intro x
    rw [runFrom_append]
    show (runFrom x (runFrom x [] c) [CGate.un (fun a => a) (c.length - 1)]).getD
        (c.length - 1) false = f x
    show ((runFrom x [] c) ++ [evalGate x (runFrom x [] c)
        (CGate.un (fun a => a) (c.length - 1))]).getD (c.length - 1) false = f x
    have hV : (runFrom x [] c).length = c.length := by
      rw [runFrom_length]
      simp
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hcomp x

/-- **THE NO-GO (proved)**: a circuit computing SAT in which one interior wire 1-bit-mediates every input
coordinate simultaneously — the mediation factorization is free to share, and counting it forces nothing. -/
theorem sat3_mediation_counting_nogo (N : ℕ) :
    ∃ (d : List (CGate N)) (r : ℕ), computes d (sat3Family N) ∧ r < d.length - 1 ∧
      ∀ i : Fin N, ∃ G : Bool → (Fin N → Bool) → Bool,
        (∀ x, sat3Family N x = G ((runFrom x [] d).getD r false) x) ∧
        (∀ (v : Bool) (x : Fin N → Bool) (b' : Bool),
          G v (Function.update x i b') = G v x) := by
  obtain ⟨d, r, hcomp, hint, hval⟩ := universal_mediator (sat3Family N)
  exact ⟨d, r, hcomp, hint, fun i =>
    ⟨fun v _ => v, fun x => (hval x).symm, fun _ _ _ => rfl⟩⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.three_children_impossible
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.universal_mediator
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_mediation_counting_nogo
