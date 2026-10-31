import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSATFanoutForcing

/-!
# N-Frame: the 1-bit mediation theorem — the reuse obstruction as a factorization

The obstruction named by the forcing file, now a theorem: in a circuit whose variable wire has a *single*
reader, the variable's entire influence factors through one Boolean value — pin that one wire and the
variable goes dead.

  `mediation_of_single_reader` — **PROVED, the obstruction**: unique `var i` gate, unique reader `r` ⇒
        `∃ G, f x = G (wire r's value) x` with `G`'s second argument insensitive to `xᵢ` — the 1-bit mediator,
        constructed by pinning wire `r` to a constant (`G v x := output of c[r := cst v]`).
  `sat3_selector_trichotomy` — **PROVED, the live edge**: every circuit computing `sat3Family`, at every
        slot-2 selector, satisfies exactly one of: **duplication** (two variable gates), **reuse** (the wire
        read twice), or **1-bit mediation**.  Forcing the fan-out surplus that beats the connectivity record
        means refuting the third branch — proving SAT admits no per-variable 1-bit bottleneck.

## Honest scope

The trichotomy is the formal interface for every future reuse-forcing argument: branch three is a concrete
factorization to refute, not a slogan.  Refuting it is communication-flavored and open — the exact residue of
"one shared subcircuit cannot service too many independent witness constraints".  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Splice helpers -/

theorem splice_length {n : ℕ} (c : List (CGate n)) (r : ℕ) (g : CGate n)
    (hr : r < c.length) :
    (c.take r ++ g :: c.drop (r + 1)).length = c.length := by
  rw [List.length_append, List.length_cons, List.length_drop, take_len c r (by omega)]
  omega

theorem splice_getD {n : ℕ} (c : List (CGate n)) (r : ℕ) (g : CGate n) (hr : r < c.length)
    (q : ℕ) (hq : q ≠ r) :
    (c.take r ++ g :: c.drop (r + 1)).getD q (CGate.cst false)
      = c.getD q (CGate.cst false) := by
  have htlen : (c.take r).length = r := take_len c r (by omega)
  by_cases h2 : q < r
  · rw [List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h2,
      List.getD_eq_getElem?_getD]
  · have hqgt : r < q := by omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    rw [show q - (c.take r).length = (q - r - 1) + 1 by omega]
    show (c.drop (r + 1)).getD (q - r - 1) (CGate.cst false)
        = c.getD q (CGate.cst false)
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
      show r + 1 + (q - r - 1) = q by omega, List.getD_eq_getElem?_getD]

theorem splice_getD_self {n : ℕ} (c : List (CGate n)) (r : ℕ) (g : CGate n)
    (hr : r < c.length) :
    (c.take r ++ g :: c.drop (r + 1)).getD r (CGate.cst false) = g := by
  rw [List.getD_append_right _ _ _ _ (le_of_eq (take_len c r (by omega)))]
  rw [show r - (c.take r).length = 0 by
    rw [take_len c r (by omega)]
    omega]
  rfl

/-- Per-point gate replacement: agreeing on the actual prefix value preserves the output at that input. -/
theorem output_congr_point {n : ℕ} (c₁ : List (CGate n)) (g g' : CGate n)
    (c₂ : List (CGate n)) (x : Fin n → Bool)
    (heq : evalGate x (runFrom x [] c₁) g = evalGate x (runFrom x [] c₁) g') :
    output (c₁ ++ g' :: c₂) x = output (c₁ ++ g :: c₂) x := by
  have hrun : runFrom x [] (c₁ ++ g' :: c₂) = runFrom x [] (c₁ ++ g :: c₂) := by
    rw [show c₁ ++ g' :: c₂ = (c₁ ++ [g']) ++ c₂ by simp,
      show c₁ ++ g :: c₂ = (c₁ ++ [g]) ++ c₂ by simp,
      runFrom_append x [] (c₁ ++ [g']) c₂, runFrom_append x [] c₁ [g'],
      runFrom_append x [] (c₁ ++ [g]) c₂, runFrom_append x [] c₁ [g]]
    show runFrom x (runFrom x [] c₁ ++ [evalGate x (runFrom x [] c₁) g']) c₂
        = runFrom x (runFrom x [] c₁ ++ [evalGate x (runFrom x [] c₁) g]) c₂
    rw [heq]
  show (runFrom x [] (c₁ ++ g' :: c₂)).getD ((c₁ ++ g' :: c₂).length - 1) false
      = (runFrom x [] (c₁ ++ g :: c₂)).getD ((c₁ ++ g :: c₂).length - 1) false
  rw [hrun, show (c₁ ++ g' :: c₂).length = (c₁ ++ g :: c₂).length by
    rw [List.length_append, List.length_append, List.length_cons, List.length_cons]]

/-! ### The mediation theorem -/

/-- **THE 1-BIT MEDIATION (proved)**: with a unique variable gate and a unique reader of its wire, the
variable's entire influence factors through that one Boolean value — pin the reader's wire and the variable
goes dead.  This is the exact obstruction any reuse-forcing argument must refute. -/
theorem mediation_of_single_reader {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (c : List (CGate n)) (hcomp : computes c f)
    (p r : ℕ) (hpg : c.getD p (CGate.cst false) = CGate.var i)
    (hU : ∀ q, c.getD q (CGate.cst false) = CGate.var i → q = p)
    (hpr : p ∈ childrenOf c r) (hrint : r < c.length - 1)
    (hRuniq : ∀ r', p ∈ childrenOf c r' → r' = r) :
    ∃ G : Bool → (Fin n → Bool) → Bool,
      (∀ x, f x = G ((runFrom x [] c).getD r false) x) ∧
      (∀ (v : Bool) (x : Fin n → Bool) (b' : Bool),
        G v (Function.update x i b') = G v x) := by
  have hplr : p < r := children_lt c r p hpr
  have hrL : r < c.length := by omega
  refine ⟨fun v x => output (c.take r ++ CGate.cst v :: c.drop (r + 1)) x, ?_, ?_⟩
  · intro x
    have hsplit := circuit_split_at c r hrL
    have hgr : evalGate x (runFrom x [] (c.take r)) (c.getD r (CGate.cst false))
        = evalGate x (runFrom x [] (c.take r))
          (CGate.cst ((runFrom x [] c).getD r false)) :=
      (output_getD_at x c r hrL).symm
    have hcongr := output_congr_point (c.take r) (c.getD r (CGate.cst false))
      (CGate.cst ((runFrom x [] c).getD r false)) (c.drop (r + 1)) x hgr
    show f x = output (c.take r ++ CGate.cst ((runFrom x [] c).getD r false)
        :: c.drop (r + 1)) x
    rw [hcongr, ← hsplit]
    exact (hcomp x).symm
  · intro v x b'
    show output (c.take r ++ CGate.cst v :: c.drop (r + 1)) (Function.update x i b')
        = output (c.take r ++ CGate.cst v :: c.drop (r + 1)) x
    have hdlen : (c.take r ++ CGate.cst v :: c.drop (r + 1)).length = c.length :=
      splice_length c r (CGate.cst v) hrL
    show (runFrom (Function.update x i b') []
        (c.take r ++ CGate.cst v :: c.drop (r + 1))).getD
        ((c.take r ++ CGate.cst v :: c.drop (r + 1)).length - 1) false
      = (runFrom x [] (c.take r ++ CGate.cst v :: c.drop (r + 1))).getD
        ((c.take r ++ CGate.cst v :: c.drop (r + 1)).length - 1) false
    apply cone_val_agree (c.take r ++ CGate.cst v :: c.drop (r + 1))
      ((c.take r ++ CGate.cst v :: c.drop (r + 1)).length - 1)
      (Function.update x i b') x ?_ _
      (cone_self _ _)
    intro q hq i' hgate
    have hii : i' ≠ i := by
      intro hii'
      subst hii'
      have hqr : q ≠ r := by
        intro h'
        rw [h', splice_getD_self c r (CGate.cst v) hrL] at hgate
        simp at hgate
      rw [splice_getD c r (CGate.cst v) hrL q hqr] at hgate
      have hqp := hU q hgate
      subst hqp
      -- the variable's wire is unread in the pinned circuit's cone
      rcases cone_parent _ _ q hq with h' | ⟨r', hr'cone, hr'child⟩
      · rw [hdlen] at h'
        omega
      · have hr'r : r' ≠ r := by
          intro h''
          rw [h''] at hr'child
          rw [show childrenOf (c.take r ++ CGate.cst v :: c.drop (r + 1)) r = ∅ from
            childrenOf_eq_cst _ r v (splice_getD_self c r (CGate.cst v) hrL)] at hr'child
          exact absurd hr'child (Finset.notMem_empty q)
        have hch : childrenOf (c.take r ++ CGate.cst v :: c.drop (r + 1)) r'
            = childrenOf c r' := by
          unfold childrenOf
          rw [splice_getD c r (CGate.cst v) hrL r' hr'r]
        rw [hch] at hr'child
        exact hr'r (hRuniq r' hr'child)
    rw [Function.update_of_ne hii]

/-! ### The trichotomy: the live edge, formal -/

/-- **THE TRICHOTOMY (proved)**: every circuit computing SAT, at every slot-2 selector — duplication, reuse,
or 1-bit mediation.  Beating the connectivity record via fan-out means refuting the third branch. -/
theorem sat3_selector_trichotomy (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N))
    (c : List (CGate N)) (hcomp : computes c (sat3Family N)) :
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ c.getD p₁ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      c.getD p₂ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j)) ∨
    (∃ p r₁ r₂, r₁ ≠ r₂ ∧ c.getD p (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      p ∈ childrenOf c r₁ ∧ p ∈ childrenOf c r₂) ∨
    (∃ (p r : ℕ) (G : Bool → (Fin N → Bool) → Bool),
      c.getD p (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      p ∈ childrenOf c r ∧
      (∀ x, sat3Family N x = G ((runFrom x [] c).getD r false) x) ∧
      (∀ (v : Bool) (x : Fin N → Bool) (b' : Bool),
        G v (Function.update x (sat3S2Sel N cIdx j) b') = G v x)) := by
  by_cases hdup : ∃ p₁ p₂, p₁ ≠ p₂ ∧
      c.getD p₁ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      c.getD p₂ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j)
  · exact Or.inl hdup
  · push_neg at hdup
    rcases sat3_fanout_forcing N hv hm2 cIdx j c hcomp with hd | ⟨p, r, hp, hrint, hchild⟩
    · exact Or.inl hd
    · by_cases hsec : ∃ r', r' ≠ r ∧ p ∈ childrenOf c r'
      · obtain ⟨r', hne, hch'⟩ := hsec
        exact Or.inr (Or.inl ⟨p, r', r, hne, hp, hch', hchild⟩)
      · push_neg at hsec
        have hRuniq : ∀ r', p ∈ childrenOf c r' → r' = r := by
          intro r' hch'
          by_contra hne
          exact (hsec r' hne) hch'
        have hU : ∀ q, c.getD q (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) →
            q = p := by
          intro q hq
          by_contra hne
          exact (hdup q p hne hq) hp
        obtain ⟨G, hG1, hG2⟩ := mediation_of_single_reader (sat3Family N)
          (sat3S2Sel N cIdx j) c hcomp p r hp hU hchild hrint hRuniq
        exact Or.inr (Or.inr ⟨p, r, G, hp, hchild, hG1, hG2⟩)

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.mediation_of_single_reader
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_trichotomy
