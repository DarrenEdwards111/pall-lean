import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDAGFanout

/-!
# N-Frame: SAT forces wire use — no-reuse circuits are top-decomposable, and SAT is not

The forcing half of the reuse question, settled: a circuit that neither duplicates a variable's gate nor reads
its wire anywhere in the interior computes a **top-decomposable** function — all of the variable's influence
rides a single edge into the output gate.  SAT's selector structure refutes top decomposition (the
identity/constant-true/constant-false behavior triple), so:

  `topDecomp_of_no_reuse` — **PROVED, the structure theorem**: unique variable gate + no interior reader
        `⇒ TopDecomp f i` — for *any* circuit computing `f`, minimal or not.
  `sat3_selector_notTopDecomp` — **PROVED**: the three behaviors at every slot-2 selector, packaged.
  `sat3_fanout_forcing` — **PROVED, the forcing**: **every** circuit computing `sat3Family` either duplicates
        a slot-2 selector's variable gate or reads its wire strictly before the output — `m·v` wires that no
        circuit may leave to the output gate alone.

## Honest scope — the obstruction, exactly

This forces *use*, not *reuse*: usage `≥ 1` beyond the output, hence the two-kill rate — it does not force
fan-out `≥ 2`.  The obstruction is now precise: a circuit may route each selector through a **single interior
reader**, compressing the variable's entire influence into one Boolean wire — a 1-bit mediator.  Nothing in the
behavior triple refutes that: unlike top decomposition, the mediator-to-output map may vary with the context.
Forcing reuse therefore means proving SAT admits no such per-variable 1-bit bottleneck — a
communication-flavored question that is the exact formal residue of "one shared subcircuit cannot service too
many independent witness constraints", and the entry price of every `2n`-internal-and-beyond bound.  Named,
not claimed.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Independence gives the degenerate top decomposition. -/
theorem topDecomp_of_indep {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (h : ∀ (x : Fin n → Bool) (b' : Bool), f (Function.update x i b') = f x) :
    TopDecomp f i :=
  ⟨fun _ c' => c', f, fun _ => rfl, h⟩

/-- **THE STRUCTURE THEOREM (proved)**: a circuit that neither duplicates the variable's gate nor reads its
wire in the interior computes a top-decomposable function — sharing or not, all influence rides one edge. -/
theorem topDecomp_of_no_reuse {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n)
    (c : List (CGate n)) (hcomp : computes c f)
    (hU : ∀ p₁ p₂, c.getD p₁ (CGate.cst false) = CGate.var i →
      c.getD p₂ (CGate.cst false) = CGate.var i → p₁ = p₂)
    (hNoR : ∀ p r, c.getD p (CGate.cst false) = CGate.var i → r < c.length - 1 →
      p ∉ childrenOf c r) :
    TopDecomp f i := by
  by_cases hpc : ∃ p ∈ coneOf c (c.length - 1), c.getD p (CGate.cst false) = CGate.var i
  · obtain ⟨p, hpcone, hpg⟩ := hpc
    have hpL : p < c.length := by
      by_contra h'
      rw [List.getD_eq_default _ _ (by omega)] at hpg
      simp at hpg
    by_cases hproot : p = c.length - 1
    · -- the output gate is the variable: f = xᵢ
      refine ⟨fun a _ => a, fun _ => false, ?_, fun _ _ => rfl⟩
      intro x
      rw [← hcomp x]
      show (runFrom x [] c).getD (c.length - 1) false = x i
      rw [output_getD_at x c (c.length - 1) (by omega), ← hproot, hpg]
      rfl
    · have hpint : p < c.length - 1 := by omega
      have hrootchild : p ∈ childrenOf c (c.length - 1) := by
        rcases cone_parent c (c.length - 1) p hpcone with h' | ⟨r, hrcone, hrchild⟩
        · omega
        · have hrle := cone_le c (c.length - 1) r hrcone
          by_cases hr : r < c.length - 1
          · exact absurd hrchild (hNoR p r hpg hr)
          · have hreq : r = c.length - 1 := by omega
            exact hreq ▸ hrchild
      have hout : ∀ x : Fin n → Bool, f x
          = evalGate x (runFrom x [] (c.take (c.length - 1)))
              (c.getD (c.length - 1) (CGate.cst false)) := by
        intro x
        rw [← hcomp x]
        exact output_getD_at x c (c.length - 1) (by omega)
      have hwp : ∀ x : Fin n → Bool,
          (runFrom x [] (c.take (c.length - 1))).getD p false = x i := by
        intro x
        rw [takeRun_getD x c (c.length - 1) p (by omega) (by omega),
          output_getD_at x c p hpL, hpg]
        rfl
      have hother : ∀ m, m < c.length - 1 → m ≠ p →
          ∀ (x : Fin n → Bool) (b'' : Bool),
            (runFrom (Function.update x i b'') [] c).getD m false
              = (runFrom x [] c).getD m false := by
        intro m hm hmp x b''
        apply cone_val_agree c m (Function.update x i b'') x ?_ m (cone_self c m)
        intro q hq i' hgate
        have hii : i' ≠ i := by
          intro hii'
          subst hii'
          have hqp := hU q p hgate hpg
          subst hqp
          rcases cone_parent c m q hq with h' | ⟨r', hr'cone, hr'child⟩
          · exact hmp h'.symm
          · have hr'le := cone_le c m r' hr'cone
            exact hNoR q r' hgate (by omega) hr'child
        rw [Function.update_of_ne hii]
      cases hgroot : c.getD (c.length - 1) (CGate.cst false) with
      | var j =>
        rw [childrenOf_eq_var c (c.length - 1) j hgroot] at hrootchild
        exact absurd hrootchild (Finset.notMem_empty p)
      | cst b' =>
        rw [childrenOf_eq_cst c (c.length - 1) b' hgroot] at hrootchild
        exact absurd hrootchild (Finset.notMem_empty p)
      | un u' j =>
        rw [childrenOf_eq_un c (c.length - 1) u' j hgroot] at hrootchild
        have hjp : j = p := by
          by_cases hj : j < c.length - 1
          · rw [if_pos hj] at hrootchild
            rw [Finset.mem_singleton] at hrootchild
            omega
          · rw [if_neg hj] at hrootchild
            exact absurd hrootchild (Finset.notMem_empty p)
        rw [hjp] at hgroot
        refine ⟨fun a _ => u' a, fun _ => false, ?_, fun _ _ => rfl⟩
        intro x
        have h := hout x
        rw [hgroot] at h
        rw [h]
        show u' ((runFrom x [] (c.take (c.length - 1))).getD p false) = u' (x i)
        rw [hwp x]
      | bin op' j k =>
        rw [childrenOf_eq_bin c (c.length - 1) op' j k hgroot] at hrootchild
        have hfeq : ∀ x : Fin n → Bool, f x
            = op' ((runFrom x [] (c.take (c.length - 1))).getD j false)
                ((runFrom x [] (c.take (c.length - 1))).getD k false) := by
          intro x
          have h := hout x
          rw [hgroot] at h
          exact h
        have hjk : j = p ∨ k = p := by
          rcases Finset.mem_union.mp hrootchild with h' | h'
          · by_cases hj : j < c.length - 1
            · rw [if_pos hj] at h'
              rw [Finset.mem_singleton] at h'
              omega
            · rw [if_neg hj] at h'
              exact absurd h' (Finset.notMem_empty p)
          · by_cases hk : k < c.length - 1
            · rw [if_pos hk] at h'
              rw [Finset.mem_singleton] at h'
              omega
            · rw [if_neg hk] at h'
              exact absurd h' (Finset.notMem_empty p)
        by_cases hjp : j = p
        · rw [hjp] at hfeq
          by_cases hkp2 : k = p
          · rw [hkp2] at hfeq
            refine ⟨fun a _ => op' a a, fun _ => false, ?_, fun _ _ => rfl⟩
            intro x
            rw [hfeq x, hwp x]
          · by_cases hkL : k < c.length - 1
            · refine ⟨op', fun x => (runFrom x [] c).getD k false, ?_, ?_⟩
              · intro x
                rw [hfeq x, hwp x, takeRun_getD x c (c.length - 1) k hkL (by omega)]
              · intro x b''
                exact hother k hkL hkp2 x b''
            · refine ⟨op', fun _ => false, ?_, fun _ _ => rfl⟩
              intro x
              rw [hfeq x, hwp x]
              congr 1
              rw [List.getD_eq_default _ false (by
                rw [runFrom_length x (c.take (c.length - 1)) []]
                show ([] : List Bool).length + (c.take (c.length - 1)).length ≤ k
                simp only [List.length_nil]
                rw [take_len c (c.length - 1) (by omega)]
                omega)]
        · have hkp : k = p := hjk.resolve_left hjp
          rw [hkp] at hfeq
          by_cases hjL : j < c.length - 1
          · refine ⟨fun a c'' => op' c'' a, fun x => (runFrom x [] c).getD j false, ?_, ?_⟩
            · intro x
              show f x = op' ((runFrom x [] c).getD j false) (x i)
              rw [hfeq x, hwp x, takeRun_getD x c (c.length - 1) j hjL (by omega)]
            · intro x b''
              exact hother j hjL hjp x b''
          · refine ⟨fun a c'' => op' c'' a, fun _ => false, ?_, fun _ _ => rfl⟩
            intro x
            show f x = op' false (x i)
            rw [hfeq x, hwp x]
            congr 1
            rw [List.getD_eq_default _ false (by
              rw [runFrom_length x (c.take (c.length - 1)) []]
              show ([] : List Bool).length + (c.take (c.length - 1)).length ≤ j
              simp only [List.length_nil]
              rw [take_len c (c.length - 1) (by omega)]
              omega)]
  · -- no variable gate in the cone: f is independent of the variable
    push_neg at hpc
    apply topDecomp_of_indep
    intro x b'
    rw [← hcomp (Function.update x i b'), ← hcomp x]
    show (runFrom (Function.update x i b') [] c).getD (c.length - 1) false
        = (runFrom x [] c).getD (c.length - 1) false
    apply cone_val_agree c (c.length - 1) (Function.update x i b') x ?_ (c.length - 1)
      (cone_self c (c.length - 1))
    intro q hq i' hgate
    have hii : i' ≠ i := by
      intro hii'
      subst hii'
      exact (hpc q hq) hgate
    rw [Function.update_of_ne hii]

/-! ### SAT refutes the decomposition at every slot-2 selector -/

/-- **The behavior triple, packaged (proved)**: `sat3Family` is not top-decomposable at any slot-2 selector. -/
theorem sat3_selector_notTopDecomp (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) :
    ¬TopDecomp (sat3Family N) (sat3S2Sel N cIdx j) := by
  set c' : Fin (sat3M N) := if cIdx.val = 0 then ⟨1, hm2⟩ else ⟨0, by omega⟩ with hc'
  have hc'ne : c'.val ≠ cIdx.val := by
    rw [hc']
    by_cases hz : cIdx.val = 0
    · rw [if_pos hz, hz]
      show (1 : ℕ) ≠ 0
      omega
    · rw [if_neg hz]
      show (0 : ℕ) ≠ cIdx.val
      omega
  apply notTopDecomp_of_behaviors (sat3Family N) (sat3S2Sel N cIdx j)
    (sat3ZBase N cIdx) (sat3AllLive N) (sat3ZBase N c')
  · intro a
    cases a
    · rw [show Function.update (sat3ZBase N cIdx) (sat3S2Sel N cIdx j) false
          = sat3ZBase N cIdx by
        rw [← sat3ZBase_s2 N cIdx cIdx j]
        exact Function.update_eq_self _ _]
      exact sat3ZBase_unsat N cIdx
    · exact sat3ZBase_flip_sat N hv cIdx j
  · intro a
    exact sat3AllLive_flip_sat N hv cIdx j a
  · intro a
    exact sat3ZBase_foreign_unsat N cIdx c' hc'ne j a

/-- **THE FORCING (proved)**: every circuit computing SAT either duplicates a slot-2 selector's variable gate
or reads its wire strictly before the output — for all `m·v` such selectors. -/
theorem sat3_fanout_forcing (N : ℕ) (hv : 1 ≤ sat3V N) (hm2 : 2 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N))
    (c : List (CGate N)) (hcomp : computes c (sat3Family N)) :
    (∃ p₁ p₂, p₁ ≠ p₂ ∧ c.getD p₁ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      c.getD p₂ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j)) ∨
    (∃ p r, c.getD p (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      r < c.length - 1 ∧ p ∈ childrenOf c r) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply sat3_selector_notTopDecomp N hv hm2 cIdx j
  apply topDecomp_of_no_reuse (sat3Family N) (sat3S2Sel N cIdx j) c hcomp
  · intro p₁ p₂ hp₁ hp₂
    by_contra hne
    exact h1 p₁ p₂ hne hp₁ hp₂
  · intro p r hp hr
    exact h2 p r hp hr

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.topDecomp_of_no_reuse
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_notTopDecomp
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_fanout_forcing
