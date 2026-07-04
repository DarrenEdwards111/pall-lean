import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDuplicateWireKill

/-!
# N-Frame: the thickness charge, part 1 — read-uniqueness, full connectivity, and the collapsed trichotomy

What the duplicate-wire kill *newly* forces, extracted in full.  The key observation: two var-gates for the
**same variable** are xor-duplicates with sign `false` — so `no_duplicate_wire` convicts them.

  `var_gate_unique` — **PROVED, the law (any function)**: a minimal circuit carries **at most one interior
        var-gate per variable**.  Minimal DAG observers read each input through a single port; all fanout
        of an input happens at wires, never by re-installing the variable.
  `minimal_full_cone` — **PROVED, Normal Form V**: every gate of a minimal circuit lies in the output cone.
        With NF I–IV: no constants, unary only at output, bins bidependent, every wire read, everything
        connected to the output.  The anatomy of minimal observers is closed.
  `sat3_selector_var_unique` — **PROVED**: for SAT the law has no output-position escape — a var-gate at
        the output makes SAT a dictator, refuted by the sign-bit flip at the workhorse context.
  `sat3_thickness_charge` — **PROVED, the collapsed trichotomy**: in a minimal circuit every unpinned
        selector is **reuse or thick-mediation** — the duplication branch is globally dead.  Combined with
        the capacity theorem: `K` tracked selectors force `≥ K/2` distinct thick merge gates, each owing a
        full obligation cube, with no duplication and no pass-through anywhere in the circuit.

## Honest scope — where the numerical overflow now lives

Part 1 is structure, not yet count: connectivity's `2mD − 1` is still the proved record.  The remaining
inequality has a sharper shape now.  In a minimal circuit each variable has exactly one var-gate; if every
wire also had fanout one the circuit would be a **read-once formula** — so the excess-fanout corner of the
open face is exactly: *prove SAT is not read-once*, the first `+1` beyond connectivity.  The general charge
needs the slot-multiplicity refinement of the cone count (`2·#bin + #un ≥ #cone − 1 + total excess fanout`,
a mechanical redo of the connectivity counting) plus `Ω(m)` forced excess — the mountain, now with the
adversary confined to reuse-or-thick and priced per slot.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### The wire value of a var-gate -/

theorem wire_val_var {n : ℕ} (c : List (CGate n)) (p : ℕ) (i : Fin n)
    (h : c.getD p (CGate.cst false) = CGate.var i) (x : Fin n → Bool) :
    (runFrom x [] c).getD p false = x i := by
  have hp : p < c.length := by
    rcases Nat.lt_or_ge p c.length with h' | h'
    · exact h'
    · exfalso
      have hd : c.getD p (CGate.cst false) = CGate.cst false :=
        List.getD_eq_default _ _ h'
      rw [h] at hd
      cases hd
  rw [output_getD_at x c p hp, h]
  rfl

/-! ### The law: at most one var-gate per variable -/

/-- **READ-UNIQUENESS (proved, any function)**: a minimal circuit carries at most one interior var-gate
per variable — two would be xor-duplicates with sign `false`. -/
theorem var_gate_unique {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (i : Fin n) (p₁ p₂ : ℕ) (hlt : p₁ < p₂) (hp₂ : p₂ < c.length - 1)
    (h₁ : c.getD p₁ (CGate.cst false) = CGate.var i)
    (h₂ : c.getD p₂ (CGate.cst false) = CGate.var i) : False :=
  no_duplicate_wire f c hcomp hmin p₁ p₂ hlt hp₂ false
    (fun x => by
      rw [wire_val_var c p₂ i h₂ x, wire_val_var c p₁ i h₁ x]
      exact (Bool.false_xor _).symm)

/-! ### Normal Form V: full connectivity -/

theorem mem_children_of_reads {n : ℕ} (c : List (CGate n)) (q p : ℕ) (hpq : p < q)
    (h : readsWire p (c.getD q (CGate.cst false)) = true) : p ∈ childrenOf c q := by
  cases hg : c.getD q (CGate.cst false) with
  | var i =>
    rw [hg] at h
    have hfalse : readsWire p (CGate.var i : CGate n) = false := rfl
    rw [hfalse] at h
    simp at h
  | cst b =>
    rw [hg] at h
    have hfalse : readsWire p (CGate.cst b : CGate n) = false := rfl
    rw [hfalse] at h
    simp at h
  | un op j =>
    rw [hg] at h
    have hj : j = p := by simpa [readsWire] using h
    subst hj
    rw [childrenOf_eq_un c q op j hg, if_pos hpq]
    exact Finset.mem_singleton_self j
  | bin op j k =>
    rw [hg] at h
    have hjk : j = p ∨ k = p := by simpa [readsWire] using h
    rw [childrenOf_eq_bin c q op j k hg]
    rcases hjk with hj | hk
    · subst hj
      exact Finset.mem_union_left _ (by rw [if_pos hpq]; exact Finset.mem_singleton_self j)
    · subst hk
      exact Finset.mem_union_right _ (by rw [if_pos hpq]; exact Finset.mem_singleton_self k)

/-- **NORMAL FORM V (proved)**: every gate of a minimal circuit lies in the output cone. -/
theorem minimal_full_cone {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f) :
    ∀ p, p < c.length → p ∈ coneOf c (c.length - 1) := by
  have main : ∀ d p, p < c.length → c.length - 1 - p = d →
      p ∈ coneOf c (c.length - 1) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro p hp hd
      rcases Nat.eq_or_lt_of_le (Nat.le_pred_of_lt hp) with heq | hlt
      · rw [heq]
        exact cone_self c (c.length - 1)
      · obtain ⟨q, hpq, hread⟩ := minimal_wire_read f c hcomp hmin p hlt
        have hq : q < c.length := by
          rcases Nat.lt_or_ge q c.length with h | h
          · exact h
          · exfalso
            rw [List.getD_eq_default _ _ h] at hread
            have hfalse : readsWire p (CGate.cst false : CGate n) = false := rfl
            rw [hfalse] at hread
            simp at hread
        have hqcone : q ∈ coneOf c (c.length - 1) :=
          ih (c.length - 1 - q) (by omega) q hq rfl
        exact cone_child c (c.length - 1) q hqcone p (mem_children_of_reads c q p hpq hread)
  intro p hp
  exact main (c.length - 1 - p) p hp rfl

/-! ### SAT: the law has no output-position escape -/

/-- **PROVED**: two var-gates for the same selector are impossible in a minimal SAT circuit — interior
duplicates die by the law, and an output var-gate makes SAT a dictator, refuted by the sign flip. -/
theorem sat3_selector_var_unique (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N))
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (p₁ p₂ : ℕ) (hlt : p₁ < p₂)
    (h₁ : c.getD p₁ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j))
    (h₂ : c.getD p₂ (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j)) : False := by
  have hp₂ : p₂ < c.length := by
    rcases Nat.lt_or_ge p₂ c.length with h | h
    · exact h
    · exfalso
      have hd : c.getD p₂ (CGate.cst false) = CGate.cst false :=
        List.getD_eq_default _ _ h
      rw [h₂] at hd
      cases hd
  rcases Nat.lt_or_ge p₂ (c.length - 1) with hint | hout
  · exact var_gate_unique (sat3Family N) c hcomp hmin _ p₁ p₂ hlt hint h₁ h₂
  · have hp₂eq : p₂ = c.length - 1 := by omega
    have hdict : ∀ x : Fin N → Bool, sat3Family N x = x (sat3S2Sel N cIdx j) := by
      intro x
      have h : (runFrom x [] c).getD (c.length - 1) false = sat3Family N x := hcomp x
      rw [← hp₂eq, output_getD_at x c p₂ hp₂, h₂] at h
      exact h.symm
    have hkv : sat3M N - 2 ≤ sat3V N := by
      have := sat3M_pred_le_sat3V N
      omega
    have hbeh : ∀ a : Bool,
        sat3Family N (Function.update (sat3Patch N cIdx
          (sat3Context N cIdx hk (fun _ => false)) (sat3Probe N ⟨0, hv⟩ false))
          (sat3SignBit N cIdx) a) = xor false a := by
      intro a
      rw [patch_probe_update]
      exact sat3Context_probe_eval N hv hk hkv cIdx (fun _ => false)
        ⟨0, by omega⟩ ⟨0, hv⟩ rfl a
    have hne : sat3S2Sel N cIdx j ≠ sat3SignBit N cIdx :=
      sat3S2Sel_ne_signBit N cIdx j cIdx
    have ht := hbeh true
    have hf := hbeh false
    rw [hdict, Function.update_of_ne hne] at ht
    rw [hdict, Function.update_of_ne hne] at hf
    exact absurd (ht.symm.trans hf) (by decide)

/-! ### The collapsed trichotomy -/

/-- **THE THICKNESS CHARGE, PART 1 (proved)**: in a minimal circuit every unpinned selector is reuse or
thick-mediation — duplication is globally dead, pass-through is globally dead. -/
theorem sat3_thickness_charge (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) (hjv : sat3M N - 2 ≤ j.val)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N)) :
    (∃ p r₁ r₂, r₁ ≠ r₂ ∧ c.getD p (CGate.cst false) = CGate.var (sat3S2Sel N cIdx j) ∧
      p ∈ childrenOf c r₁ ∧ p ∈ childrenOf c r₂) ∨
    (∃ p r, MediatedAt c (sat3S2Sel N cIdx j) p r ∧
      ∃ q ∈ coneOf c r, ∃ i' : Fin N, i' ≠ sat3S2Sel N cIdx j ∧
        c.getD q (CGate.cst false) = CGate.var i') := by
  rcases sat3_selector_terminal N hv (by omega) cIdx j c hcomp with
    ⟨p₁, p₂, hne, h₁, h₂⟩ | hr | ⟨p, r, hmed⟩
  · exfalso
    rcases Nat.lt_trichotomy p₁ p₂ with hlt | heq | hgt
    · exact sat3_selector_var_unique N hv hm3 hk cIdx j c hcomp hmin p₁ p₂ hlt h₁ h₂
    · exact hne heq
    · exact sat3_selector_var_unique N hv hm3 hk cIdx j c hcomp hmin p₂ p₁ hgt h₂ h₁
  · exact Or.inl hr
  · exact Or.inr ⟨p, r, hmed,
      sat3_selector_mediator_thick N hv hm3 hk cIdx j hjv c hcomp hmin p r hmed⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.var_gate_unique
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.minimal_full_cone
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_thickness_charge
