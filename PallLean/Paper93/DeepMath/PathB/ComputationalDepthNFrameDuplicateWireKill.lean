import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSemanticObligation

/-!
# N-Frame: the duplicate-wire kill — charging the redundancy, and the death of pass-through

Step 4 of the semantic campaign, delivered as a kill rather than a count.  The passthrough branch of the
dichotomy says `wire r = ε ⊕ wire p` **globally** — and a global identity supports surgery: every reader of
`r` can read `p` instead, with its op pre-composed with the sign `ε`.  Then nothing reads `r`, and Normal
Form IV convicts the circuit of non-minimality.

  `rewireGate` / `runFrom_rewire` — **PROVED, the surgery**: redirect all references to `r` onto `p` with
        ε-adjusted ops; the entire run is unchanged, gate for gate.
  `no_duplicate_wire` — **PROVED, the charge**: a minimal circuit contains **no** pair of xor-duplicate
        wires with the later one interior.  Two budget-priced wires may never carry the same one bit.
  `sat3_sign_mediator_thick` / `sat3_selector_mediator_thick` — **PROVED, the door closes**: in a *minimal*
        circuit, the passthrough branch of the dichotomy is impossible — every mediated sign bit and every
        tracked selector has a **thick** mediator wire, one whose cone reads a second variable.  The
        pass-through exception, which blocked every counting argument since the mediation era began, is
        dead at the minimal-circuit level.

## Honest scope

What this charges: exact global duplication — the only cone-thin way to satisfy an obligation cube — cannot
occur in a minimal circuit.  What remains open: charging **thickness**.  Every tracked mediator wire must
now genuinely merge its coordinate with other information, but connectivity already pays for one merge per
variable, and a binary tree's internal nodes are all thick — so thickness alone does not yet overflow
`2mD − 1`.  The closing inequality — the aggregate of forced merges exceeding the tree minimum — is the one
open statement, now with the adversary confined to a single branch.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Positional access for the rewired suffix -/

theorem takeMap_getD {n : ℕ} (d : List (CGate n)) (Φ : CGate n → CGate n) (m q : ℕ)
    (hmq : m ≤ q) (hq : q < d.length) :
    (d.take m ++ (d.drop m).map Φ).getD q (CGate.cst false)
      = Φ (d.getD q (CGate.cst false)) := by
  have htlen : (d.take m).length = m := take_len d m (by omega)
  rw [List.getD_append_right _ _ _ _ (by omega : (d.take m).length ≤ q)]
  rw [htlen]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop]
  rw [show m + (q - m) = q by omega]
  rw [List.getElem?_eq_getElem hq]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  rfl

/-! ### The rewiring surgery -/

/-- Redirect every reference to wire `r` onto wire `p`, pre-composing the op with the sign `ε`. -/
def rewireGate {n : ℕ} (r p : ℕ) (ε : Bool) : CGate n → CGate n
  | .var i => .var i
  | .cst b => .cst b
  | .un op j => if j = r then .un (fun b => op (xor ε b)) p else .un op j
  | .bin op j k =>
      .bin (fun a b => op (if j = r then xor ε a else a) (if k = r then xor ε b else b))
        (if j = r then p else j) (if k = r then p else k)

theorem evalGate_rewire {n : ℕ} (x : Fin n → Bool) (vals : List Bool) (r p : ℕ) (ε : Bool)
    (hrel : vals.getD r false = xor ε (vals.getD p false)) (g : CGate n) :
    evalGate x vals (rewireGate r p ε g) = evalGate x vals g := by
  cases g with
  | var i => rfl
  | cst b => rfl
  | un op j =>
    by_cases hj : j = r
    · simp only [rewireGate, if_pos hj]
      show op (xor ε (vals.getD p false)) = op (vals.getD j false)
      rw [hj, hrel]
    · simp only [rewireGate, if_neg hj]
  | bin op j k =>
    simp only [rewireGate]
    by_cases hj : j = r
    · by_cases hk : k = r
      · rw [if_pos hj, if_pos hk]
        show op (if j = r then xor ε (vals.getD p false) else vals.getD p false)
            (if k = r then xor ε (vals.getD p false) else vals.getD p false)
          = op (vals.getD j false) (vals.getD k false)
        rw [if_pos hj, if_pos hk, hj, hk, hrel]
      · rw [if_pos hj, if_neg hk]
        show op (if j = r then xor ε (vals.getD p false) else vals.getD p false)
            (if k = r then xor ε (vals.getD k false) else vals.getD k false)
          = op (vals.getD j false) (vals.getD k false)
        rw [if_pos hj, if_neg hk, hj, hrel]
    · by_cases hk : k = r
      · rw [if_neg hj, if_pos hk]
        show op (if j = r then xor ε (vals.getD j false) else vals.getD j false)
            (if k = r then xor ε (vals.getD p false) else vals.getD p false)
          = op (vals.getD j false) (vals.getD k false)
        rw [if_neg hj, if_pos hk, hk, hrel]
      · rw [if_neg hj, if_neg hk]
        show op (if j = r then xor ε (vals.getD j false) else vals.getD j false)
            (if k = r then xor ε (vals.getD k false) else vals.getD k false)
          = op (vals.getD j false) (vals.getD k false)
        rw [if_neg hj, if_neg hk]

theorem readsWire_rewire {n : ℕ} (r p : ℕ) (hpr : p ≠ r) (ε : Bool) (g : CGate n) :
    readsWire r (rewireGate r p ε g) = false := by
  cases g with
  | var i => rfl
  | cst b => rfl
  | un op j =>
    by_cases hj : j = r
    · simp [rewireGate, hj, readsWire, hpr]
    · simp [rewireGate, hj, readsWire]
  | bin op j k =>
    by_cases hj : j = r <;> by_cases hk : k = r <;>
      simp [rewireGate, hj, hk, readsWire, hpr]

theorem runFrom_rewire {n : ℕ} (x : Fin n → Bool) (r p : ℕ) (ε : Bool) :
    ∀ (gs : List (CGate n)) (vals : List Bool), p < vals.length → r < vals.length →
      vals.getD r false = xor ε (vals.getD p false) →
      runFrom x vals (gs.map (rewireGate r p ε)) = runFrom x vals gs := by
  intro gs
  induction gs with
  | nil => intro vals _ _ _; rfl
  | cons g rest ih =>
    intro vals hp hr hrel
    show runFrom x (vals ++ [evalGate x vals (rewireGate r p ε g)])
        (rest.map (rewireGate r p ε))
        = runFrom x (vals ++ [evalGate x vals g]) rest
    rw [evalGate_rewire x vals r p ε hrel g]
    exact ih (vals ++ [evalGate x vals g])
      (by rw [List.length_append]; omega)
      (by rw [List.length_append]; omega)
      (by rw [List.getD_append _ _ _ _ hr, List.getD_append _ _ _ _ hp]; exact hrel)

/-! ### The charge: minimal circuits carry no duplicate wires -/

/-- **THE REDUNDANCY CHARGE (proved)**: a minimal circuit contains no pair of xor-duplicate wires with the
later one interior — two budget-priced wires may never carry the same one bit. -/
theorem no_duplicate_wire {n : ℕ} (f : (Fin n → Bool) → Bool) (c : List (CGate n))
    (hcomp : computes c f) (hmin : c.length = cbudget f)
    (p r : ℕ) (hpr : p < r) (hr : r < c.length - 1) (ε : Bool)
    (hdup : ∀ x : Fin n → Bool,
      (runFrom x [] c).getD r false = xor ε ((runFrom x [] c).getD p false)) : False := by
  classical
  set c' : List (CGate n) :=
    c.take (r + 1) ++ (c.drop (r + 1)).map (rewireGate r p ε) with hc'
  have hlen : c'.length = c.length := by
    rw [hc', List.length_append, List.length_map, List.length_take, List.length_drop]
    omega
  have hrun : ∀ x, runFrom x [] c' = runFrom x [] c := by
    intro x
    have hVlen : (runFrom x [] (c.take (r + 1))).length = r + 1 := by
      rw [runFrom_length]
      simp only [List.length_nil, List.length_take]
      omega
    have hfull : runFrom x [] c
        = runFrom x (runFrom x [] (c.take (r + 1))) (c.drop (r + 1)) := by
      conv_lhs => rw [← List.take_append_drop (r + 1) c]
      rw [runFrom_append]
    have hrelV : (runFrom x [] (c.take (r + 1))).getD r false
        = xor ε ((runFrom x [] (c.take (r + 1))).getD p false) := by
      have h1 := runFrom_getD_stable x (c.drop (r + 1)) (runFrom x [] (c.take (r + 1)))
        r (by rw [hVlen]; omega)
      have h2 := runFrom_getD_stable x (c.drop (r + 1)) (runFrom x [] (c.take (r + 1)))
        p (by rw [hVlen]; omega)
      rw [← h1, ← h2, ← hfull]
      exact hdup x
    rw [hc', runFrom_append]
    conv_rhs => rw [← List.take_append_drop (r + 1) c]
    rw [runFrom_append]
    exact runFrom_rewire x r p ε (c.drop (r + 1)) (runFrom x [] (c.take (r + 1)))
      (by rw [hVlen]; omega) (by rw [hVlen]; omega) hrelV
  have hcomp' : computes c' f := by
    intro x
    show (runFrom x [] c').getD (c'.length - 1) false = f x
    rw [hrun x, hlen]
    exact hcomp x
  have hmin' : c'.length = cbudget f := by
    rw [hlen]
    exact hmin
  obtain ⟨q, hq, hqr⟩ := minimal_wire_read f c' hcomp' hmin' r (by rw [hlen]; omega)
  have hnoread : readsWire r (c'.getD q (CGate.cst false)) = false := by
    rcases Nat.lt_or_ge q c.length with hql | hql
    · have hget : c'.getD q (CGate.cst false)
          = rewireGate r p ε (c.getD q (CGate.cst false)) := by
        rw [hc']
        exact takeMap_getD c (rewireGate r p ε) (r + 1) q (by omega) hql
      rw [hget]
      exact readsWire_rewire r p (by omega) ε _
    · rw [List.getD_eq_default _ _ (by rw [hlen]; omega)]
      rfl
  rw [hqr] at hnoread
  simp at hnoread

/-! ### The door closes: in minimal circuits, tracked mediators are thick -/

/-- **SAT sign bits (proved)**: in a minimal circuit, every mediated sign bit's mediator wire is thick —
the passthrough branch is impossible. -/
theorem sat3_sign_mediator_thick (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (p r : ℕ) (hmed : MediatedAt c (sat3SignBit N cIdx) p r) :
    ∃ q ∈ coneOf c r, ∃ i' : Fin N, i' ≠ sat3SignBit N cIdx ∧
      c.getD q (CGate.cst false) = CGate.var i' := by
  rcases sat3_sign_thick_or_duplicated N hv hm3 hk cIdx c hcomp p r hmed with
    h | ⟨ε, hlt, hdup⟩
  · exact h
  · exact (no_duplicate_wire (sat3Family N) c hcomp hmin p r hlt
      hmed.2.2.2.1 ε hdup).elim

/-- **SAT selectors (proved)**: in a minimal circuit, every tracked slot-2 selector's mediator wire is
thick — the passthrough branch is impossible. -/
theorem sat3_selector_mediator_thick (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) (hjv : sat3M N - 2 ≤ j.val)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (hmin : c.length = cbudget (sat3Family N))
    (p r : ℕ) (hmed : MediatedAt c (sat3S2Sel N cIdx j) p r) :
    ∃ q ∈ coneOf c r, ∃ i' : Fin N, i' ≠ sat3S2Sel N cIdx j ∧
      c.getD q (CGate.cst false) = CGate.var i' := by
  rcases sat3_selector_thick_or_duplicated N hv hm3 hk cIdx j hjv c hcomp p r hmed with
    h | ⟨ε, hlt, hdup⟩
  · exact h
  · exact (no_duplicate_wire (sat3Family N) c hcomp hmin p r hlt
      hmed.2.2.2.1 ε hdup).elim

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.no_duplicate_wire
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_mediator_thick
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_mediator_thick
