import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameDeadGateElimination

/-!
# N-Frame: semantic obligation — the cube objects, and the thick-or-passthrough dichotomy

The mountain face, attacked at its provable core.  Steps 1–2 of the semantic campaign are definitions fed
by the two context lifts; step 3 — "a cheap tracked wire behaves like pass-through" — is proved here in its
exact form, which is stronger than "near-passthrough" on one side and honestly weaker on the other:

  `TracksAcrossContexts` / `ObligationCube` / `SimultaneousObligations` — the semantic obstruction objects:
        a port that flips with its coordinate across an entire context family, and many such at once.
        Fed by both lifts: `sat3_sign_obligationCube`, `sat3_selector_obligationCube` — sign bits and
        slot-2 selectors now impose the *same* abstract obligation object.
  `tracked_wire_dichotomy` — **PROVED, the dichotomy**: a tracked wire either carries a **second variable
        in its cone** (thick), or it is a **global signed copy of its coordinate** — `wire r = ε ⊕ xᵢ`
        *everywhere*, not merely on the context family.  There is no third option: the only way to satisfy
        an obligation cube without reading a second variable is to be the coordinate, exactly, globally.
  `passthrough_duplicates` — **PROVED**: in the passthrough branch the circuit carries the same one bit on
        two distinct budget-priced wires (`wire r = ε ⊕ wire p` with `p < r`) — exact semantic duplication.
  `sat3_sign_thick_or_duplicated` / `sat3_selector_thick_or_duplicated` — **PROVED, the SAT headline**:
        every mediated sign bit / tracked selector makes its mediator wire either thick or a duplicate.

## Honest scope

The dichotomy converts the obligation cube into a global structural alternative, and the passthrough branch
into formal redundancy — two wires, one bit.  What remains open is exactly HAL's step 4: charging that
redundancy.  Duplicated wires are *not* yet a kill: the duplicate `r` is a live bin gate that also reads its
other child, so deleting it needs the reader-side surgery that the pass-through exception has blocked all
along.  And thick wires are not yet a cost: connectivity already pays for one merge per variable.  The
closing inequality — many thick-or-duplicated mediators overflow `2mD − 1` — is the one open statement,
unchanged.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-! ### Step 1–2: the semantic obstruction objects -/

/-- The port wire `r` flips with coordinate `i` at every context of the family `F`. -/
def TracksAcrossContexts {n : ℕ} (c : List (CGate n)) (i : Fin n) (r : ℕ)
    {ι : Type} (F : ι → (Fin n → Bool)) : Prop :=
  ∀ a : ι,
    (runFrom (Function.update (F a) i true) [] c).getD r false
      ≠ (runFrom (Function.update (F a) i false) [] c).getD r false

/-- The full obligation object: a mediation configuration whose port carries the whole context cube. -/
def ObligationCube {n : ℕ} (c : List (CGate n)) (i : Fin n) (p r : ℕ)
    {ι : Type} (F : ι → (Fin n → Bool)) : Prop :=
  MediatedAt c i p r ∧ TracksAcrossContexts c i r F

/-- Many coordinates' obligation cubes, realized simultaneously inside one shared circuit. -/
def SimultaneousObligations {n : ℕ} (c : List (CGate n)) (S : List (Fin n × ℕ × ℕ))
    {ι : Type} (F : Fin n × ℕ × ℕ → ι → (Fin n → Bool)) : Prop :=
  ∀ t ∈ S, ObligationCube c t.1 t.2.1 t.2.2 (F t)

/-- The SAT context-point family: pin context `bvec` around designated block `cIdx`, probe `u` inside. -/
def sat3CubeFamily (N : ℕ) (cIdx : Fin (sat3M N)) (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (u : Fin N → Bool) : (Fin (sat3M N - 2) → Bool) → (Fin N → Bool) :=
  fun bvec => sat3Patch N cIdx (sat3Context N cIdx hk bvec) u

/-- **Feeder (proved)**: a mediated sign bit carries a full obligation cube. -/
theorem sat3_sign_obligationCube (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (p r : ℕ) (hmed : MediatedAt c (sat3SignBit N cIdx) p r) :
    ObligationCube c (sat3SignBit N cIdx) p r
      (sat3CubeFamily N cIdx hk (sat3Probe N ⟨0, hv⟩ false)) :=
  ⟨hmed, fun bvec => sat3_sign_port_tracks_contexts N hv hm3 hk cIdx c hcomp p r hmed bvec⟩

/-- **Feeder (proved)**: a mediated slot-2 selector on an unpinned variable carries a full obligation
cube — the same abstract object as the sign bits. -/
theorem sat3_selector_obligationCube (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) (hjv : sat3M N - 2 ≤ j.val)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (p r : ℕ) (hmed : MediatedAt c (sat3S2Sel N cIdx j) p r) :
    ObligationCube c (sat3S2Sel N cIdx j) p r
      (sat3CubeFamily N cIdx hk (fun _ => false)) :=
  ⟨hmed, fun bvec =>
    sat3_selector_port_tracks_contexts N hv hm3 hk cIdx j hjv c hcomp p r hmed bvec⟩

/-! ### Step 3: the dichotomy — thick, or globally passthrough -/

/-- **THE DICHOTOMY (proved)**: a tracked wire either carries a second variable in its cone, or is a
global signed copy of its coordinate — everywhere, not merely on the context family. -/
theorem tracked_wire_dichotomy {n : ℕ} (c : List (CGate n)) (i : Fin n) (r : ℕ)
    {ι : Type} (F : ι → (Fin n → Bool)) (a₀ : ι)
    (htr : TracksAcrossContexts c i r F) :
    (∃ q ∈ coneOf c r, ∃ i' : Fin n, i' ≠ i ∧
        c.getD q (CGate.cst false) = CGate.var i') ∨
    (∃ ε : Bool, ∀ x : Fin n → Bool,
        (runFrom x [] c).getD r false = xor ε (x i)) := by
  classical
  by_cases hthick : ∃ q ∈ coneOf c r, ∃ i' : Fin n, i' ≠ i ∧
      c.getD q (CGate.cst false) = CGate.var i'
  · exact Or.inl hthick
  · push_neg at hthick
    right
    have hagree : ∀ x y : Fin n → Bool, x i = y i →
        (runFrom x [] c).getD r false = (runFrom y [] c).getD r false := by
      intro x y hxy
      exact cone_val_agree c r x y
        (fun q hq i' hvar => by
          by_cases hi : i' = i
          · rw [hi]
            exact hxy
          · exact absurd hvar (hthick q hq i' hi))
        r (cone_self c r)
    refine ⟨(runFrom (Function.update (F a₀) i false) [] c).getD r false, ?_⟩
    intro x
    have hx : (runFrom x [] c).getD r false
        = (runFrom (Function.update (F a₀) i (x i)) [] c).getD r false :=
      hagree x _ (by rw [Function.update_self])
    rw [hx]
    cases hxi : x i with
    | false =>
      cases h2 : (runFrom (Function.update (F a₀) i false) [] c).getD r false with
      | false => rfl
      | true => rfl
    | true =>
      have hflip := htr a₀
      cases h2 : (runFrom (Function.update (F a₀) i false) [] c).getD r false with
      | false =>
        cases h1 : (runFrom (Function.update (F a₀) i true) [] c).getD r false with
        | false =>
          exfalso
          rw [h1, h2] at hflip
          exact hflip rfl
        | true => rfl
      | true =>
        cases h1 : (runFrom (Function.update (F a₀) i true) [] c).getD r false with
        | false => rfl
        | true =>
          exfalso
          rw [h1, h2] at hflip
          exact hflip rfl

/-- **DUPLICATION (proved)**: in the passthrough branch, the mediator's var-gate `p` and its reader `r` are
two distinct wires carrying the same one bit, up to a fixed sign. -/
theorem passthrough_duplicates {n : ℕ} (c : List (CGate n)) (i : Fin n) (p r : ℕ)
    (hmed : MediatedAt c i p r) (ε : Bool)
    (hpt : ∀ x : Fin n → Bool, (runFrom x [] c).getD r false = xor ε (x i)) :
    p < r ∧ ∀ x : Fin n → Bool,
      (runFrom x [] c).getD r false = xor ε ((runFrom x [] c).getD p false) := by
  have hp : p < c.length := by
    rcases Nat.lt_or_ge p c.length with h | h
    · exact h
    · exfalso
      have hd : c.getD p (CGate.cst false) = CGate.cst false :=
        List.getD_eq_default _ _ h
      rw [hmed.1] at hd
      cases hd
  have hwp : ∀ x : Fin n → Bool, (runFrom x [] c).getD p false = x i := by
    intro x
    rw [output_getD_at x c p hp, hmed.1]
    rfl
  refine ⟨children_lt c r p hmed.2.2.1, ?_⟩
  intro x
  rw [hpt x, hwp x]

/-! ### The SAT headline: thick or duplicated, for both coordinate families -/

/-- **SAT sign bits (proved)**: every mediated sign bit's mediator wire is thick or a duplicate. -/
theorem sat3_sign_thick_or_duplicated (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (p r : ℕ) (hmed : MediatedAt c (sat3SignBit N cIdx) p r) :
    (∃ q ∈ coneOf c r, ∃ i' : Fin N, i' ≠ sat3SignBit N cIdx ∧
        c.getD q (CGate.cst false) = CGate.var i') ∨
    (∃ ε : Bool, p < r ∧ ∀ x : Fin N → Bool,
        (runFrom x [] c).getD r false = xor ε ((runFrom x [] c).getD p false)) := by
  rcases tracked_wire_dichotomy c (sat3SignBit N cIdx) r
      (sat3CubeFamily N cIdx hk (sat3Probe N ⟨0, hv⟩ false)) (fun _ => false)
      (sat3_sign_obligationCube N hv hm3 hk cIdx c hcomp p r hmed).2 with h | ⟨ε, hpt⟩
  · exact Or.inl h
  · obtain ⟨hlt, hdup⟩ := passthrough_duplicates c _ p r hmed ε hpt
    exact Or.inr ⟨ε, hlt, hdup⟩

/-- **SAT selectors (proved)**: every mediated slot-2 selector on an unpinned variable has a mediator wire
that is thick or a duplicate. -/
theorem sat3_selector_thick_or_duplicated (N : ℕ) (hv : 1 ≤ sat3V N) (hm3 : 3 ≤ sat3M N)
    (hk : (sat3M N - 2) + 1 ≤ sat3M N)
    (cIdx : Fin (sat3M N)) (j : Fin (sat3V N)) (hjv : sat3M N - 2 ≤ j.val)
    (c : List (CGate N)) (hcomp : computes c (sat3Family N))
    (p r : ℕ) (hmed : MediatedAt c (sat3S2Sel N cIdx j) p r) :
    (∃ q ∈ coneOf c r, ∃ i' : Fin N, i' ≠ sat3S2Sel N cIdx j ∧
        c.getD q (CGate.cst false) = CGate.var i') ∨
    (∃ ε : Bool, p < r ∧ ∀ x : Fin N → Bool,
        (runFrom x [] c).getD r false = xor ε ((runFrom x [] c).getD p false)) := by
  rcases tracked_wire_dichotomy c (sat3S2Sel N cIdx j) r
      (sat3CubeFamily N cIdx hk (fun _ => false)) (fun _ => false)
      (sat3_selector_obligationCube N hv hm3 hk cIdx j hjv c hcomp p r hmed).2 with h | ⟨ε, hpt⟩
  · exact Or.inl h
  · obtain ⟨hlt, hdup⟩ := passthrough_duplicates c _ p r hmed ε hpt
    exact Or.inr ⟨ε, hlt, hdup⟩

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.tracked_wire_dichotomy
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.passthrough_duplicates
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_sign_thick_or_duplicated
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.sat3_selector_thick_or_duplicated
