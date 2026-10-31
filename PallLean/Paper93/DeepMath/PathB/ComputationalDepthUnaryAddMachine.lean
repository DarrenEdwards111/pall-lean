import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATVerifierSpec

/-!
# The multiplication sub-arc, brick 1: the unary adder

**Decision executed**: the coordinate convention stays (E6-codec compatibility), so the
CNF evaluator must compute `v = 3·Nat.pair t p + tag` from unary coordinate blocks —
quadratic unary arithmetic on tape.  Sub-arc roadmap: **add** (this brick) → copy (the
marking shuttle) → mul (iterated copy-add) → square/compare → pair-assembly
(`3·pair(t,p)+tag`) → the evaluator (discharging `SatVerifierInP`).

**The adder.**  On `1^a 0 1^b 0 rest`, produce `1^(a+b) 0 0 rest` in one rightward scan
with a single backstep: overwrite the first separator with `1` (merging the blocks into
`1^(a+b+1)`), walk to the merged block's end, step back once and overwrite the last `1`
with `0`.  Three phases, six states, time `≤ n + 3` on *every* input:

* `unaryAdd` — the total spec, written exactly as the machine acts: flip the first
  `false` to `true`, then flip the cell before the (new) first `false` back;
* `unaryAdd_encode` — on well-formed blocks it is addition:
  `1^a 0 1^b 0 rest ↦ 1^(a+b) 0 0 rest`;
* `walkS0`/`walkS1` — `getD`-conditioned walk lemmas (no list-shape juggling, so
  garbage totality is native);
* `addMachine_transduces` — the machine transduces `unaryAdd` within clock `n + 4`;
  `unaryAdd_polyComputable`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UnaryAddMachine

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinLookupMachine (firstFalse false_exists)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.DIndexMachine (getD_at getD_beyond writeAt_boundary
  run_one run_two)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-! ## `writeAt` read lemmas -/

theorem getD_writeAt_self (x : List Bool) (p : ℕ) (w : Bool) :
    (writeAt x p w).getD p false = w := by
  unfold writeAt
  have hlen : p < (x ++ List.replicate (p + 1 - x.length) false).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simpa using hlen), List.getElem_set_self]
  rfl

theorem getD_writeAt_lt (x : List Bool) (p i : ℕ) (w : Bool) (h : i < p) :
    (writeAt x p w).getD i false = x.getD i false := by
  unfold writeAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega)]
  rcases Nat.lt_or_ge i x.length with hi | hi
  · rw [List.getElem?_append_left hi, List.getD_eq_getElem?_getD]
  · rw [List.getElem?_append_right hi, List.getElem?_replicate]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    split
    · rfl
    · rfl

/-- The first `false` is within the padded range. -/
theorem firstFalse_le_length (x : List Bool) : firstFalse x ≤ x.length :=
  Nat.find_le (getD_beyond x x.length (Nat.le_refl _))

/-! ## The spec -/

/-- The adder's total spec, exactly as the machine acts: flip the first `false` to
`true` (merging the two blocks), then flip the cell before the new first `false` back
to `false` (trimming the merged block by one). -/
noncomputable def unaryAdd (x : List Bool) : List Bool :=
  writeAt (writeAt x (firstFalse x) true)
    (firstFalse (writeAt x (firstFalse x) true) - 1) false

/-- `firstFalse` on a well-formed block. -/
theorem firstFalse_block (k : ℕ) (z : List Bool) :
    firstFalse (List.replicate k true ++ false :: z) = k := by
  have hspec : (List.replicate k true ++ false :: z).getD k false = false := by
    have := getD_at (List.replicate k true) false z
    rwa [List.length_replicate] at this
  have hmin : ∀ i < k, (List.replicate k true ++ false :: z).getD i false = true := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hi),
      List.getElem?_replicate]
    simp [hi]
  refine le_antisymm (Nat.find_le hspec) ?_
  show k ≤ Nat.find (false_exists (List.replicate k true ++ false :: z))
  rw [Nat.le_find_iff]
  intro m hm hfalse
  rw [hmin m hm] at hfalse
  simp at hfalse

/-- **On well-formed blocks the spec is addition**: `1^a 0 1^b 0 rest ↦ 1^(a+b) 0 0 rest`. -/
theorem unaryAdd_encode (a b : ℕ) (rest : List Bool) :
    unaryAdd (encodeNat a ++ encodeNat b ++ rest)
      = encodeNat (a + b) ++ false :: rest := by
  have hx : encodeNat a ++ encodeNat b ++ rest
      = List.replicate a true ++ false :: (List.replicate b true ++ false :: rest) := by
    simp [encodeNat]
  have hf1 : firstFalse (encodeNat a ++ encodeNat b ++ rest) = a := by
    rw [hx, firstFalse_block]
  have hw1 : writeAt (encodeNat a ++ encodeNat b ++ rest) a true
      = List.replicate (a + b + 1) true ++ false :: rest := by
    have hb := writeAt_boundary (List.replicate a true) false true
      (List.replicate b true ++ false :: rest)
    rw [List.length_replicate] at hb
    rw [hx, hb, show a + b + 1 = a + (b + 1) from by omega, List.replicate_add,
      List.replicate_succ]
    simp
  have hf2 : firstFalse (List.replicate (a + b + 1) true ++ false :: rest) = a + b + 1 :=
    firstFalse_block _ _
  unfold unaryAdd
  rw [hf1, hw1, hf2]
  have hsplit : List.replicate (a + b + 1) true ++ false :: rest
      = List.replicate (a + b) true ++ true :: (false :: rest) := by
    rw [show a + b + 1 = a + b + 1 from rfl, List.replicate_succ']
    simp
  have hb2 := writeAt_boundary (List.replicate (a + b) true) true false (false :: rest)
  rw [List.length_replicate] at hb2
  rw [show a + b + 1 - 1 = a + b from by omega, hsplit, hb2]
  simp [encodeNat]

/-! ## The machine -/

/-- Phases: `0` scan the first block, `1` scan the merged block, `2` trim, `3` halt. -/
def addMachine : Machine where
  State := Fin 4 × Bool
  fin := inferInstance
  dec := inferInstance
  start := (0, false)
  halt := fun s => decide (s.1 = 3)
  δ := fun s b =>
    if s.1 = 0 then
      (if b then ((0, s.2), none, 1) else ((1, s.2), some true, 1))
    else if s.1 = 1 then
      (if b then ((1, s.2), none, 1) else ((2, s.2), none, 0))
    else if s.1 = 2 then ((3, s.2), some false, 2)
    else ((3, s.2), none, 2)
  accept := fun s => s.2

theorem step_scan0_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step addMachine ⟨(0, ans), p, x⟩ = ⟨(0, ans), p + 1, x⟩ := by
  simp only [step, addMachine, h, moveHead]; rfl

theorem step_scan0_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step addMachine ⟨(0, ans), p, x⟩ = ⟨(1, ans), p + 1, writeAt x p true⟩ := by
  simp only [step, addMachine, h, moveHead]; rfl

theorem step_scan1_T {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = true) :
    step addMachine ⟨(1, ans), p, x⟩ = ⟨(1, ans), p + 1, x⟩ := by
  simp only [step, addMachine, h, moveHead]; rfl

theorem step_scan1_F {ans : Bool} {p : ℕ} {x : List Bool} (h : x.getD p false = false) :
    step addMachine ⟨(1, ans), p, x⟩ = ⟨(2, ans), p - 1, x⟩ := by
  simp only [step, addMachine, h, moveHead]; rfl

theorem step_trim {ans : Bool} {p : ℕ} {x : List Bool} :
    step addMachine ⟨(2, ans), p, x⟩ = ⟨(3, ans), p, writeAt x p false⟩ := by
  simp only [step, addMachine, moveHead]; rfl

/-! ## `getD`-conditioned walks -/

theorem walkS0 : ∀ (j : ℕ) (x : List Bool) (p : ℕ) (ans : Bool),
    (∀ i < j, x.getD (p + i) false = true) →
    run addMachine j ⟨(0, ans), p, x⟩ = ⟨(0, ans), p + j, x⟩
  | 0, x, p, ans, _ => rfl
  | j + 1, x, p, ans, h => by
    rw [show j + 1 = 1 + j from by omega, run_add, run_one,
      step_scan0_T (by simpa using h 0 (by omega)),
      walkS0 j x (p + 1) ans (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show p + (i + 1) = p + 1 + i from by omega] at this)]
    rw [show p + (1 + j) = p + 1 + j from by omega]

theorem walkS1 : ∀ (j : ℕ) (x : List Bool) (p : ℕ) (ans : Bool),
    (∀ i < j, x.getD (p + i) false = true) →
    run addMachine j ⟨(1, ans), p, x⟩ = ⟨(1, ans), p + j, x⟩
  | 0, x, p, ans, _ => rfl
  | j + 1, x, p, ans, h => by
    rw [show j + 1 = 1 + j from by omega, run_add, run_one,
      step_scan1_T (by simpa using h 0 (by omega)),
      walkS1 j x (p + 1) ans (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show p + (i + 1) = p + 1 + i from by omega] at this)]
    rw [show p + (1 + j) = p + 1 + j from by omega]

/-! ## The full run and the transduction -/

/-- **Total halting with the spec's output**, on every input, within `|x| + 3` steps. -/
theorem addMachine_halts (x : List Bool) :
    ∃ t ≤ x.length + 3, ∃ p,
      run addMachine t (init addMachine x) = ⟨(3, false), p, unaryAdd x⟩ := by
  set k₁ := firstFalse x with hk₁
  set x₁ := writeAt x k₁ true with hx₁
  set k₂ := firstFalse x₁ with hk₂
  have hk₁spec : x.getD k₁ false = false := Nat.find_spec (false_exists x)
  have hk₁min : ∀ i < k₁, x.getD i false = true := by
    intro i hi
    have := Nat.find_min (false_exists x) hi
    simpa using this
  have hk₂spec : x₁.getD k₂ false = false := Nat.find_spec (false_exists x₁)
  have hk₂min : ∀ i < k₂, x₁.getD i false = true := by
    intro i hi
    have := Nat.find_min (false_exists x₁) hi
    simpa using this
  have hk₁k₂ : k₁ + 1 ≤ k₂ := by
    rw [hk₂]
    show k₁ + 1 ≤ Nat.find (false_exists x₁)
    rw [Nat.le_find_iff]
    intro m hm hfalse
    rcases Nat.lt_or_ge m k₁ with h | h
    · rw [hx₁, getD_writeAt_lt x k₁ m true h, hk₁min m h] at hfalse
      simp at hfalse
    · have hmk : m = k₁ := by omega
      rw [hmk, hx₁, getD_writeAt_self] at hfalse
      simp at hfalse
  have hwalk0 := walkS0 k₁ x 0 false (fun i hi => by
    have := hk₁min i hi
    simpa using this)
  have hstep1 : step addMachine ⟨(0, false), k₁, x⟩ = ⟨(1, false), k₁ + 1, x₁⟩ := by
    rw [step_scan0_F hk₁spec, hx₁]
  have hwalk1 := walkS1 (k₂ - (k₁ + 1)) x₁ (k₁ + 1) false
    (fun i hi => hk₂min _ (by omega))
  have hstep2 : step addMachine ⟨(1, false), k₂, x₁⟩ = ⟨(2, false), k₂ - 1, x₁⟩ :=
    step_scan1_F hk₂spec
  have hlen1 : k₁ ≤ x.length := by
    rw [hk₁]
    exact firstFalse_le_length x
  have hlen2 : k₂ ≤ x.length + 1 := by
    have h1 : k₂ ≤ x₁.length := by
      rw [hk₂]
      exact firstFalse_le_length x₁
    have h2 : x₁.length = max x.length (k₁ + 1) := by
      rw [hx₁]
      exact writeAt_length x k₁ true
    omega
  refine ⟨k₁ + 1 + (k₂ - (k₁ + 1)) + 1 + 1, by omega, k₂ - 1, ?_⟩
  rw [show unaryAdd x = writeAt x₁ (k₂ - 1) false from by
    unfold unaryAdd
    rw [← hk₁, ← hx₁, ← hk₂]]
  rw [show init addMachine x = (⟨(0, false), 0, x⟩ : Cfg addMachine) from rfl,
    run_add, run_add, run_add, run_add, run_one, run_one, run_one, hwalk0]
  simp only [Nat.zero_add]
  rw [hstep1, hwalk1, show k₁ + 1 + (k₂ - (k₁ + 1)) = k₂ from by omega, hstep2,
    step_trim]

/-! ## Transduction and P-membership -/

/-- **The adder transduces `unaryAdd`** within clock `n + 4`, on all inputs. -/
theorem addMachine_transduces : Transduces addMachine unaryAdd (fun n => n + 4) := by
  intro x
  obtain ⟨t, ht, p, hrun⟩ := addMachine_halts x
  have hhalt : addMachine.halt (run addMachine t (init addMachine x)).st = true := by
    rw [hrun]
    rfl
  have hstable : run addMachine (x.length + 4) (init addMachine x)
      = run addMachine t (init addMachine x) :=
    run_stable addMachine x (by omega) hhalt
  constructor
  · show addMachine.halt (run addMachine (x.length + 4) (init addMachine x)).st = true
    rw [hstable, hrun]
    rfl
  · show transOut addMachine x (x.length + 4) = unaryAdd x
    unfold transOut
    rw [hstable, hrun]

/-- Unary addition is polynomial-time computable. -/
theorem unaryAdd_polyComputable : PolyComputable unaryAdd :=
  ⟨addMachine, fun n => n + 4, ⟨5, 1, fun n => by
    show n + 4 ≤ 5 * (n + 1) ^ 1
    have : (n + 1) ^ 1 = n + 1 := pow_one _
    omega⟩, addMachine_transduces⟩

end PallLean.Paper93.DeepMath.PathB.UnaryAddMachine
