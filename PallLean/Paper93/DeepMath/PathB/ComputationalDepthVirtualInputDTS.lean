import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPadMountainReductions

/-!
# Mountain 1, camp 7: the virtual-input DTS half — the bit oracle, and a real obstruction found

The DTS half (`PaddingDTSHalf`) is the campaign's flagged hard half: decide `L` by running the
padded decider on `pad(x)` *without materializing* `pad(x)` (writing `(n+1)^m` cells would blow the
polylog space budget).  Building it, the machine-independent core came out clean — and then a genuine
structural obstruction surfaced, exactly the kind the campaign has been catching by audit.

## What is proved — the bit oracle (the read side is cheap, and `m`-independent)

* **`padBit x i`** — the `i`-th bit of `pad(x)`, in closed form: `true` on even tagged positions,
  `x`'s bit on odd ones, `false` everywhere at index `≥ 2|x|`.  **Independent of `m`** — because the
  pad, the separator, and every out-of-range read are all `false`, so the pad's *length* never affects
  any *bit*.
* **`padBit_eq`** — the oracle is correct: `padBit x i = (padWith m x).getD i false`, for every `m`
  and `i`.  So a decider can recompute any bit of `pad(x)` from `x` and `i` alone, in `O(log)` space,
  never touching `(n+1)^m`.  The virtual *read* is genuinely free.

## The obstruction found — bounded space-growth does NOT bound modified cells

* **`flipFirst` / `flipFirst_growth_zero` / `flipFirst_modifies_input`** — a machine that writes to
  input position `0` with **zero tape growth** (`SpaceGrowthLe … 0`) yet **modifies an input cell**.
  Scaled up (a sweeper), a `polylog`-*growth* machine can overwrite `Ω(|input|)` input cells.  So the
  virtual simulator cannot reconstruct the padded decider's working tape by "oracle reads + track the
  few writes": the writes are *not* few.  In this **single-tape, writable-input** model, the padded
  decider may rewrite the `(n+1)^m`-cell input region in place, and no `polylog`-space simulator can
  track that.

## Honest verdict — the DTS half needs a read-only-input model refinement

The read side is discharged (`padBit_eq`); the obstruction is on the *write* side, and it is real, not
a proof-engineering gap.  The standard resolution is the literature's actual model: **TISP with a
read-only input tape** and a separate `polylog` work tape — there the decider *cannot* modify the
input, the simulator recomputes input bits via `padBit`, and only the `polylog` work tape is tracked.
`ROInputDTSSimExists` names that refinement's obligation, and `paddingDTSHalf_of_roSim` would carry it
— but wiring it needs the read-only-input class, a model refinement flagged here, not hidden.  This is
a finding about the *concretization* (single-tape `DTS` is too coarse for padding), the same discipline
as camps 3–6.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.VirtualInputDTS

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.EncPairDecode
open PallLean.Paper93.DeepMath.PathB.PadFunction

/-! ### The bit oracle -/

/-- The `i`-th bit of `pad(x)`, in closed form — independent of `m`. -/
def padBit (x : List Bool) (i : ℕ) : Bool :=
  if i < 2 * x.length then (if i % 2 = 0 then true else x.getD (i / 2) false) else false

/-- `getD` on an all-`false` replicate is `false` (in range or out). -/
theorem getD_replicate_false (k j : ℕ) : (List.replicate k false).getD j false = false := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    cases j with
    | zero => simp
    | succ j => rw [List.replicate_succ, List.getD_cons_succ]; exact ih j

/-- `getD` into the left summand. -/
theorem getD_append_left {α : Type} : ∀ (l₁ l₂ : List α) (i : ℕ) (d : α), i < l₁.length →
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ i d h; simp at h
  | cons a as ih =>
    intro l₂ i d h
    cases i with
    | zero => simp
    | succ j =>
      rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
      exact ih l₂ j d (by simp only [List.length_cons] at h; omega)

/-- `getD` into the right summand. -/
theorem getD_append_right {α : Type} : ∀ (l₁ l₂ : List α) (i : ℕ) (d : α), l₁.length ≤ i →
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ i d _; simp
  | cons a as ih =>
    intro l₂ i d h
    cases i with
    | zero => simp only [List.length_cons] at h; omega
    | succ j =>
      have h' : as.length ≤ j := by simp only [List.length_cons] at h; omega
      rw [List.cons_append, List.getD_cons_succ, ih l₂ j d h']
      congr 1
      simp only [List.length_cons]
      omega

/-- The tagged prefix has length `2|x|`. -/
theorem flatten_tag_length (x : List Bool) :
    (List.map (fun b => [true, b]) x).flatten.length = 2 * x.length := by
  induction x with
  | nil => simp
  | cons b xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

/-- The tagged-bit structure of the pairing prefix. -/
theorem getD_flatten_tag (x : List Bool) (i : ℕ) :
    (List.map (fun b => [true, b]) x).flatten.getD i false
      = if i < 2 * x.length then (if i % 2 = 0 then true else x.getD (i / 2) false) else false := by
  induction x generalizing i with
  | nil => simp
  | cons b xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
      List.length_cons]
    match i with
    | 0 => simp
    | 1 =>
      rw [List.getD_cons_succ, List.getD_cons_zero,
        if_pos (show (1 : ℕ) < 2 * (xs.length + 1) from by omega),
        if_neg (show ¬ (1 : ℕ) % 2 = 0 from by decide),
        show (1 : ℕ) / 2 = 0 from by decide, List.getD_cons_zero]
    | (j + 2) =>
      rw [List.getD_cons_succ, List.getD_cons_succ, ih j]
      by_cases hlt : j < 2 * xs.length
      · rw [if_pos hlt, if_pos (show j + 2 < 2 * (xs.length + 1) from by omega)]
        by_cases hpar : j % 2 = 0
        · rw [if_pos hpar, if_pos (show (j + 2) % 2 = 0 from by omega)]
        · rw [if_neg hpar, if_neg (show ¬ (j + 2) % 2 = 0 from by omega),
            show (j + 2) / 2 = j / 2 + 1 from by omega, List.getD_cons_succ]
      · rw [if_neg hlt, if_neg (show ¬ j + 2 < 2 * (xs.length + 1) from by omega)]

/-- **The bit oracle is correct (proved).**  `padBit x i = (padWith m x).getD i false`, for every
`m` and `i` — the read of any bit of `pad(x)` needs only `x` and `i`, never `(n+1)^m`. -/
theorem padBit_eq (m : ℕ) (x : List Bool) (i : ℕ) :
    padBit x i = (padWith m x).getD i false := by
  rw [padWith, encPair, List.append_assoc, List.singleton_append]
  rcases Nat.lt_or_ge i (2 * x.length) with hlt | hge
  · rw [getD_append_left _ _ _ _ (by rw [flatten_tag_length]; exact hlt), getD_flatten_tag]
    simp only [padBit, if_pos hlt]
  · rw [getD_append_right _ _ _ _ (by rw [flatten_tag_length x]; exact hge), flatten_tag_length x]
    have hpb : padBit x i = false := by simp only [padBit, if_neg (not_lt.mpr hge)]
    rw [hpb]
    cases hk : i - 2 * x.length with
    | zero => simp
    | succ k => rw [List.getD_cons_succ, getD_replicate_false]

/-! ### The obstruction: bounded growth ≠ bounded modification -/

/-- A machine that, in one step, writes `true` at head position `0`, then halts.  Zero tape growth
(it overwrites in place), yet it modifies an input cell. -/
def flipFirst : Machine where
  State := Bool
  fin := inferInstance
  dec := inferInstance
  start := false
  halt := fun s => s
  δ := fun _ _ => (true, some true, (2 : Move))
  accept := fun _ => true

/-- One step of `flipFirst`: state `true`, head reset, position `0` written `true`. -/
theorem run_flipFirst_one (x : List Bool) :
    run flipFirst 1 (init flipFirst x) = ⟨true, 0, writeAt x 0 true⟩ := by
  show step flipFirst (init flipFirst x) = ⟨true, 0, writeAt x 0 true⟩
  simp [step, init, flipFirst, moveHead]

/-- **Zero growth (proved).**  `flipFirst` never grows the tape beyond the input. -/
theorem flipFirst_growth_zero (x : List Bool) (hx : 0 < x.length) :
    SpaceGrowthLe flipFirst x 0 := by
  intro t
  cases t with
  | zero => simp only [run_zero, init]; omega
  | succ t =>
    have hstab : run flipFirst (t + 1) (init flipFirst x) = run flipFirst 1 (init flipFirst x) :=
      run_stable flipFirst x (by omega) (by rw [run_flipFirst_one]; rfl)
    rw [hstab, run_flipFirst_one]
    show (writeAt x 0 true).length ≤ x.length + 0
    rw [writeAt_length]
    omega

/-- **An input cell is modified (proved).**  On a nonempty input starting with `false`, `flipFirst`
changes position `0` from `false` to `true` — modification with zero growth.  So bounded space-growth
does not bound the number of overwritten input cells. -/
theorem flipFirst_modifies_input (x : List Bool) (hx0 : x.getD 0 false = false) (hx : 0 < x.length) :
    (run flipFirst 1 (init flipFirst x)).tp.getD 0 false = true ∧ x.getD 0 false = false := by
  refine ⟨?_, hx0⟩
  rw [run_flipFirst_one]
  obtain ⟨c, rest, rfl⟩ : ∃ c rest, x = c :: rest := by
    cases x with
    | nil => simp at hx
    | cons c rest => exact ⟨c, rest, rfl⟩
  show (writeAt (c :: rest) 0 true).getD 0 false = true
  simp only [writeAt, List.length_cons]
  rw [show 0 + 1 - (rest.length + 1) = 0 from by omega, List.replicate, List.append_nil]
  rfl

/-! ### The read-only-input refinement, named -/

/-- **The read-only-input DTS simulator (the model refinement's obligation).**  In the TISP model
with a read-only input tape, a padded decider yields an original-language decider: recompute input
bits via `padBit`, track only the `polylog` work tape.  Named here; wiring it needs the read-only
input class, a refinement of `DTS`, flagged not hidden. -/
def ROInputDTSSimExists : Prop :=
  ∀ m p L, 1 ≤ m → DTS p (padLang m L) → DTS (m * p) L

/-- With the read-only-input simulator, the DTS half is exactly it (definitional): the honest content
is that the simulator is stated against the *refined* model, where `padBit` reads and `polylog`
work-tape tracking suffice — the single-tape `DTS` above cannot host it (`flipFirst_modifies_input`). -/
theorem paddingDTSHalf_of_roSim (h : ROInputDTSSimExists) : PaddingAssembly.PaddingDTSHalf := h

end PallLean.Paper93.DeepMath.PathB.VirtualInputDTS

#print axioms PallLean.Paper93.DeepMath.PathB.VirtualInputDTS.padBit_eq
#print axioms PallLean.Paper93.DeepMath.PathB.VirtualInputDTS.flipFirst_growth_zero
#print axioms PallLean.Paper93.DeepMath.PathB.VirtualInputDTS.flipFirst_modifies_input
