import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedCircuitCompiler

/-!
# Step (4): information bounds and the read-once cap (audit-corrected scope)

The information side of the step-(4) analysis (`SCOPE_STEP4_DYNAMIC_INVARIANT.md`), machine-checked — with the
claims stated at their **audited** strength:

* `instantaneous_info_le_n` — the direct universal cap: at any fixed time the state is a function of an `n`-bit
  input, so the reachable-state count is `≤ 2^n` for **every** program, no normalization needed.
* `stateImage_card_le` — **info ≤ reads** (the sharper trace induction): reachable states `≤ 2^{#input gates}`.
  Logic gates cannot increase the state count; an input gate at most doubles it.  This bounds *cumulative
  input-driven information growth* by the read count (`≤ cost`) — the honest bound; for a single program it does
  NOT cap at `n` (a program may forget and re-read; `qfProg A` re-reads quadratically).
* `readOnce` / `info_cap` — read-once normalization: every program has a semantics-preserving equivalent with
  exactly `n` reads (`readOnce_inputCount`) and cost `≤ n + 2·cost`, whose reachable-state count stays `≤ 2^n` at
  every prefix.  Hence the **min over programs computing `f`** of any invariant dominated by prefix-state-counts
  is `≤ n` on every computable function.

## What this does and does NOT close (per audit)

CLOSED: instantaneous-state information (universally `≤ n`), and min-over-programs input-driven growth (`≤ n` via
`readOnce`) — these cannot yield superpolynomial lower bounds.  NOT closed: cut-communication / congestion /
layout-movement measures, which charge logic across cuts and are bounded by neither argument — each such candidate
needs its own collapse-or-survive test (against `qfProg A` and the three proved collapses:
`canonical_schemeResource_eq_clock`, `ChargedLengthObserverCollapse`, `ChargedDynamicQueryCollapse` — which refute
their specific measures, not all logic-sensitive invariants).  Soundness gives a ONE-WAY reduction only: invariant
hardness ⟹ cost hardness (the converse fails — `Inv ≡ 0`); proving the step-(6) hardness side is therefore
at-least-separation-hard.  A **no-go plus honest bounds**, not a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedInfoCap

open PallLean.Paper93.DeepMath.PathB.ChargedGate
open PallLean.Paper93.DeepMath.PathB.ChargedCircuit

variable {n w : ℕ}

/-- The number of input gates (reads) in a gate sequence. -/
def inputCount (gs : List (Gate n w)) : ℕ := (gs.filterMap Gate.readsInput).length

/-- The set of wire-states reachable at the end of `gs` (over all inputs), from a fixed start. -/
noncomputable def stateImage (gs : List (Gate n w)) (s : Fin w → Bool) : Finset (Fin w → Bool) := by
  classical
  exact Finset.univ.image (fun x : Fin n → Bool => runGates x gs s)

/-- **The direct universal cap** (instantaneous information): at any time the state is a function of the
`n`-bit input, so at most `2^n` states are reachable — for every program, with no normalization. -/
theorem instantaneous_info_le_n (s : Fin w → Bool) (gs : List (Gate n w)) :
    (stateImage gs s).card ≤ 2 ^ n := by
  classical
  calc (stateImage gs s).card
      ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_image_le
    _ = 2 ^ n := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **Info ≤ reads.**  The reachable-state count is at most `2^{#input gates}`. -/
theorem stateImage_card_le (s : Fin w → Bool) (gs : List (Gate n w)) :
    (stateImage gs s).card ≤ 2 ^ inputCount gs := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    have h1 : stateImage ([] : List (Gate n w)) s = {s} := by
      unfold stateImage
      classical
      exact Finset.image_const Finset.univ_nonempty s
    rw [h1, Finset.card_singleton]
    exact Nat.one_le_two_pow
  | append_singleton gs g ih =>
    have hrun : ∀ x : Fin n → Bool, runGates x (gs ++ [g]) s = step x (runGates x gs s) g := by
      intro x
      rw [runGates_append']
      rfl
    cases g with
    | input i t =>
      have hsub : stateImage (gs ++ [Gate.input i t]) s
          ⊆ Finset.image (fun p : (Fin w → Bool) × Bool => Function.update p.1 t p.2)
              ((stateImage gs s) ×ˢ (Finset.univ : Finset Bool)) := by
        intro y hy
        unfold stateImage at hy
        classical
        rw [Finset.mem_image] at hy
        obtain ⟨x, _, hx⟩ := hy
        rw [hrun x] at hx
        refine Finset.mem_image.mpr ⟨(runGates x gs s, x i), ?_, hx⟩
        rw [Finset.mem_product]
        exact ⟨by unfold stateImage; exact Finset.mem_image_of_mem _ (Finset.mem_univ x),
          Finset.mem_univ _⟩
      have hcount : inputCount (gs ++ [Gate.input i t]) = inputCount gs + 1 := by
        unfold inputCount
        rw [List.filterMap_append, List.length_append]
        rfl
      calc (stateImage (gs ++ [Gate.input i t]) s).card
          ≤ (Finset.image (fun p : (Fin w → Bool) × Bool => Function.update p.1 t p.2)
              ((stateImage gs s) ×ˢ (Finset.univ : Finset Bool))).card := Finset.card_le_card hsub
        _ ≤ ((stateImage gs s) ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
        _ = (stateImage gs s).card * 2 := by
            rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
        _ ≤ 2 ^ inputCount gs * 2 := Nat.mul_le_mul_right 2 ih
        _ = 2 ^ inputCount (gs ++ [Gate.input i t]) := by rw [hcount, pow_succ]
    | notg a t =>
      have hsub : stateImage (gs ++ [Gate.notg a t]) s
          ⊆ (stateImage gs s).image
              (fun s' => step (fun _ : Fin n => false) s' (Gate.notg a t (n := n))) := by
        intro y hy
        unfold stateImage at hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, _, hx⟩ := hy
        rw [hrun x, step_congr x (fun _ : Fin n => false) _ _ (fun i hi => by cases hi)] at hx
        exact Finset.mem_image.mpr ⟨runGates x gs s,
          by unfold stateImage; exact Finset.mem_image_of_mem _ (Finset.mem_univ x), hx⟩
      have hcount : inputCount (gs ++ [Gate.notg a t]) = inputCount gs := by
        unfold inputCount
        rw [List.filterMap_append, List.length_append]
        rfl
      calc (stateImage (gs ++ [Gate.notg a t]) s).card
          ≤ ((stateImage gs s).image _).card := Finset.card_le_card hsub
        _ ≤ (stateImage gs s).card := Finset.card_image_le
        _ ≤ 2 ^ inputCount gs := ih
        _ = 2 ^ inputCount (gs ++ [Gate.notg a t]) := by rw [hcount]
    | andg a b t =>
      have hsub : stateImage (gs ++ [Gate.andg a b t]) s
          ⊆ (stateImage gs s).image
              (fun s' => step (fun _ : Fin n => false) s' (Gate.andg a b t (n := n))) := by
        intro y hy
        unfold stateImage at hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, _, hx⟩ := hy
        rw [hrun x, step_congr x (fun _ : Fin n => false) _ _ (fun i hi => by cases hi)] at hx
        exact Finset.mem_image.mpr ⟨runGates x gs s,
          by unfold stateImage; exact Finset.mem_image_of_mem _ (Finset.mem_univ x), hx⟩
      have hcount : inputCount (gs ++ [Gate.andg a b t]) = inputCount gs := by
        unfold inputCount
        rw [List.filterMap_append, List.length_append]
        rfl
      calc (stateImage (gs ++ [Gate.andg a b t]) s).card
          ≤ ((stateImage gs s).image _).card := Finset.card_le_card hsub
        _ ≤ (stateImage gs s).card := Finset.card_image_le
        _ ≤ 2 ^ inputCount gs := ih
        _ = 2 ^ inputCount (gs ++ [Gate.andg a b t]) := by rw [hcount]
    | xorg a b t =>
      have hsub : stateImage (gs ++ [Gate.xorg a b t]) s
          ⊆ (stateImage gs s).image
              (fun s' => step (fun _ : Fin n => false) s' (Gate.xorg a b t (n := n))) := by
        intro y hy
        unfold stateImage at hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, _, hx⟩ := hy
        rw [hrun x, step_congr x (fun _ : Fin n => false) _ _ (fun i hi => by cases hi)] at hx
        exact Finset.mem_image.mpr ⟨runGates x gs s,
          by unfold stateImage; exact Finset.mem_image_of_mem _ (Finset.mem_univ x), hx⟩
      have hcount : inputCount (gs ++ [Gate.xorg a b t]) = inputCount gs := by
        unfold inputCount
        rw [List.filterMap_append, List.length_append]
        rfl
      calc (stateImage (gs ++ [Gate.xorg a b t]) s).card
          ≤ ((stateImage gs s).image _).card := Finset.card_le_card hsub
        _ ≤ (stateImage gs s).card := Finset.card_image_le
        _ ≤ 2 ^ inputCount gs := ih
        _ = 2 ^ inputCount (gs ++ [Gate.xorg a b t]) := by rw [hcount]

/-! ## Read-once normalization -/

/-- The low wire holding input `i`. -/
def lowWire (w : ℕ) (i : Fin n) : Fin (n + w) := ⟨i.val, by omega⟩

/-- The high wire simulating original wire `j`. -/
def highWire (j : Fin w) : Fin (n + w) := ⟨n + j.val, by omega⟩

/-- Load each input into its dedicated low wire. -/
def loadPrefix (n w : ℕ) : List (Gate n (n + w)) :=
  (List.finRange n).map (fun i => Gate.input i (lowWire w i))

/-- Replace each gate by its high-wire version; an `input` becomes a two-`NOT` copy from the low wire. -/
def shiftGate : Gate n w → List (Gate n (n + w))
  | .input i t => [.notg (lowWire w i) (highWire t), .notg (highWire t) (highWire t)]
  | .notg a t => [.notg (highWire a) (highWire t)]
  | .andg a b t => [.andg (highWire a) (highWire b) (highWire t)]
  | .xorg a b t => [.xorg (highWire a) (highWire b) (highWire t)]

/-- **The read-once program**: load prefix, then the shifted body. -/
def readOnce (P : Prog n w) : Prog n (n + w) :=
  ⟨loadPrefix n w ++ P.gates.flatMap shiftGate, highWire P.out⟩

/-- The simulation relation: low wires hold the inputs, high wires mirror the original state. -/
def Rel (z : Fin n → Bool) (S : Fin (n + w) → Bool) (s : Fin w → Bool) : Prop :=
  (∀ i : Fin n, S (lowWire w i) = z i) ∧ (∀ j : Fin w, S (highWire j) = s j)

theorem lowWire_ne_highWire (i : Fin n) (j : Fin w) : lowWire w i ≠ highWire j :=
  Fin.ne_of_val_ne (by have := i.isLt; simp [lowWire, highWire]; omega)

theorem highWire_injective : Function.Injective (highWire (n := n) (w := w)) := by
  intro a b hab
  have := congrArg Fin.val hab
  simp only [highWire] at this
  exact Fin.ext (by omega)

/-- One shifted gate preserves the simulation relation. -/
theorem rel_step (z : Fin n → Bool) (S : Fin (n + w) → Bool) (s : Fin w → Bool) (g : Gate n w)
    (hRel : Rel z S s) : Rel z (runGates z (shiftGate g) S) (step z s g) := by
  obtain ⟨hlow, hhigh⟩ := hRel
  cases g with
  | input i t =>
    constructor
    · intro i'
      show (Function.update (Function.update S (highWire t) (! S (lowWire w i)))
          (highWire t) (! (Function.update S (highWire t) (! S (lowWire w i))) (highWire t)))
          (lowWire w i') = z i'
      rw [Function.update_of_ne (lowWire_ne_highWire i' t),
        Function.update_of_ne (lowWire_ne_highWire i' t), hlow]
    · intro j
      show (Function.update (Function.update S (highWire t) (! S (lowWire w i)))
          (highWire t) (! (Function.update S (highWire t) (! S (lowWire w i))) (highWire t)))
          (highWire j) = (Function.update s t (z i)) j
      by_cases hjt : j = t
      · subst hjt
        simp only [Function.update_self]
        rw [Bool.not_not, hlow]
      · rw [Function.update_of_ne (fun hc => hjt (highWire_injective hc)),
          Function.update_of_ne (fun hc => hjt (highWire_injective hc)), hhigh,
          Function.update_of_ne hjt]
  | notg a t =>
    constructor
    · intro i'
      show (Function.update S (highWire t) (! S (highWire a))) (lowWire w i') = z i'
      rw [Function.update_of_ne (lowWire_ne_highWire i' t), hlow]
    · intro j
      show (Function.update S (highWire t) (! S (highWire a))) (highWire j)
          = (Function.update s t (! s a)) j
      by_cases hjt : j = t
      · subst hjt
        rw [Function.update_self, Function.update_self, hhigh]
      · rw [Function.update_of_ne (fun hc => hjt (highWire_injective hc)), hhigh,
          Function.update_of_ne hjt]
  | andg a b t =>
    constructor
    · intro i'
      show (Function.update S (highWire t) (S (highWire a) && S (highWire b))) (lowWire w i') = z i'
      rw [Function.update_of_ne (lowWire_ne_highWire i' t), hlow]
    · intro j
      show (Function.update S (highWire t) (S (highWire a) && S (highWire b))) (highWire j)
          = (Function.update s t (s a && s b)) j
      by_cases hjt : j = t
      · subst hjt
        rw [Function.update_self, Function.update_self, hhigh, hhigh]
      · rw [Function.update_of_ne (fun hc => hjt (highWire_injective hc)), hhigh,
          Function.update_of_ne hjt]
  | xorg a b t =>
    constructor
    · intro i'
      show (Function.update S (highWire t) (xor (S (highWire a)) (S (highWire b))))
          (lowWire w i') = z i'
      rw [Function.update_of_ne (lowWire_ne_highWire i' t), hlow]
    · intro j
      show (Function.update S (highWire t) (xor (S (highWire a)) (S (highWire b)))) (highWire j)
          = (Function.update s t (xor (s a) (s b))) j
      by_cases hjt : j = t
      · subst hjt
        rw [Function.update_self, Function.update_self, hhigh, hhigh]
      · rw [Function.update_of_ne (fun hc => hjt (highWire_injective hc)), hhigh,
          Function.update_of_ne hjt]

/-- The shifted body preserves the simulation relation. -/
theorem rel_fold (z : Fin n → Bool) (gs : List (Gate n w)) :
    ∀ (S : Fin (n + w) → Bool) (s : Fin w → Bool), Rel z S s →
      Rel z (runGates z (gs.flatMap shiftGate) S) (runGates z gs s) := by
  induction gs with
  | nil => intro S s h; exact h
  | cons g gs ih =>
    intro S s h
    rw [List.flatMap_cons, runGates_append']
    exact ih _ _ (rel_step z S s g h)

/-- Low wires not in the load list are untouched. -/
theorem loadl_notin (z : Fin n → Bool) (l : List (Fin n)) (i : Fin n) (hi : i ∉ l) :
    ∀ S : Fin (n + w) → Bool,
      (runGates z (l.map (fun i' => Gate.input i' (lowWire w i'))) S) (lowWire w i)
        = S (lowWire w i) := by
  induction l with
  | nil => intro S; rfl
  | cons i0 l ihl =>
    intro S
    show (runGates z (l.map _) (Function.update S (lowWire w i0) (z i0))) (lowWire w i) = _
    rw [ihl (fun hc => hi (List.mem_cons_of_mem i0 hc)),
      Function.update_of_ne (fun hc => hi (by
        rw [show i = i0 from Fin.ext (by
          have := congrArg Fin.val hc; simpa [lowWire] using this)]
        exact List.mem_cons_self))]

/-- Loaded low wires hold their inputs. -/
theorem loadl_low (z : Fin n → Bool) (l : List (Fin n)) (hnd : l.Nodup) (i : Fin n) (hi : i ∈ l) :
    ∀ S : Fin (n + w) → Bool,
      (runGates z (l.map (fun i' => Gate.input i' (lowWire w i'))) S) (lowWire w i) = z i := by
  induction l with
  | nil => exact absurd hi List.not_mem_nil
  | cons i0 l ihl =>
    intro S
    obtain ⟨hnotin, hnd'⟩ := List.nodup_cons.mp hnd
    show (runGates z (l.map _) (Function.update S (lowWire w i0) (z i0))) (lowWire w i) = z i
    rcases List.mem_cons.mp hi with heq | hmem
    · subst heq
      rw [loadl_notin z l i hnotin, Function.update_self]
    · exact ihl hnd' hmem _

/-- High wires are untouched by the load prefix. -/
theorem loadl_high (z : Fin n → Bool) (l : List (Fin n)) (j : Fin w) :
    ∀ S : Fin (n + w) → Bool,
      (runGates z (l.map (fun i' => Gate.input i' (lowWire w i'))) S) (highWire j)
        = S (highWire j) := by
  induction l with
  | nil => intro S; rfl
  | cons i0 l ihl =>
    intro S
    show (runGates z (l.map _) (Function.update S (lowWire w i0) (z i0))) (highWire j) = _
    rw [ihl, Function.update_of_ne (fun hc => lowWire_ne_highWire i0 j hc.symm)]

/-- **Read-once normalization is semantics-preserving.** -/
theorem readOnce_run (P : Prog n w) (z : Fin n → Bool) : (readOnce P).run z = P.run z := by
  unfold readOnce Prog.run
  rw [runGates_append']
  have hRel : Rel z (runGates z (loadPrefix n w) (fun _ => false)) (fun _ => false) := by
    constructor
    · intro i
      exact loadl_low z (List.finRange n) (List.nodup_finRange n) i (List.mem_finRange i) _
    · intro j
      exact loadl_high z (List.finRange n) j _
  exact (rel_fold z P.gates _ _ hRel).2 P.out

/-- The shifted body contains no input gates. -/
theorem body_no_reads (gs : List (Gate n w)) :
    (gs.flatMap shiftGate).filterMap Gate.readsInput = [] := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, List.filterMap_append, ih]
    have hg : (shiftGate g).filterMap Gate.readsInput = [] := by cases g <;> rfl
    rw [hg]
    rfl

/-- **The read-once program reads exactly `n` inputs.** -/
theorem readOnce_inputCount (P : Prog n w) : inputCount (readOnce P).gates = n := by
  unfold readOnce inputCount
  rw [List.filterMap_append, List.length_append, body_no_reads]
  have h1 : (loadPrefix n w).filterMap Gate.readsInput = List.finRange n := by
    unfold loadPrefix
    rw [List.filterMap_map]
    have h2 : (Gate.readsInput ∘ fun i : Fin n => Gate.input i (lowWire w i)) = some := rfl
    rw [h2, List.filterMap_some]
  rw [h1, List.length_finRange, List.length_nil]
  omega

/-- Read-once costs at most `n + 2·cost`. -/
theorem readOnce_cost (P : Prog n w) : (readOnce P).cost ≤ n + 2 * P.cost := by
  unfold readOnce Prog.cost
  rw [List.length_append]
  have h1 : (loadPrefix n w).length = n := by
    unfold loadPrefix
    rw [List.length_map, List.length_finRange]
  have h2 : ∀ gs : List (Gate n w), (gs.flatMap shiftGate).length ≤ 2 * gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have hg : (shiftGate g).length ≤ 2 := by cases g <;> simp [shiftGate]
      omega
  have := h2 P.gates
  omega

/-- Prefix reads are bounded by total reads. -/
theorem inputCount_take_le (gs : List (Gate n w)) (t : ℕ) :
    inputCount (gs.take t) ≤ inputCount gs := by
  unfold inputCount
  exact ((List.take_sublist t gs).filterMap Gate.readsInput).length_le

/-- **The cap theorem (Horn-A no-go).**  Every charged program has an equivalent whose reachable-state count
never exceeds `2^n` at ANY time.  Hence the canonical information invariant `max_t log₂|stateImage|` has
`min ≤ n` on every computable function: no information-type dynamic invariant can separate anything. -/
theorem info_cap (P : Prog n w) :
    ∃ (w' : ℕ) (P' : Prog n w'),
      (∀ z, P'.run z = P.run z)
      ∧ P'.cost ≤ n + 2 * P.cost
      ∧ ∀ t : ℕ, (stateImage (P'.gates.take t) (fun _ => false)).card ≤ 2 ^ n := by
  refine ⟨n + w, readOnce P, readOnce_run P, readOnce_cost P, fun t => ?_⟩
  calc (stateImage ((readOnce P).gates.take t) (fun _ => false)).card
      ≤ 2 ^ inputCount ((readOnce P).gates.take t) := stateImage_card_le _ _
    _ ≤ 2 ^ inputCount (readOnce P).gates :=
        Nat.pow_le_pow_right (by norm_num) (inputCount_take_le _ t)
    _ = 2 ^ n := by rw [readOnce_inputCount]

end PallLean.Paper93.DeepMath.PathB.ChargedInfoCap

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedInfoCap.stateImage_card_le
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedInfoCap.readOnce_run
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedInfoCap.info_cap
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedInfoCap.instantaneous_info_le_n
