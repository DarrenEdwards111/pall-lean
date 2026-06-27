import Mathlib

/-!
# SYM∘AND circuits and the satisfying-count decomposition (PROVED) — toward the Williams fast-SAT

The two cited axioms of the lazy-diagonal arc are full Williams-strength.  This file makes a *genuine* start on
the deeper one's algorithmic side — the Williams faster-than-brute-force `ACC`-`SAT` algorithm — by formalising
the structural fact that makes `SYM∘AND` circuits tractable to count.

A `SYM∘AND` circuit is a symmetric Boolean function `symFn : ℕ → Bool` applied to the number of firing `AND`
gates.  Its key property: the output depends on the input *only through the firing count*, so the number of
satisfying assignments decomposes as

  `satCount = Σ_{k} (if symFn k then #{inputs with exactly k gates firing} else 0)`.

This reduces SAT-*counting* of a `SYM∘AND` circuit to counting the level sets of the firing-count function — the
structural reason Williams' `ACC`-`SAT` algorithm beats brute force (after Beigel–Tarui put `ACC⁰` into
`SYM∘AND` form).  This is real circuit complexity, proved unconditionally; the full algorithm (computing those
level-set sizes faster than `2^n`) and Beigel–Tarui itself remain the cited axioms.
-/

namespace PallLean.Paper93.DeepMath.PathB.SymAnd

variable {n : ℕ}

/-- An `AND` gate over `n` Boolean variables: for each variable, either it is unconstrained (`none`) or it
requires the variable to take a fixed value (`some b`) — a conjunction of literals. -/
abbrev AndGate (n : ℕ) : Type := Fin n → Option Bool

/-- The gate fires on input `x` iff every constrained variable matches the required literal. -/
def AndFires (g : AndGate n) (x : Fin n → Bool) : Prop := ∀ i b, g i = some b → x i = b

instance (g : AndGate n) (x : Fin n → Bool) : Decidable (AndFires g x) := by
  unfold AndFires; infer_instance

/-- Boolean evaluation of an `AND` gate. -/
def andEval (g : AndGate n) (x : Fin n → Bool) : Bool := decide (AndFires g x)

/-- The number of `AND` gates that fire on input `x`. -/
def firingCount (gates : List (AndGate n)) (x : Fin n → Bool) : ℕ :=
  gates.countP (fun g => andEval g x)

/-- `firingCount` never exceeds the number of gates. -/
theorem firingCount_le (gates : List (AndGate n)) (x : Fin n → Bool) :
    firingCount gates x ≤ gates.length :=
  List.countP_le_length

/-- A `SYM∘AND` circuit's output: the symmetric function `symFn` applied to the firing count. -/
def symEval (symFn : ℕ → Bool) (gates : List (AndGate n)) (x : Fin n → Bool) : Bool :=
  symFn (firingCount gates x)

/-- The number of satisfying assignments of a `SYM∘AND` circuit. -/
def satCount (symFn : ℕ → Bool) (gates : List (AndGate n)) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Bool => symEval symFn gates x = true)).card

/-- The number of inputs on which exactly `k` gates fire — the level set of the firing-count function. -/
def levelCard (gates : List (AndGate n)) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Bool => firingCount gates x = k)).card

/-- **The satisfying-count decomposition.**  Because a `SYM∘AND` circuit's output depends on its input only
through the firing count, its number of satisfying assignments is the sum, over each possible count `k`, of
`symFn k` weighting the size of the `k`-th level set:

  `satCount symFn gates = Σ_{k ≤ #gates} (if symFn k then levelCard gates k else 0)`.

This is the structural fact that lets the count be computed from the level-set sizes alone — the heart of why
`SYM∘AND` (hence, via Beigel–Tarui, `ACC⁰`) circuits are tractable to count, which Williams' algorithm exploits.
-/
theorem satCount_decompose (symFn : ℕ → Bool) (gates : List (AndGate n)) :
    satCount symFn gates
      = ∑ k ∈ Finset.range (gates.length + 1),
          if symFn k then levelCard gates k else 0 := by
  rw [satCount, Finset.card_eq_sum_card_fiberwise
    (f := fun x : Fin n → Bool => firingCount gates x) (t := Finset.range (gates.length + 1))
    (fun x _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (firingCount_le gates x)))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hset : ((Finset.univ.filter (fun x : Fin n → Bool => symEval symFn gates x = true)).filter
        (fun x => firingCount gates x = k))
      = if symFn k then Finset.univ.filter (fun x : Fin n → Bool => firingCount gates x = k) else ∅ := by
    ext x
    by_cases hs : symFn k = true <;> by_cases hc : firingCount gates x = k <;>
      simp [Finset.mem_filter, symEval, hs, hc]
  rw [hset, levelCard]
  by_cases hs : symFn k = true <;> simp [hs]

/-- **The level sets partition the input space**: their sizes sum to `2ⁿ` (every assignment fires exactly some
number of gates).  So the `#gates + 1` numbers `levelCard gates 0, …, levelCard gates #gates` carry the full
mass of `{0,1}ⁿ` — computing them is exactly what a fast `SYM∘AND`-counting algorithm must do. -/
theorem sum_levelCard (gates : List (AndGate n)) :
    ∑ k ∈ Finset.range (gates.length + 1), levelCard gates k = 2 ^ n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n → Bool)))
    (f := fun x => firingCount gates x) (t := Finset.range (gates.length + 1))
    (fun x _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (firingCount_le gates x)))
  simp only [levelCard]
  rw [← h, Finset.card_univ]
  simp

/-- **Brute-force baseline**: a `SYM∘AND` circuit has at most `2ⁿ` satisfying assignments.  The content of the
Williams program is to *count* them in time `≪ 2ⁿ`; `satCount_decompose` reduces that to computing the level-set
sizes, the genuinely hard step (left to the cited axioms). -/
theorem satCount_le (symFn : ℕ → Bool) (gates : List (AndGate n)) :
    satCount symFn gates ≤ 2 ^ n := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_univ]
  simp

/-- **`satCount` depends on the gate structure only through the `level-set sizes` and `symFn`.**  Two `SYM∘AND`
circuits with the same symmetric function and the same level-set profile (and same gate count) have the same
satisfying-count — the precise sense in which the count is a *symmetric* quantity, and why an algorithm need
only produce the `levelCard` profile. -/
theorem satCount_eq_of_levelCard (symFn : ℕ → Bool) (gates gates' : List (AndGate n))
    (hlen : gates.length = gates'.length)
    (hlc : ∀ k, levelCard gates k = levelCard gates' k) :
    satCount symFn gates = satCount symFn gates' := by
  rw [satCount_decompose, satCount_decompose, hlen]
  exact Finset.sum_congr rfl (fun k _ => by rw [hlc])

/-- **`firingCount` is a sum of gate indicators** — `Σ_g [g fires]`.  This is the bridge to the polynomial
method: the firing count is a linear form in the gate-output indicators, each of which is a product of literal
indicators (an `AND`), so the count is represented by a polynomial whose degree is controlled by the gate
fan-ins — the algebraic handle the Razborov–Smolensky / Williams machinery uses. -/
theorem firingCount_eq_sum (gates : List (AndGate n)) (x : Fin n → Bool) :
    firingCount gates x = (gates.map (fun g => (andEval g x).toNat)).sum := by
  induction gates with
  | nil => rfl
  | cons g gs ih =>
    have hc : firingCount (g :: gs) x = firingCount gs x + (andEval g x).toNat := by
      simp only [firingCount, List.countP_cons]
      cases andEval g x <;> simp
    rw [hc, ih, List.map_cons, List.sum_cons]
    omega

/-- **The empty `SYM∘AND` circuit** fires no gates, so its output is the constant `symFn 0`. -/
@[simp] theorem firingCount_nil (x : Fin n → Bool) : firingCount ([] : List (AndGate n)) x = 0 := rfl

/-- **Satisfying-count of the constant (empty) circuit**: all `2ⁿ` assignments if `symFn 0`, none otherwise. -/
theorem satCount_nil (symFn : ℕ → Bool) :
    satCount symFn ([] : List (AndGate n)) = if symFn 0 then 2 ^ n else 0 := by
  rw [satCount]
  by_cases hs : symFn 0 = true <;> simp [symEval, hs]

end PallLean.Paper93.DeepMath.PathB.SymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.satCount_decompose
#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.firingCount_eq_sum
#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.satCount_nil
#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.sum_levelCard
#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.satCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.satCount_eq_of_levelCard
