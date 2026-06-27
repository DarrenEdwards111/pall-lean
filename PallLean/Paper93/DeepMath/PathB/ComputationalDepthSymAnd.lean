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

end PallLean.Paper93.DeepMath.PathB.SymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.SymAnd.satCount_decompose
