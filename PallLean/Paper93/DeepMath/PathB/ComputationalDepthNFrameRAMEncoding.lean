import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameTMEncoding

/-!
# N-Frame: the RAM encoding — indirect addressing in the boundary model

The TM file handled the radius-1 case.  This file does the RAM side — and begins with an **honest correction** to the
earlier "RAM is `O(log B)`-local" shorthand: it is *false for load coordinates*.  An indirect load `acc := mem[A]` makes
the accumulator's next value depend on one bit of **every** memory cell (plus the address) — a window of `R + O(log R)`
bits, not `O(log B)`.  The Shannon bound `7·2^k` is useless there.  The true statement, and what this file proves, is:

> RAM step coordinates have **polynomial-size structured circuits** (address multiplexers) despite their large windows —
> and the tableau machinery (bricks 2–5) is size-parametric, so it accepts them directly, bypassing Shannon.

The machine: a **scan-RAM** with one-hot addressing — `R` memory bits, a one-hot `R`-bit pointer, an accumulator:

  `acc' := acc XOR mem[A]` (indirect, pointer-addressed load) · `A' := rotate A` · `mem' := mem`.

  `orChain` / `eval_orChain` / `volume_orChain_le` — **PROVED**: the OR-chain combinator and its exact semantics/size.
  `ramStep` / `ramTree` / `ramTree_eval` / `ramTree_volume` — **PROVED**: the step semantics, its per-coordinate circuit
        trees (the load coordinate is the multiplexer `⋁ᵢ (Aᵢ ∧ memᵢ)` — volume `≤ 4R+3`, *linear*, despite the
        `R+1`-bit window), and their correctness and size.
  `ramScan_cbudget` — **PROVED, the headline**: the scan-RAM run `T` steps decides `f` with
        `cbudget f ≤ (2R+1) + T·((2R+1)·(4R+3)) + 1` — polynomial in `R` and `T`, with the per-step factor *linear*
        rather than Shannon-exponential.

## Honest scope

One-hot addressing carries the full indirect-access structure (pointer-addressed load); **binary** addressing reduces to
it by the standard `w → 2^w` decoder — whose circuit *size* is already bounded by the repo's `volume_mintermOn_le`, and
whose value-correctness (binary-decode bijection) is the named mechanical residue.  A full program-controlled RAM
(program counter, instruction dispatch) is the same pattern plus an `O(1)`-way dispatch multiplexer — named, mechanical.
The open target `NFrameCircuitLowerBoundTarget SAT` is untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {R : ℕ}

/-! ### The OR-chain combinator -/

/-- OR-chain of a list of transducers. -/
def orChain {B : ℕ} : List (Trans B) → Trans B
  | [] => Trans.cst false
  | t :: l => Trans.bin (· || ·) t (orChain l)

theorem eval_orChain {B : ℕ} (l : List (Trans B)) (x : Fin B → Bool) :
    eval (orChain l) x = l.any (fun t => eval t x) := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [orChain, eval, ih]

theorem volume_orChain_le {B : ℕ} (l : List (Trans B)) (c : ℕ)
    (h : ∀ t ∈ l, volume t ≤ c) :
    volume (orChain l) ≤ (c + 1) * l.length + 1 := by
  induction l with
  | nil => simp [orChain, volume]
  | cons t l ih =>
    have ht := h t (List.mem_cons_self)
    have hl := ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))
    simp only [orChain, volume, List.length_cons]
    have : (c + 1) * (l.length + 1) = (c + 1) * l.length + (c + 1) := by ring
    omega

/-! ### The scan-RAM: coordinates and step semantics -/

/-- The one-hot address bit `i` (coordinates `[0, R)`). -/
def aIdx (i : Fin R) : Fin (R + 1 + R) := ⟨i.val, by have := i.isLt; omega⟩

/-- The accumulator (coordinate `R`). -/
def accIdx : Fin (R + 1 + R) := ⟨R, by omega⟩

/-- The memory bit `i` (coordinates `[R+1, 2R+1)`). -/
def mIdx (i : Fin R) : Fin (R + 1 + R) := ⟨R + 1 + i.val, by have := i.isLt; omega⟩

/-- The pointer-addressed load: `⋁ᵢ (Aᵢ ∧ memᵢ)` — under a one-hot pointer, this is `mem[A]`. -/
def loadVal (x : Fin (R + 1 + R) → Bool) : Bool :=
  (List.finRange R).any (fun i => x (aIdx i) && x (mIdx i))

/-- **The scan-RAM step**: rotate the pointer, XOR the loaded bit into the accumulator, keep memory. -/
def ramStep (j : Fin (R + 1 + R)) (x : Fin (R + 1 + R) → Bool) : Bool :=
  if hj : j.val < R then
    x (aIdx ⟨(j.val + R - 1) % R, Nat.mod_lt _ (by omega)⟩)
  else if j.val = R then
    xor (x accIdx) (loadVal x)
  else
    x j

/-! ### The per-coordinate circuit trees -/

/-- The load multiplexer tree: `⋁ᵢ (Aᵢ ∧ memᵢ)` — **linear** volume despite its `R+1`-bit window. -/
def loadTree : Trans (R + 1 + R) :=
  orChain ((List.finRange R).map fun i =>
    Trans.bin (· && ·) (Trans.var (aIdx i)) (Trans.var (mIdx i)))

theorem eval_loadTree (x : Fin (R + 1 + R) → Bool) : eval loadTree x = loadVal x := by
  unfold loadTree loadVal
  rw [eval_orChain, List.any_map]
  rfl

theorem volume_loadTree : volume (loadTree (R := R)) ≤ 4 * R + 1 := by
  unfold loadTree
  have h := volume_orChain_le
    ((List.finRange R).map fun i =>
      Trans.bin (· && ·) (Trans.var (aIdx i)) (Trans.var (mIdx i))) 3
    (by
      intro t ht
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
      simp [volume])
  rw [List.length_map, List.length_finRange] at h
  omega

/-- The per-coordinate tree of the scan-RAM step. -/
def ramTree (j : Fin (R + 1 + R)) : Trans (R + 1 + R) :=
  if hj : j.val < R then
    Trans.var (aIdx ⟨(j.val + R - 1) % R, Nat.mod_lt _ (by omega)⟩)
  else if j.val = R then
    Trans.bin xor (Trans.var accIdx) loadTree
  else
    Trans.var j

/-- **The trees compute the step (proved).** -/
theorem ramTree_eval (j : Fin (R + 1 + R)) (x : Fin (R + 1 + R) → Bool) :
    eval (ramTree j) x = ramStep j x := by
  unfold ramTree ramStep
  by_cases hj : j.val < R
  · rw [dif_pos hj, dif_pos hj]
    rfl
  · rw [dif_neg hj, dif_neg hj]
    by_cases hacc : j.val = R
    · rw [if_pos hacc, if_pos hacc]
      show xor (x accIdx) (eval loadTree x) = xor (x accIdx) (loadVal x)
      rw [eval_loadTree]
    · rw [if_neg hacc, if_neg hacc]
      rfl

/-- **The trees are small (proved)**: every coordinate's circuit has volume `≤ 4R+3` — linear, not
Shannon-exponential. -/
theorem ramTree_volume (j : Fin (R + 1 + R)) : volume (ramTree j) ≤ 4 * R + 3 := by
  unfold ramTree
  by_cases hj : j.val < R
  · rw [dif_pos hj]
    simp [volume]
  · rw [dif_neg hj]
    by_cases hacc : j.val = R
    · rw [if_pos hacc]
      have := volume_loadTree (R := R)
      simp only [volume]
      omega
    · rw [if_neg hacc]
      simp [volume]

/-! ### The headline: the scan-RAM circuit bound -/

/-- **The scan-RAM circuit bound (proved).**  The indirect-access machine run `T` steps decides `f` with
`cbudget f ≤ (2R+1) + T·((2R+1)·(4R+3)) + 1` — polynomial in `R` and `T`, the per-step factor linear: indirect
addressing enters the boundary model through structured multiplexer circuits, not through window-exponential
realization. -/
theorem ramScan_cbudget {n : ℕ} (T : ℕ) (out : Fin (R + 1 + R))
    (inp : Fin (R + 1 + R) → Sum (Fin n) Bool) (f : (Fin n → Bool) → Bool)
    (hdec : ∀ x : Fin n → Bool,
      iterStep (ramStep (R := R)) T (fun j => Sum.elim x id (inp j)) out = f x) :
    cbudget f ≤ (R + 1 + R) + T * ((R + 1 + R) * (4 * R + 3)) + 1 := by
  -- the per-coordinate circuits, directly (no Shannon)
  set cs : Fin (R + 1 + R) → List (CGate (R + 1 + R)) :=
    fun j => compile 0 (ramTree j) with hcs
  have hcomp : ∀ j, computes (cs j) (ramStep j) := by
    intro j x
    rw [hcs]
    have h1 := compile_computes (ramTree j) x
    rw [h1]
    exact ramTree_eval j x
  have hc0 : ∀ j, 0 < (cs j).length := by
    intro j
    rw [hcs, compile_length]
    exact volume_pos _
  have hsz : ∀ j, (cs j).length ≤ 4 * R + 3 := by
    intro j
    rw [hcs, compile_length]
    exact ramTree_volume j
  have hs0 : 0 < 4 * R + 3 := by omega
  have hmc := machineCircuit_computes cs (ramStep (R := R)) (4 * R + 3) T out hsz hc0 hcomp hs0
  have hcomputes : computes
      ((machineCircuit cs (4 * R + 3) T out).map (retypeInpCB inp)) f := by
    intro x
    show (runFrom x [] ((machineCircuit cs (4 * R + 3) T out).map (retypeInpCB inp))).getD
        (((machineCircuit cs (4 * R + 3) T out).map (retypeInpCB inp)).length - 1) false = f x
    rw [List.length_map, runFrom_retypeInpCB inp x]
    have hmc2 := hmc (fun j => Sum.elim x id (inp j))
    unfold output at hmc2
    rw [hmc2]
    exact hdec x
  have hmem : cbudget f
      ≤ ((machineCircuit cs (4 * R + 3) T out).map (retypeInpCB inp)).length :=
    Nat.sInf_le ⟨_, hcomputes, rfl⟩
  have hlen : ((machineCircuit cs (4 * R + 3) T out).map (retypeInpCB inp)).length
      = (R + 1 + R) + T * ((R + 1 + R) * (4 * R + 3)) + 1 := by
    rw [List.length_map, machineCircuit_length cs (4 * R + 3) T out hsz]
  omega

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.eval_loadTree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.ramTree_eval
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.ramScan_cbudget
