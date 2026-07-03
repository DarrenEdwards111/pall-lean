import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameSimulationBrick5

/-!
# N-Frame: the blockwise radius-1 machine — the TM-tableau locality encoding

Brick 5 discharged `simulation` for the abstract local-machine model.  This file supplies the encoding that classical
machines actually use: the **blockwise radius-1 (cellular / tableau-row) machine**.  The configuration is `N` cells of
`c` bits; each cell's next block is a function of its left neighbour, itself, and its right neighbour.  This is exactly
the locality structure of Turing-machine tableaux (Cook–Levin: each tableau cell depends on the three cells above it,
with head and state carried in the cell blocks).

  `cellIdx` / `blockOf` / `blockOpt` — the cell/bit index arithmetic and block extraction (out-of-range neighbours read
        as the all-`false` block).
  `blockStep` — the machine: coordinate `(cell q, bit b)`'s next value is the rule applied to blocks `q−1, q, q+1`.
  `blockWindow` / `blockWindow_length` — **PROVED**: each coordinate's window is at most `3c` bits.
  `blockStep_local` — **PROVED, the locality theorem**: `blockStep` is a `3c`-local step function — every hypothesis of
        the local-machine interface.
  `blockMachine_cbudget` — **PROVED, the cash-out**: a radius-1 machine on `N` cells of `c` bits deciding `f` in `T`
        steps gives `cbudget f ≤ N·c + T·(N·c·(7·2^{3c})) + 1` — **polynomial in `N` and `T` for any fixed cell width**
        (`2^{3c}` is a constant of the alphabet), which is the Cook–Levin tableau bound.

## Honest scope — the locality engine of both encodings; the two named residues

A single-tape TM with state set `Q` and alphabet `Γ` *is* a radius-1 blockwise machine with `c = ⌈log|Γ|⌉ + 1 + ⌈log|Q|⌉`
bits per cell (symbol, head-flag, state) — the classical encoding; instantiating a concrete `δ`-table into a `rule` and
proving the step correspondence is mechanical but a separate formalization.  A RAM is *not* radius-1 — indirect
addressing needs `O(log B)`-bit windows (address decoding) — but it plugs into the same general local-machine interface
(brick 4/5) with `k = O(log B)`, still polynomial.  Both instantiations are the named residual translation steps; the
locality engine they plug into is, with this file, fully proved.  The open target `NFrameCircuitLowerBoundTarget SAT` is
untouched.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

variable {N c : ℕ}

/-! ### Index arithmetic -/

theorem c_pos_of (j : Fin (N * c)) : 0 < c := by
  rcases Nat.eq_zero_or_pos c with h | h
  · subst h
    exact absurd j.isLt (by simp)
  · exact h

theorem cellIdx_lt (q : Fin N) (b : Fin c) : q.val * c + b.val < N * c := by
  have h1 : q.val * c + b.val < (q.val + 1) * c := by
    have := b.isLt
    rw [Nat.succ_mul]
    omega
  have h2 : (q.val + 1) * c ≤ N * c := Nat.mul_le_mul_right c (by have := q.isLt; omega)
  omega

/-- The flat index of bit `b` of cell `q`. -/
def cellIdx (q : Fin N) (b : Fin c) : Fin (N * c) := ⟨q.val * c + b.val, cellIdx_lt q b⟩

/-- The cell of a flat coordinate. -/
def cellOf (j : Fin (N * c)) : Fin N :=
  ⟨j.val / c, by rw [Nat.div_lt_iff_lt_mul (c_pos_of j)]; exact j.isLt⟩

/-- The bit-within-cell of a flat coordinate. -/
def bitOf (j : Fin (N * c)) : Fin c := ⟨j.val % c, Nat.mod_lt _ (c_pos_of j)⟩

/-! ### Blocks and neighbours -/

/-- The `c`-bit block of cell `q`. -/
def blockOf (x : Fin (N * c) → Bool) (q : Fin N) : Fin c → Bool :=
  fun b => x (cellIdx q b)

/-- A possibly-out-of-range block: missing neighbours read as all-`false`. -/
def blockOpt (x : Fin (N * c) → Bool) : Option (Fin N) → Fin c → Bool
  | none => fun _ => false
  | some q => blockOf x q

/-- The left neighbour of cell `q`, if any. -/
def leftOf (q : Fin N) : Option (Fin N) :=
  if h : q.val = 0 then none else some ⟨q.val - 1, by have := q.isLt; omega⟩

/-- The right neighbour of cell `q`, if any. -/
def rightOf (q : Fin N) : Option (Fin N) :=
  if h : q.val + 1 < N then some ⟨q.val + 1, h⟩ else none

/-! ### The blockwise machine and its window -/

/-- **The blockwise radius-1 machine**: coordinate `(cell q, bit b)`'s next value is the rule applied to the blocks of
cells `q−1, q, q+1`. -/
def blockStep (rule : (Fin c → Bool) → (Fin c → Bool) → (Fin c → Bool) → Fin c → Bool)
    (j : Fin (N * c)) (x : Fin (N * c) → Bool) : Bool :=
  rule (blockOpt x (leftOf (cellOf j))) (blockOf x (cellOf j))
    (blockOpt x (rightOf (cellOf j))) (bitOf j)

/-- The bit indices of one cell. -/
def cellWindow (q : Fin N) : List (Fin (N * c)) := (List.finRange c).map (cellIdx q)

/-- The bit indices of a possibly-missing cell. -/
def optWindow : Option (Fin N) → List (Fin (N * c))
  | none => []
  | some q => cellWindow q

/-- The window of a coordinate: the three neighbouring cells' bits. -/
def blockWindow (j : Fin (N * c)) : List (Fin (N * c)) :=
  optWindow (leftOf (cellOf j)) ++ cellWindow (cellOf j) ++ optWindow (rightOf (cellOf j))

theorem cellWindow_length (q : Fin N) : (cellWindow (c := c) q).length = c := by
  simp [cellWindow]

theorem optWindow_length (o : Option (Fin N)) : (optWindow (c := c) o).length ≤ c := by
  cases o with
  | none => simp [optWindow]
  | some q => rw [optWindow, cellWindow_length]

/-- **The window bound (proved)**: each coordinate reads at most `3c` bits. -/
theorem blockWindow_length (j : Fin (N * c)) : (blockWindow j).length ≤ 3 * c := by
  unfold blockWindow
  rw [List.length_append, List.length_append, cellWindow_length]
  have h1 := optWindow_length (c := c) (leftOf (cellOf j))
  have h2 := optWindow_length (c := c) (rightOf (cellOf j))
  omega

theorem cellIdx_mem_cellWindow (q : Fin N) (b : Fin c) :
    cellIdx q b ∈ cellWindow (c := c) q :=
  List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩

/-- **The locality theorem (proved)**: the blockwise machine is `3c`-local — its step at any coordinate depends only on
that coordinate's window. -/
theorem blockStep_local (rule : (Fin c → Bool) → (Fin c → Bool) → (Fin c → Bool) → Fin c → Bool)
    (j : Fin (N * c)) (x y : Fin (N * c) → Bool)
    (hagree : ∀ p ∈ blockWindow j, x p = y p) :
    blockStep rule j x = blockStep rule j y := by
  have hself : blockOf x (cellOf j) = blockOf y (cellOf j) := by
    funext b
    exact hagree _ (by
      unfold blockWindow
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
        (Or.inr (cellIdx_mem_cellWindow (cellOf j) b)))))
  have hleft : blockOpt x (leftOf (cellOf j)) = blockOpt y (leftOf (cellOf j)) := by
    cases hL : leftOf (cellOf j) with
    | none => rfl
    | some q =>
      funext b
      show blockOf x q b = blockOf y q b
      exact hagree _ (by
        unfold blockWindow
        rw [hL]
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
          (Or.inl (cellIdx_mem_cellWindow q b)))))
  have hright : blockOpt x (rightOf (cellOf j)) = blockOpt y (rightOf (cellOf j)) := by
    cases hR : rightOf (cellOf j) with
    | none => rfl
    | some q =>
      funext b
      show blockOf x q b = blockOf y q b
      exact hagree _ (by
        unfold blockWindow
        rw [hR]
        exact List.mem_append.mpr (Or.inr (cellIdx_mem_cellWindow q b)))
  unfold blockStep
  rw [hself, hleft, hright]

/-! ### The cash-out: the Cook–Levin tableau bound -/

/-- **The blockwise-machine circuit bound (proved)**: a radius-1 machine on `N` cells of `c` bits deciding `f` in `T`
steps gives `cbudget f ≤ N·c + T·(N·c·(7·2^{3c})) + 1` — polynomial in `N` and `T` for any fixed cell width (the
Cook–Levin tableau bound in the boundary model). -/
theorem blockMachine_cbudget {n : ℕ}
    (rule : (Fin c → Bool) → (Fin c → Bool) → (Fin c → Bool) → Fin c → Bool)
    (T : ℕ) (out : Fin (N * c)) (inp : Fin (N * c) → Option (Fin n))
    (f : (Fin n → Bool) → Bool)
    (hdec : ∀ x : Fin n → Bool,
      iterStep (fun j => blockStep rule j) T (fun j => ((inp j).map x).getD false) out = f x) :
    cbudget f ≤ N * c + T * (N * c * (7 * 2 ^ (3 * c))) + 1 :=
  localMachine_cbudget (fun j => blockStep rule j) blockWindow (3 * c)
    blockWindow_length (fun j x y h => blockStep_local rule j x y h) T out inp f hdec

end PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.blockWindow_length
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.blockStep_local
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer.blockMachine_cbudget
