import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDetTimeHierarchyRung3Lazy

/-!
# Time hierarchy, rung 3 (NTM realisation): the lazy diagonaliser over a machine enumeration

Rung 3's core (`…Rung3Lazy`) proved the lazy chain-collapse abstractly.  This file takes the next step of the
nondeterministic construction — the analogue of rung 1 for the deterministic case: it realises the lazy diagonal as
**one concrete acceptance function** `diagonalizer` over an *enumeration* `M : ℕ → ℕ → Bool` of machines (machine `i`
accepts input `x` iff `M i x`), with an explicit **range scheme** — machine `i` owns the `L + 1` inputs
`[i·(L+1), i·(L+1)+L]` — and proves the diagonaliser **escapes the enumeration**: no machine computes it.

  `diagonalizer M L x` — on input `x` owned by machine `i = x / (L+1)` at offset `k = x % (L+1)`: **shift** if `k < L`
        (`= M i (x+1)`, a complement-free simulation of machine `i` on the *next* input), **flip** at the boundary
        `k = L` (`= !(M i (i·(L+1)))`, the single complement of machine `i` on the *first* input of its range).
  `diagonalizer_shift` / `diagonalizer_flip` — the structure made explicit: on the `L` interior inputs of each range the
        diagonaliser is a **plain shift with no complement**; only the one boundary input complements.
  `diag_differs` — **PROVED**: for every machine `i`, the diagonaliser differs from `M i` at some input of `i`'s range
        (via rung 3's `lazyDiag_escapes_range`).
  `diagonalizer_not_enumerated` — **PROVED**: no machine of the enumeration computes the diagonaliser — it escapes the
        class.

## Why this is the nondeterministic realisation

The diagonaliser is **complement-free except at range boundaries**: of the `L + 1` inputs each machine owns, `L` are
pure shifts `M i (x+1)` (nondeterministic simulations, no complement) and exactly `1` is a complement.  This is the
whole point of laziness — a nondeterministic machine can do the `L` shifts cheaply and afford the single boundary
complement by exhaustive search within the padded budget of the range.  `diagonalizer_not_enumerated` is the
`D ∉ class` direction, realised over a concrete enumeration and range.

## Honest scope

This realises the diagonaliser and proves it escapes an *abstract* machine enumeration `M : ℕ → ℕ → Bool`, using rung
3's lazy core.  It is **not** the `NondetTimeHierarchy` socket.  What remains is the genuinely machine-level content,
the nondeterministic analogue of rungs 1–2's RAM interpreter: (i) `M` being an actual **enumerable NTM** model (the
repo's `ACC0NTM.NTM` has `Config : Type`, not enumerable); (ii) the `D ∈ NTIME[g]` direction — realising the shift as a
clocked **universal NTM simulation** of machine `i` on input `x+1`, and the boundary complement by exhaustive search
within the padded budget; (iii) the range width `L` grown by a fast-growing padding `f` so an `NTIME[f]` machine has
room for the boundary complement while an `NTIME[g]` machine does not, giving `NTIME[f] ⊊ NTIME[g]`.  This file supplies
the diagonaliser + the escapes direction; the universal-NTM-simulation realisation is the remaining socket.  Nothing
here is `NondetTimeHierarchy`, `NEXP ⊄ ACC⁰`, or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.LazyDiagonalization

/-- The lazy diagonaliser as one acceptance function over an enumeration `M` of machines, with machine `i` owning the
`L + 1` inputs `[i·(L+1), i·(L+1)+L]`.  On input `x` (owner `i = x/(L+1)`, offset `k = x%(L+1)`): **shift** to machine
`i` on the next input `x+1` when `k < L`, else **flip** machine `i`'s answer on the first input of its range. -/
def diagonalizer (M : ℕ → ℕ → Bool) (L x : ℕ) : Bool :=
  if x % (L + 1) < L then M (x / (L + 1)) (x + 1)
  else !(M (x / (L + 1)) ((x / (L + 1)) * (L + 1)))

/-- **Interior = pure shift, no complement (proved)**: on the `L` interior inputs of a range, the diagonaliser just
simulates its machine on the next input. -/
theorem diagonalizer_shift (M : ℕ → ℕ → Bool) (L x : ℕ) (h : x % (L + 1) < L) :
    diagonalizer M L x = M (x / (L + 1)) (x + 1) := if_pos h

/-- **Boundary = the single complement (proved)**: only on the one boundary input of a range does the diagonaliser
complement its machine (on the range's first input). -/
theorem diagonalizer_flip (M : ℕ → ℕ → Bool) (L x : ℕ) (h : ¬ x % (L + 1) < L) :
    diagonalizer M L x = !(M (x / (L + 1)) ((x / (L + 1)) * (L + 1))) := if_neg h

/-- **The diagonaliser differs from every machine (proved)**: for each machine `i`, `diagonalizer M L` disagrees with
`M i` at some input of `i`'s range `[i·(L+1), i·(L+1)+L]` — the lazy chain-collapse (rung 3) applied to `M i`. -/
theorem diag_differs (M : ℕ → ℕ → Bool) (L i : ℕ) : ∃ x, diagonalizer M L x ≠ M i x := by
  obtain ⟨k, hk, hne⟩ := lazyDiag_escapes_range (M i) (i * (L + 1)) L
  have hk' : k < L + 1 := Nat.lt_succ_of_le hk
  have hdiv : (i * (L + 1) + k) / (L + 1) = i := by
    rw [show i * (L + 1) + k = k + (L + 1) * i by ring,
      Nat.add_mul_div_left k i (Nat.succ_pos L), Nat.div_eq_of_lt hk', Nat.zero_add]
  have hmod : (i * (L + 1) + k) % (L + 1) = k := by
    rw [show i * (L + 1) + k = k + (L + 1) * i by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hk']
  refine ⟨i * (L + 1) + k, ?_⟩
  simp only [diagonalizer, hdiv, hmod]
  intro h
  exact hne h.symm

/-- **The diagonaliser escapes the enumeration (proved)**: no machine `M i` computes `diagonalizer M L` — it is not any
enumerated machine's language.  This is the `D ∉ class` direction of the nondeterministic construction, realised over a
concrete enumeration and range, and complement-free except at range boundaries. -/
theorem diagonalizer_not_enumerated (M : ℕ → ℕ → Bool) (L : ℕ) :
    ¬ ∃ i, ∀ x, M i x = diagonalizer M L x := by
  rintro ⟨i, hi⟩
  obtain ⟨x, hx⟩ := diag_differs M L i
  exact hx (hi x).symm

end PallLean.Paper93.DeepMath.PathB.LazyDiagonalization

#print axioms PallLean.Paper93.DeepMath.PathB.LazyDiagonalization.diag_differs
#print axioms PallLean.Paper93.DeepMath.PathB.LazyDiagonalization.diagonalizer_not_enumerated
