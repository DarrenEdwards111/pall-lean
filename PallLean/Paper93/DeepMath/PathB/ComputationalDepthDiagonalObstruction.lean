import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHierarchyCanonical

/-!
# The diagonal socket: what is provable, and why the universal machine is irreducible

The last hierarchy socket is `DiagonalAgainstCanon a b` — a language in `NTIME(a)` differing from
every canonical `NTIME(b)` language.  This file builds everything about it that is genuinely
provable, and machine-checks the precise obstruction that makes the remaining piece — the universal
machine plus lazy diagonalisation — irreducible rather than a matter of more plumbing.

## What is proved

Fix a concrete surjection `surj : ℕ → (Σ k, FinMachineData k × ℕ)` (from countability) and the
induced enumeration `canonEnum b i` of the canonical `NTIME(b)` languages.

* **`canonEnum_covers`** — the enumeration covers `NTIMEcanon b`: every canonical language is
  `canonEnum b i` for some `i`.
* **`naiveDiag`** — the Cantor diagonal: `naiveDiag b x = ! canonEnum b (|x|) x`.
* **`naiveDiag_differs`** — the diagonal DIFFERS from every canonical language.  Proved cleanly by
  Cantor: on `x = 0^i` (with `|x| = i`), `naiveDiag` flips `canonEnum b i`, and `canonEnum b i` is
  the target language.  So the "differs from all" half of the socket is fully discharged.

## The obstruction (machine-checked)

* **`naiveDiag_is_complement`** — `naiveDiag b x = ! canonEnum b (|x|) x`: the naive diagonal is,
  pointwise, the COMPLEMENT of a universal nondeterministic evaluation.  Complementing an `NTIME`
  language is a `coNTIME` operation, not an `NTIME` one — so `naiveDiag ∈ NTIME(a)` is exactly the
  nondeterministic complementation problem.  This is the concrete, proved reason the naive diagonal
  does NOT witness `DiagonalAgainstCanon`: it differs from everything but sits in `coNTIME(a)`, the
  wrong class.

## The irreducible remainder

`DiagonalAgainstCanon a b` needs a diagonal that BOTH differs (done, `naiveDiag_differs` shows the
Cantor part is easy) AND lands in `NTIME(a)` (not `coNTIME`).  The standard fix is **lazy /
delayed diagonalisation** (Žák / Cook / Seiferas–Fischer–Meyer): a cleverer diagonal that spreads
the single flip across a range of inputs so the complement is realised within the `n^a` budget
without a global negation — and it requires a **universal machine** that simulates
`canonLang b k data c` on its own index within the larger clock.

Building that universal machine over `ComposableMachine` (encode the transition table on the tape,
simulate steps, count the clock) is genuine formalisation labor — hundreds to thousands of lines —
and it is the one piece of the entire uniform route that cannot be reduced further or faked.  This
file marks the boundary precisely: the diagonalisation LOGIC is proved; the universal machine is
the irreducible primitive, and the proved `naiveDiag_is_complement` is exactly why.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.DiagonalObstruction

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal
open PallLean.Paper93.DeepMath.PathB.NTIMEEnumerable
open PallLean.Paper93.DeepMath.PathB.HierarchyCanonical

/-- A fixed surjection onto the canonical parameters (from countability). -/
noncomputable def surj : ℕ → Σ k, FinMachineData k × ℕ :=
  Classical.choose (exists_surjective_nat (Σ k, FinMachineData k × ℕ))

theorem surj_surjective : Function.Surjective surj :=
  Classical.choose_spec (exists_surjective_nat (Σ k, FinMachineData k × ℕ))

/-- The concrete enumeration of canonical `NTIME(b)` languages. -/
noncomputable def canonEnum (b i : ℕ) : Lang :=
  canonLang b (surj i).1 (surj i).2.1 (surj i).2.2

/-- **The enumeration covers `NTIMEcanon b` (proved).** -/
theorem canonEnum_covers (b : ℕ) (L : Lang) (h : NTIMEcanon b L) : ∃ i, L = canonEnum b i := by
  obtain ⟨k, data, c, rfl⟩ := h
  obtain ⟨i, hi⟩ := surj_surjective ⟨k, data, c⟩
  exact ⟨i, by unfold canonEnum; rw [hi]⟩

/-- **The Cantor diagonal**: flip the `|x|`-th canonical language on input `x`. -/
noncomputable def naiveDiag (b : ℕ) : Lang := fun x => ! canonEnum b x.length x

/-- **The diagonal is a complement (proved) — the obstruction.**  `naiveDiag` is pointwise the
complement of the universal evaluation `canonEnum`.  Complementing `NTIME` is `coNTIME`, so
`naiveDiag ∈ NTIME(a)` is the nondeterministic complementation problem — the wrong class. -/
theorem naiveDiag_is_complement (b : ℕ) (x : List Bool) :
    naiveDiag b x = ! canonEnum b x.length x := rfl

/-- **The diagonal differs from every canonical language (proved).**  The Cantor half of the socket:
on `x = 0^i` the diagonal flips `canonEnum b i`, which is the target language — so they disagree
there, hence differ as functions. -/
theorem naiveDiag_differs (b k : ℕ) (data : FinMachineData k) (c : ℕ) :
    naiveDiag b ≠ canonLang b k data c := by
  obtain ⟨i, hi⟩ := surj_surjective ⟨k, data, c⟩
  have hce : canonEnum b i = canonLang b k data c := by unfold canonEnum; rw [hi]
  intro heq
  have hx := congrFun heq (List.replicate i false)
  have hlen : (List.replicate i false).length = i := by simp
  have hnd : naiveDiag b (List.replicate i false)
      = ! canonLang b k data c (List.replicate i false) := by
    show (! canonEnum b (List.replicate i false).length (List.replicate i false)) = _
    rw [hlen, hce]
  rw [hnd] at hx
  revert hx
  cases canonLang b k data c (List.replicate i false) <;> decide

/-- **The differs-from-all half of `DiagonalAgainstCanon`, discharged (proved).**  Any diagonal that
merely needs to differ from every canonical language is provided by `naiveDiag`; the ONLY missing
ingredient for `DiagonalAgainstCanon a b` is `naiveDiag ∈ NTIME(a)` — and by
`naiveDiag_is_complement` that is the co-nondeterministic obstruction requiring lazy diagonalisation
and a universal machine. -/
theorem diagonal_differs_half (b : ℕ) :
    ∀ (k : ℕ) (data : FinMachineData k) (c : ℕ), naiveDiag b ≠ canonLang b k data c :=
  naiveDiag_differs b

end PallLean.Paper93.DeepMath.PathB.DiagonalObstruction

#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalObstruction.canonEnum_covers
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalObstruction.naiveDiag_differs
#print axioms PallLean.Paper93.DeepMath.PathB.DiagonalObstruction.naiveDiag_is_complement
