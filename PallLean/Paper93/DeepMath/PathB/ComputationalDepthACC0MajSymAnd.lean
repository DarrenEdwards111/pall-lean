import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymAndFanIn

/-!
# The `MAJ∘SYM∘AND` collapse — majority of `SYM∘AND`s is a `SYM∘AND`, but exponentially (proved)

Entry 216 produced an *exact* representation of an `ACC⁰[p]` circuit `f` as a **majority vote of `2j` `SYM∘AND`
approximants** (`MajVote g = f`).  To reach the entry-203 quasipolynomial *single* `SYM∘AND` (the BT depth-collapse),
one would collapse that majority into one `SYM∘AND`.  This file proves the **structural collapse** — *any* Boolean
combiner of a list of `SYM∘AND`s (in particular `MAJ`) is a `SYM∘AND` — and is honest about the crucial caveat: the size
is **multiplicative**, hence *exponential* in the number of gates.

**This is exactly where the majority-route and the classical CRT-route diverge.**  The collapse is real (via the binary
`SYM∘AND` combine `hasSymAndFormFanIn_combine`, whose count mixed-radix-encodes the two sub-counts, iterated through an
`if-then-else` decomposition), so the entry-216 majority *is* a single `SYM∘AND` — but of multiplicative size
`∼ (size)^{(#gates)}`, exponential for the `2j = Θ(n)` approximants.  So the **RS-amplification route yields an
exact-but-exponential `SYM∘AND`, not the quasipolynomial one**.  Beigel–Tarui's quasipolynomial single `SYM∘AND` comes
instead from the *direct* low-degree route (entry 203 `btQuasipolyCollapse`: a low-degree representation has a
quasipolynomial `SYM∘AND`), fed by the RS approximation's degree bound (entry 204) — not from majority-of-approximants.

## What is proved (clean axioms, no `sorry`)

* **`IsSymAnd f := ∃ s w, HasSymAndFormFanIn f s w`** — `f` is (some-size) `SYM∘AND`.
* **`isSymAnd_combine`** — closure under any binary combiner (the existing `hasSymAndFormFanIn_combine`, existentialised).
* **`isSymAnd_list`** — the collapse: for any list `gs` of `SYM∘AND`s and any combiner `G : List Bool → Bool`,
  `fun x => G (gs.map (· x))` is a `SYM∘AND` (induction on `gs`, via the `if-then-else = (a∧A)∨(¬a∧B)` decomposition and
  three binary combines per step).  `MAJ` is a special case (`G = list-majority`).

## Honest scope

This proves the **structural `MAJ∘SYM∘AND` collapse** completely — any Boolean combiner of finitely many `SYM∘AND`s
(including `MAJ`, hence the entry-216 `MajVote`) is a single `SYM∘AND` — by induction using only the existing binary
combine.  **The size is multiplicative (exponential in the list length)**, as the iterated combine's `s₁+(s₁+1)·s₂` makes
explicit; this file does not (and cannot, via this route) give a *quasipolynomial* bound.  The honest consequence: the
entry-216 majority representation collapses to an exact `SYM∘AND` of **exponential** size; the quasipolynomial single
`SYM∘AND` of Beigel–Tarui is the **separate direct low-degree route** (entries 203–204), not this majority collapse.
This proves the collapse *exists* (structurally), and documents that it is *not* the quasipolynomial path.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`,
`ACC0_ROUTE_B_CONDITIONAL_ANATOMY.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0MajSymAnd

open PallLean.Paper93.DeepMath.PathB.ACC0SymAndFanIn
  (HasSymAndFormFanIn hasSymAndFormFanIn_const hasSymAndFormFanIn_combine)

variable {n : ℕ}

/-- **`f` is a `SYM∘AND`** (of some size and fan-in). -/
def IsSymAnd (f : (Fin n → Bool) → Bool) : Prop := ∃ s w, HasSymAndFormFanIn f s w

/-- **Closure under any binary combiner (PROVED).**  `comb (f x) (g x)` is a `SYM∘AND` if `f`, `g` are — the existing
binary `SYM∘AND` combine (`hasSymAndFormFanIn_combine`, mixed-radix), existentialised.  (Size `s₁+(s₁+1)·s₂` —
multiplicative.) -/
theorem isSymAnd_combine {f g : (Fin n → Bool) → Bool} (comb : Bool → Bool → Bool)
    (hf : IsSymAnd f) (hg : IsSymAnd g) : IsSymAnd (fun x => comb (f x) (g x)) := by
  obtain ⟨s1, w1, hf⟩ := hf
  obtain ⟨s2, w2, hg⟩ := hg
  exact ⟨_, _, hasSymAndFormFanIn_combine comb hf hg⟩

/-- **The `MAJ∘SYM∘AND` collapse (PROVED).**  For any list `gs` of `SYM∘AND`s and any Boolean combiner
`G : List Bool → Bool`, the function `fun x => G (gs.map (· x))` is a `SYM∘AND`.  Induction on `gs`: at the head `g`,
write `G (g x :: rest) = if g x then G(true::rest) else G(false::rest) = (g x ∧ A x) ∨ (¬ g x ∧ B x)` where
`A, B` are `SYM∘AND`s by induction, and combine via three binary combines.  `MAJ` is the special case `G = list-majority`
— so the entry-216 majority `MajVote g` is a `SYM∘AND`.  **Size: multiplicative (exponential in `gs.length`).** -/
theorem isSymAnd_list (gs : List ((Fin n → Bool) → Bool)) (hgs : ∀ g ∈ gs, IsSymAnd g)
    (G : List Bool → Bool) :
    IsSymAnd (fun x => G (gs.map (fun g => g x))) := by
  induction gs generalizing G with
  | nil => exact ⟨0, 0, hasSymAndFormFanIn_const (G [])⟩
  | cons g gs ih =>
      have hg : IsSymAnd g := hgs g (by simp)
      have hgs' : ∀ g' ∈ gs, IsSymAnd g' := fun g' hg' => hgs g' (by simp [hg'])
      have hA : IsSymAnd (fun x => G (true :: gs.map (fun g => g x))) :=
        ih hgs' (fun r => G (true :: r))
      have hB : IsSymAnd (fun x => G (false :: gs.map (fun g => g x))) :=
        ih hgs' (fun r => G (false :: r))
      have hP := isSymAnd_combine (· && ·) hg hA
      have hQ := isSymAnd_combine (fun a b => !a && b) hg hB
      have hR := isSymAnd_combine (· || ·) hP hQ
      have heq : (fun x => G (g x :: gs.map (fun g => g x)))
          = (fun x => (g x && G (true :: gs.map (fun g => g x)))
              || (!(g x) && G (false :: gs.map (fun g => g x)))) := by
        funext x
        cases hgx : g x <;> simp
      simp only [List.map_cons]
      rw [heq]; exact hR

end PallLean.Paper93.DeepMath.PathB.ACC0MajSymAnd

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MajSymAnd.isSymAnd_combine
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0MajSymAnd.isSymAnd_list
