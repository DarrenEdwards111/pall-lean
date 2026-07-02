import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEnumerableNTMComplement

/-!
# Enumerable NTM: the nondeterministic-hierarchy separation skeleton

This assembles the socket-1 diagonalisation into a clean `NTIME`-class separation.  The lazy diagonal language `D` is
**proved** to escape `NTIME[f]` (no enumerable machine of the model computes it with clock `f`).  The one remaining fact —
that `D` is *realisable* within a larger clock `g` (the diagonaliser machine, shift + boundary complement, run within
budget `g`) — is isolated as an **explicit hypothesis**, exactly the honest form of the Williams sockets (a stated `Prop`
the caller must supply, not a hidden axiom).  Given it, the diagonalisation gives `NTIME[g] ⊄ NTIME[f]`.

  `NTIME` — the languages computed by the enumerable model within clock `tb`: `{L | ∃ e, (fun x ↦ nLang … tb e x) = L}`.
  `diagLang_not_mem_NTIME` — **PROVED**: the diagonal language `D_f = diagonalizer (nLang … f) L` is **not** in `NTIME[f]`
        (the escape, from `lazy_diag_escapes_all_ntm`).
  `NTIME_not_subset_of_diag_realizable` — **PROVED**: if `D_f ∈ NTIME[g]` (the realisation hypothesis), then
        `NTIME[g] ⊄ NTIME[f]` — the strict-separation direction.

## Honest scope — the separation modulo the (deep) realisation

`diagLang_not_mem_NTIME` is fully proved: the diagonal genuinely escapes clock `f`.  The separation
`NTIME_not_subset_of_diag_realizable` is proved *given* `D_f ∈ NTIME[g]`, which is precisely the diagonaliser's machine
realisation within budget `g` — assembling the overhead-`1` universal-simulation **shift** (done) with the boundary
**complement** (a decidable search of `≤ (tb+1)·B^{tb}` configs, bounded in the prior rung) into an actual enumerable NTM
run within the padded clock `g`.  That realisation is the `≈ Williams' algorithm` universal-machine content the memory
flags as the deep bottleneck; it is stated here as an honest hypothesis, not proved or axiomatised away.  So this file
reduces the nondeterministic time hierarchy to that single realisation fact.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.EnumerableNTM

open PallLean.Paper93.DeepMath.PathB.LazyDiagonalization

/-- The languages computed by the enumerable model within clock `tb`: those equal to some machine `e`'s bounded-acceptance
language. -/
def NTIME (nsucc : ℕ → ℕ → List ℕ) (ninit : ℕ → ℕ) (naccept : ℕ → ℕ → Bool) (tb : ℕ → ℕ) :
    Set (ℕ → Bool) :=
  {L | ∃ e, (fun x => nLang nsucc ninit naccept tb e x) = L}

/-- **The diagonal escapes clock `f` (proved)**: `D_f = diagonalizer (nLang … f) L` is not the language of any enumerable
machine run with clock `f`. -/
theorem diagLang_not_mem_NTIME (nsucc : ℕ → ℕ → List ℕ) (ninit : ℕ → ℕ) (naccept : ℕ → ℕ → Bool)
    (f : ℕ → ℕ) (L : ℕ) :
    (fun x => diagonalizer (nLang nsucc ninit naccept f) L x) ∉ NTIME nsucc ninit naccept f := by
  rintro ⟨e, he⟩
  exact lazy_diag_escapes_all_ntm nsucc ninit naccept f L ⟨e, fun x => congrFun he x⟩

/-- **The separation, modulo realisation (proved)**: if the diagonal `D_f` is realisable within the larger clock `g`
(`D_f ∈ NTIME[g]`), then `NTIME[g] ⊄ NTIME[f]` — a language of clock `g` escapes clock `f`.  The realisation hypothesis is
the diagonaliser machine (shift + bounded complement) run within budget `g`. -/
theorem NTIME_not_subset_of_diag_realizable (nsucc : ℕ → ℕ → List ℕ) (ninit : ℕ → ℕ)
    (naccept : ℕ → ℕ → Bool) (f g : ℕ → ℕ) (L : ℕ)
    (h : (fun x => diagonalizer (nLang nsucc ninit naccept f) L x) ∈ NTIME nsucc ninit naccept g) :
    ¬ (NTIME nsucc ninit naccept g ⊆ NTIME nsucc ninit naccept f) :=
  fun hsub => diagLang_not_mem_NTIME nsucc ninit naccept f L (hsub h)

end PallLean.Paper93.DeepMath.PathB.EnumerableNTM

#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.diagLang_not_mem_NTIME
#print axioms PallLean.Paper93.DeepMath.PathB.EnumerableNTM.NTIME_not_subset_of_diag_realizable
