import PallLean.PaperFaithfulSeparation
import PallLean.GlobalGodMoveGauge

/-!
# Can Π⋆ (the God-Move gauge) be built as a theorem? No — it is uninhabited where it matters

The pvsnp1 separation reduces to building the Global God-Move gauge `Π⋆` as a theorem: a linear projection on
the compiled polynomial that (a) satisfies the P-side rank bound (`≤ n^200`) and (b) preserves the identity
minor for SAT-deciders (rank `≥ C(n/3, log n)`).  Asked to build it.  It cannot be built as a theorem, and this
is not merely open — the repo already **proves** it, kernel-clean: the required gauge is *uninhabited* for a
SAT-decider, because its two defining properties recreate the impossible rank sandwich.

**The gauge's two properties contradict each other on a SAT-decider.**
`IsAmplituhedronGauge` bundles `p_side_bound` (`rank(gauge(compiledPoly)) ≤ n^200`) and
`preserves_identity_minor_for_sat_deciders` (`rank(gauge(compiledPoly)) ≥ C(n/3, log n)` when `M` decides SAT).
Both bound the *same* `mlBlockedSpdpRank(gauge(compiledPoly))`, and `no_rank_sandwich_at_large_n` forbids both
at `n ≥ 2^804`.  Hence `isAmplituhedronGauge_uninhabited_for_sat_decider`: for a SAT-decider there is **no**
such gauge.  (Same shape as the raw-object refutation, one level up: the gauge cannot rescue what the raw
collapse could not do.)

**So "build Π⋆" for a machine proves that machine does not decide SAT.**  Contrapositive:
`piStar_forces_no_sat_decider` — if the gauge exists for `M`'s compilation, then `¬ DecidesSAT M`.  Building the
gauge is not a sub-lemma beneath the separation; it *is* the separation.  For an actual SAT-decider it is
provably impossible; universally, `rank_sandwich_axiom_iff_no_bounded_sat_decider` shows the gauge-sandwich
statement is *equivalent* to "no bounded SAT-decider exists".

**Therefore the God-Move route cannot be completed by proving Π⋆.**  The gauge is empty exactly where the
separation needs it (on the SAT-decider's compilation), and its universal existence is logically the separation
itself.  Discharging `AmplituhedronGaugeHyp` as a theorem = proving `P ≠ NP`, restated — and for the hard object
it is not merely unproved but provably uninhabited.

## What is proved

* **`sat_decider_admits_no_piStar`** — a SAT-decider's compilation admits no amplituhedron gauge (the repo's
  `isAmplituhedronGauge_uninhabited_for_sat_decider`, re-exposed).
* **`piStar_forces_no_sat_decider`** — if the gauge exists for `M`, then `M` does not decide SAT: building Π⋆
  *is* proving the separation for `M`.
* **`piStar_universal_iff_separation`** — the universal gauge-sandwich statement is equivalent to "no bounded
  SAT-decider": Π⋆-as-a-theorem ⟺ the separation.

## Honest verdict — Π⋆ is not a theorem-in-waiting; it is the separation, and empty where it matters

Building Π⋆ as a theorem is not a remaining lemma — it is `P ≠ NP` in gauge costume, and worse for the route: on
the SAT-decider's compilation the gauge is *provably uninhabited* (`sat_decider_admits_no_piStar`), because its
P-side bound and minor-preservation recreate the forbidden rank sandwich.  So the gauge cannot be exhibited for
the object that would matter; its existence for a machine *is* a proof that the machine does not decide SAT
(`piStar_forces_no_sat_decider`), and the universal statement is equivalent to the separation
(`piStar_universal_iff_separation`).  I did not build Π⋆, because it cannot be built as a theorem where it is
needed — the repo already proves it empty there.  The God-Move route does not reduce the separation to a
provable gauge; it repackages the separation as the gauge's existence, which is exactly `cost_super`.  Nothing
here is `P ≠ NP` (nor `P = NP`).
-/

namespace PallLean.PiStarGaugeVerdict

open PaperFaithfulSeparation TuringMachine

/-- **A SAT-decider admits no Π⋆ gauge (proved, kernel-clean).**  For a SAT-decider `M` at `n ≥ 2^804`, there is
no amplituhedron gauge on its compiled polynomial — the P-side bound and identity-minor preservation cannot both
hold (the impossible rank sandwich). -/
theorem sat_decider_admits_no_piStar
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hdec : DecidesSAT M) :
    ¬ ∃ (gauge : MvPolynomial
          (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial
          (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns gauge :=
  isAmplituhedronGauge_uninhabited_for_sat_decider M n hn hn2 htb hns hdec

/-- **Building Π⋆ for `M` proves `M` does not decide SAT (proved).**  Contrapositive of uninhabitedness: if a
gauge exists for `M`'s compilation, then `M` is not a SAT-decider.  So exhibiting the gauge *is* proving the
separation for `M`; there is no gauge to exhibit for an actual SAT-decider. -/
theorem piStar_forces_no_sat_decider
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : MvPolynomial
          (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ →ₗ[ℚ]
        MvPolynomial
          (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (hgauge : GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns gauge) :
    ¬ DecidesSAT M :=
  fun hdec => sat_decider_admits_no_piStar M n hn hn2 htb hns hdec ⟨gauge, hgauge⟩

/-- **Π⋆-as-a-theorem is equivalent to the separation (proved).**  The universal gauge-sandwich statement holds
iff no bounded SAT-decider exists — building the gauge universally *is* proving the separation, not a step
beneath it. -/
theorem piStar_universal_iff_separation :
    (∀ (M : DTM) (n : ℕ) (_ : n ≥ 2 ^ 804) (_ : n ≥ 2)
       (_ : M.timeBound ≤ 4) (_ : M.numStates ≤ n) (_ : DecidesSAT M),
       ∃ (r : ℕ), Nat.choose (n / 3) (Nat.log 2 n) ≤ r ∧ r ≤ n ^ 200) ↔
    (∀ (M : DTM) (n : ℕ) (_ : n ≥ 2 ^ 804) (_ : n ≥ 2)
       (_ : M.timeBound ≤ 4) (_ : M.numStates ≤ n),
       ¬ DecidesSAT M) :=
  rank_sandwich_axiom_iff_no_bounded_sat_decider

end PallLean.PiStarGaugeVerdict

#print axioms PallLean.PiStarGaugeVerdict.sat_decider_admits_no_piStar
#print axioms PallLean.PiStarGaugeVerdict.piStar_forces_no_sat_decider
#print axioms PallLean.PiStarGaugeVerdict.piStar_universal_iff_separation
