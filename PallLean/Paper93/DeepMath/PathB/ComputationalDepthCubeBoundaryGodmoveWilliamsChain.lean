import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCubeBoundaryGodmoveSymAnd

/-!
# The Williams endgame chain: three named classical theorems ⇒ `NEXP ⊄ ACC⁰`

The boundary-Godmove arc built a proved ladder of count compression — junta → symmetric-inputs → SYM∘AND — each rung
feeding `NFrameFastSAT.FastSATModel` and hence the Williams meta-theorem's speedup slot.  This file ties the ladder to
the endgame: it **discharges the `ACC⁰`-SAT speedup socket** from a faithfully-stated Beigel–Tarui reduction (using the
proved SYM∘AND count layer of `…SymAnd`), leaving the separation resting on **exactly three named classical theorems**
and nothing else.

  `HasSymAndForm` — **the Beigel–Tarui output, stated faithfully (a socket, not proved)**: every circuit in the family
        equals a `SYM ∘ (m gates)` with the count boundary subexponential, `(m+1)+1 ≤ 2^{n−budget}` (the quasipolynomial
        fan-in of the YBT normal form).  This is the deep structural reduction; it is a **hypothesis**, not proved here.
  `symAndForm_gives_speedup` — **the discharge (proved)**: from `HasSymAndForm`, the proved SYM∘AND count layer
        (`symAndModel`) manufactures a single `FastSATModel` for the whole family — so `NFrameFastSATSpeedup` (the
        speedup slot) *follows from Beigel–Tarui*; it is no longer a separate assumption.
  `nexp_not_acc0_of_bt_and_williams` — **the endgame chain (proved conditional)**: Beigel–Tarui (`HasSymAndForm`) +
        the easy-witness collapse (`EasyWitnessCollapse`) + the nondeterministic time hierarchy (`NondetTimeHierarchy`)
        ⇒ `NEXP ⊄ ACC⁰`.  The glue and the speedup are proved; the three hypotheses are the classical residue.

## Honest scope — what is and is not done

This does **not** prove `NEXP ⊄ ACC⁰`, and it does not prove any of the three deep ingredients.  Each is an established
theorem of Williams (2011) whose faithful Lean formalisation is a major library on its own:

* **Beigel–Tarui** (`HasSymAndForm` here): that an *arbitrary* `ACC⁰` circuit reduces to `SYM ∘ AND` with `m`
  quasipolynomial — the polynomial method over `ℤ_m` with degree growing to `polylog` under depth composition.  Stated
  faithfully as a hypothesis; **not proved** (the repo's open structural socket).
* **`EasyWitnessCollapse`** — the Impagliazzo–Kabanets–Wigderson easy-witness / SAT-speedup collapse.  Needs a verified
  NTM time-class + hardness-vs-randomness library.  **Not proved.**
* **`NondetTimeHierarchy`** — `NTIME[2ⁿ] ⊄ NTIME[2ⁿ/superpoly]`, classical lazy diagonalisation over nondeterministic
  time-bounded machines.  Needs a verified NTM model (deterministic diagonalisation does not suffice — nondeterministic
  classes are not closed under complement).  **Not proved.**

What is genuinely new here: the **speedup is no longer an independent assumption** — it is derived from Beigel–Tarui via
the proved count layer.  The separation now rests on exactly those three named classical theorems.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`; discharging the three sockets *is* the theorem, and this file does not do that.
-/

namespace PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveWilliamsChain

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.NFrameFastSAT
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsFastSat (fastSatWork)
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem
  (CClass EasyWitnessCollapse NondetTimeHierarchy)
open PallLean.Paper93.DeepMath.PathB.ACC0SymmetricObserver (gateCount symEval sym_count_card_le)
open PallLean.Paper93.DeepMath.PathB.ACC0ResidueObserver (observed_sat_iff)
open PallLean.Paper93.DeepMath.PathB.NFrameACC0Speedup (Satisfiable)

variable {n : ℕ} {Circuit : Type}

/-- **The Beigel–Tarui output, stated faithfully (socket, not proved).**  Every circuit `C` of the family (with truth
function `satEval C`) equals a `SYM ∘ (m gates)` circuit `symEval g h`, with the SYM-top count boundary subexponential:
`(m+1)+1 ≤ 2^{n−budget}`.  This is exactly the conclusion of the Yao–Beigel–Tarui reduction (symmetric top over `m`
quasipolynomially many `AND`s, `m + 1 < 2^n`).  Here it is a **hypothesis** — the deep reduction is not performed. -/
def HasSymAndForm (n : ℕ) (Circuit : Type) (satEval : Circuit → (Fin n → Bool) → Bool) (budget : ℕ) : Prop :=
  ∀ C, ∃ (m : ℕ) (g : Fin m → (Fin n → Bool) → Bool) (h : ℕ → Bool),
    (∀ x, satEval C x = symEval g h x) ∧ (m + 1) + 1 ≤ 2 ^ (n - budget)

/-- **The discharge (proved): Beigel–Tarui output ⇒ one fast-SAT model for the whole family.**  From `HasSymAndForm`,
each circuit's SYM∘AND form gives an `≤ m+1`-cell count table (the repo's `sym_count_card_le`), deciding SAT through the
count boundary (`observed_sat_iff`); these assemble into a single `FastSATModel` for the family. -/
noncomputable def symAndFormModel (satEval : Circuit → (Fin n → Bool) → Bool) (budget : ℕ)
    (hb : budget ≤ n) (H : HasSymAndForm n Circuit satEval budget) :
    FastSATModel n Circuit (fun C => decide (Satisfiable (satEval C))) := by
  choose m g h heq hcard using H
  exact
    { encode := fun C =>
        ⟨(Finset.univ.image (gateCount (g C))).card,
          decide (∃ c ∈ Finset.univ.image (gateCount (g C)), h C c = true)⟩
      correct := fun C => by
        have hfun : satEval C = symEval (g C) (h C) := funext (heq C)
        show decide (∃ c ∈ Finset.univ.image (gateCount (g C)), h C c = true)
            = decide (Satisfiable (satEval C))
        rw [hfun]
        exact decide_eq_decide.mpr
          (observed_sat_iff (f := symEval (g C) (h C)) (stat := gateCount (g C)) (h C) (fun _ => rfl)).symm
      budget := budget
      budget_le := hb
      work_le := fun C => by
        have hcell : (Finset.univ.image (gateCount (g C))).card + 1 ≤ (m C + 1) + 1 :=
          Nat.add_le_add_right (sym_count_card_le (g C)) 1
        simpa [fastSatWork] using le_trans hcell (hcard C) }

/-- **The speedup, derived from Beigel–Tarui (proved)**: `HasSymAndForm` yields the N-Frame fast-SAT speedup slot the
Williams meta-theorem consumes — so the speedup is no longer an independent assumption. -/
theorem symAndForm_gives_speedup (satEval : Circuit → (Fin n → Bool) → Bool) (budget : ℕ)
    (hb : budget ≤ n) (H : HasSymAndForm n Circuit satEval budget) :
    NFrameFastSATSpeedup n Circuit (fun C => decide (Satisfiable (satEval C))) :=
  ⟨symAndFormModel satEval budget hb H⟩

/-- **The Williams endgame chain (proved conditional): three named classical theorems ⇒ `NEXP ⊄ ACC⁰`.**  Beigel–Tarui
(`HasSymAndForm`, discharging the speedup via the proved count layer) together with the easy-witness collapse and the
nondeterministic time hierarchy force `NEXP ⊄ ACC⁰`.  The glue and the speedup are proved; the three hypotheses are the
classical residue and are **not** proved here. -/
theorem nexp_not_acc0_of_bt_and_williams
    (NEXP ACC0 NTIME2n NTIME2nFast : CClass)
    (satEval : Circuit → (Fin n → Bool) → Bool) (budget : ℕ) (hb : budget ≤ n)
    (bt : HasSymAndForm n Circuit satEval budget)
    (collapse : EasyWitnessCollapse NEXP ACC0 NTIME2n NTIME2nFast
      (NFrameFastSATSpeedup n Circuit (fun C => decide (Satisfiable (satEval C)))))
    (hierarchy : NondetTimeHierarchy NTIME2n NTIME2nFast) :
    ¬ (NEXP ⊆ ACC0) :=
  nframe_fastSAT_gives_separation NEXP ACC0 NTIME2n NTIME2nFast collapse hierarchy
    (symAndForm_gives_speedup satEval budget hb bt)

end PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveWilliamsChain

#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveWilliamsChain.symAndForm_gives_speedup
#print axioms PallLean.Paper93.DeepMath.PathB.CubeBoundaryGodmoveWilliamsChain.nexp_not_acc0_of_bt_and_williams
