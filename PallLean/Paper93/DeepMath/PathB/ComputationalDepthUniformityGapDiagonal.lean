import PallLean.Paper93.DeepMath.PathB.ComputationalDepthComposableMachine

/-!
# The uniformity gap, machine side: faithful `P` provably misses a length language

The circuit route's two targets straddle a *uniformity* gap: the non-uniform target
(`∀ k, ∃ n, n^k + k < cbudget (SATFamily n)`) demands a bound against ALL circuit
families, while the uniform target (`SAT ∉ P`, i.e. `¬ InP SATLang`) only demands a
bound against circuit families a `ComposableMachine` can generate.  This file proves the
machine side of the strictness of that gap: **the faithful uniform `P` misses some
language whose fixed-length slices are constant functions** — the classic
length-language (sparse/advice) witness, machine-checked against THIS repository's
`ComposableMachine.InP`, not an abstract machine predicate.

## The argument

* `lengthLang A` (`w ↦ A |w|`) reads only the input length through an arbitrary oracle
  `A : ℕ → Bool`; the map `A ↦ lengthLang A` is injective (`lengthLang_injective`).
* Every machine is behaviourally canonicalized to state space `Fin k`
  (`toData` / `ofData`, simulation proved step-by-step: `step_toData`, `run_toData`,
  `decides_toData`) — the same transport discipline as the `comp` simulation lemmas of
  `ComposableMachine`, so nothing is hidden in an "up to iso" phrase.
* A machine determines a *clock-free* language (`langOf`, accept-at-first-halt;
  `decides_langOf`: any language it decides under any polynomial clock IS `langOf`).
  This kills the trap that `Decides M L T` mentions the uncountable clock `T`.
* Canonical machine data `Σ k, FinMachineData k` is countable (finitely many machines
  per state count); a Cantor diagonal (`no_injection_to_nat`, self-contained via
  `Function.invFun`) then forces some `lengthLang A` outside `InP`
  (`exists_lengthLang_not_inP`).
* Non-vacuity: `inP_lengthLang_true` — the constant-true length language IS in `InP`
  (a one-state machine decides it with clock `0`), so the family straddles the class.

## Honest scope

This is the classic countability/advice separation (folklore since the 1970s), not new
mathematics — the point is that it is now MACHINE-CHECKED against the repository's
faithful `InP`, so "the uniformity gap is strict" can be a *theorem* of the corpus
(completed on the circuit side in `UniformityGapNamed`, where the missed language is
shown to have polynomial — indeed constant — `cbudget` slices).  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-! ### Length languages -/

/-- The **length language** of an oracle `A : ℕ → Bool`: membership depends only on the
input's length.  Its fixed-length slices are constant functions — the classic witness
that non-uniform capture is blind to uniformity. -/
def lengthLang (A : ℕ → Bool) : List Bool → Bool := fun w => A w.length

/-- Distinct oracles give distinct length languages (evaluate on `List.replicate`). -/
theorem lengthLang_injective : Function.Injective lengthLang := by
  intro A B h
  funext m
  have hm := congrFun h (List.replicate m false)
  simpa [lengthLang] using hm

/-! ### Canonical machines: state space `Fin k` -/

/-- Raw data of a machine over state space `Fin k`: start state, halt flag, transition
table, accept flag.  A plain product type, so countability is by instance search. -/
abbrev FinMachineData (k : ℕ) : Type :=
  Fin k × (Fin k → Bool) × (Fin k → Bool → Fin k × Option Bool × Move) × (Fin k → Bool)

/-- Realize canonical data as an actual `Machine`. -/
def ofData {k : ℕ} (N : FinMachineData k) : Machine where
  State := Fin k
  fin := inferInstance
  dec := inferInstance
  start := N.1
  halt := N.2.1
  δ := N.2.2.1
  accept := N.2.2.2

/-- The canonical state indexing of a machine (finiteness is the `Machine.fin` field). -/
noncomputable def stateEquiv (M : Machine) : M.State ≃ Fin (Fintype.card M.State) :=
  Fintype.equivFin M.State

/-- Canonicalize a machine to `Fin k` states by transporting all four components along
`stateEquiv`. -/
noncomputable def toData (M : Machine) : FinMachineData (Fintype.card M.State) :=
  (stateEquiv M M.start,
   fun s => M.halt ((stateEquiv M).symm s),
   fun s b => (stateEquiv M (M.δ ((stateEquiv M).symm s) b).1,
               (M.δ ((stateEquiv M).symm s) b).2.1,
               (M.δ ((stateEquiv M).symm s) b).2.2),
   fun s => M.accept ((stateEquiv M).symm s))

/-- Transport a configuration along the canonicalization. -/
noncomputable def mapCfg (M : Machine) (c : Cfg M) : Cfg (ofData (toData M)) :=
  ⟨stateEquiv M c.st, c.hd, c.tp⟩

/-- **One-step simulation**: the canonical machine mirrors `M` exactly. -/
theorem step_toData (M : Machine) (c : Cfg M) :
    step (ofData (toData M)) (mapCfg M c) = mapCfg M (step M c) := by
  have key : ∀ s : M.State, (stateEquiv M).symm (stateEquiv M s) = s :=
    fun s => Equiv.symm_apply_apply _ s
  by_cases h : M.halt c.st = true
  · have h' : (ofData (toData M)).halt (mapCfg M c).st = true := by
      show M.halt ((stateEquiv M).symm (stateEquiv M c.st)) = true
      rw [key]; exact h
    rw [step_of_halted _ h', step_of_halted _ h]
  · simp only [Bool.not_eq_true] at h
    have h' : (ofData (toData M)).halt (mapCfg M c).st = false := by
      show M.halt ((stateEquiv M).symm (stateEquiv M c.st)) = false
      rw [key]; exact h
    unfold step
    rw [h, h']
    simp only [Bool.false_eq_true, if_false]
    show (⟨stateEquiv M (M.δ ((stateEquiv M).symm (stateEquiv M c.st))
              (c.tp.getD c.hd false)).1,
           moveHead c.hd (M.δ ((stateEquiv M).symm (stateEquiv M c.st))
              (c.tp.getD c.hd false)).2.2,
           (match (M.δ ((stateEquiv M).symm (stateEquiv M c.st))
              (c.tp.getD c.hd false)).2.1 with
             | none => c.tp
             | some w => writeAt c.tp c.hd w)⟩ : Cfg (ofData (toData M)))
        = ⟨stateEquiv M (M.δ c.st (c.tp.getD c.hd false)).1,
           moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2,
           (match (M.δ c.st (c.tp.getD c.hd false)).2.1 with
             | none => c.tp
             | some w => writeAt c.tp c.hd w)⟩
    rw [key]

/-- The forced initial configurations correspond. -/
theorem init_toData (M : Machine) (x : List Bool) :
    init (ofData (toData M)) x = mapCfg M (init M x) := rfl

/-- **Run simulation**: the canonical machine's run mirrors `M`'s run. -/
theorem run_toData (M : Machine) (x : List Bool) (t : ℕ) :
    run (ofData (toData M)) t (init (ofData (toData M)) x)
      = mapCfg M (run M t (init M x)) := by
  induction t with
  | zero => exact init_toData M x
  | succ t ih => rw [run_succ, ih, step_toData, ← run_succ]

/-- **Decision transport**: whatever `M` decides, its canonicalization decides — with
the same clock. -/
theorem decides_toData {M : Machine} {L : List Bool → Bool} {T : ℕ → ℕ}
    (hDec : Decides M L T) : Decides (ofData (toData M)) L T := by
  intro x
  obtain ⟨hHalt, hOut⟩ := hDec x
  refine ⟨?_, ?_⟩
  · show (ofData (toData M)).halt
        (run (ofData (toData M)) (T x.length) (init (ofData (toData M)) x)).st = true
    rw [run_toData]
    show M.halt ((stateEquiv M).symm
        (stateEquiv M (run M (T x.length) (init M x)).st)) = true
    rw [Equiv.symm_apply_apply]
    exact hHalt
  · show (ofData (toData M)).accept
        (run (ofData (toData M)) (T x.length) (init (ofData (toData M)) x)).st = L x
    rw [run_toData]
    show M.accept ((stateEquiv M).symm
        (stateEquiv M (run M (T x.length) (init M x)).st)) = L x
    rw [Equiv.symm_apply_apply]
    exact hOut

/-! ### The clock-free language of a machine -/

/-- The language a machine determines, clock-free: accept at the FIRST halting time
(default `false` if it never halts).  This removes the clock `T` from the countability
argument — `Decides M L T` mentions an arbitrary `T : ℕ → ℕ`, of which there are
uncountably many, but the decided language depends on `M` alone. -/
noncomputable def langOf (M : Machine) : List Bool → Bool := fun x =>
  if h : ∃ t, HaltsBy M x t then M.accept (run M (Nat.find h) (init M x)).st else false

/-- Any language `M` decides under any clock IS `langOf M` (halting is stable, so the
decision read at the clock equals the decision read at the first halt). -/
theorem decides_langOf {M : Machine} {L : List Bool → Bool} {T : ℕ → ℕ}
    (hDec : Decides M L T) : L = langOf M := by
  funext x
  obtain ⟨hHalt, hOut⟩ := hDec x
  have hex : ∃ t, HaltsBy M x t := ⟨T x.length, hHalt⟩
  have hle : Nat.find hex ≤ T x.length := Nat.find_le hHalt
  have hspec : HaltsBy M x (Nat.find hex) := Nat.find_spec hex
  have hstab : run M (T x.length) (init M x) = run M (Nat.find hex) (init M x) :=
    run_stable M x hle hspec
  calc L x = decideOut M x (T x.length) := hOut.symm
    _ = M.accept (run M (T x.length) (init M x)).st := rfl
    _ = M.accept (run M (Nat.find hex) (init M x)).st := by rw [hstab]
    _ = langOf M x := by
        show _ = if h : ∃ t, HaltsBy M x t
            then M.accept (run M (Nat.find h) (init M x)).st else false
        rw [dif_pos hex]

/-! ### Countability and the Cantor diagonal -/

/-- **Every `InP` language is `langOf` of a canonical machine.**  This is the
countable-parameterization step: `Σ k, FinMachineData k` is countable, and the clock
has been eliminated. -/
theorem inP_lang_canonical {L : List Bool → Bool} (h : InP L) :
    ∃ p : Σ k, FinMachineData k, L = langOf (ofData p.2) := by
  obtain ⟨M, T, _hT, hDec⟩ := h
  exact ⟨⟨Fintype.card M.State, toData M⟩, decides_langOf (decides_toData hDec)⟩

/-- **Cantor, self-contained**: no injection of `ℕ → Bool` into `ℕ`.  (Diagonalize
through the partial inverse `Function.invFun`.) -/
theorem no_injection_to_nat (f : (ℕ → Bool) → ℕ) : ¬ Function.Injective f := by
  intro hf
  have hgf : ∀ A, Function.invFun f (f A) = A :=
    fun A => Function.leftInverse_invFun hf A
  set D : ℕ → Bool := fun n => ! Function.invFun f n n with hD
  have h1 : D (f D) = ! Function.invFun f (f D) (f D) := rfl
  rw [hgf D] at h1
  cases hDb : D (f D) with
  | false => rw [hDb] at h1; exact Bool.noConfusion h1
  | true => rw [hDb] at h1; exact Bool.noConfusion h1

/-- **The diagonal**: some length language is outside the faithful uniform `P`.
If every `lengthLang A` were in `InP`, the injective chain
`(ℕ → Bool) ↪ length languages ↪ canonical machine data ↪ ℕ`
would contradict Cantor. -/
theorem exists_lengthLang_not_inP : ∃ A : ℕ → Bool, ¬ InP (lengthLang A) := by
  by_contra hall
  push_neg at hall
  have hchoice : ∀ A : ℕ → Bool,
      ∃ p : Σ k, FinMachineData k, lengthLang A = langOf (ofData p.2) :=
    fun A => inP_lang_canonical (hall A)
  choose Φ hΦ using hchoice
  have hΦinj : Function.Injective Φ := by
    intro A B hAB
    apply lengthLang_injective
    rw [hΦ A, hΦ B, hAB]
  obtain ⟨g, hg⟩ := (countable_iff_exists_injective (Σ k, FinMachineData k)).mp
    inferInstance
  exact no_injection_to_nat (g ∘ Φ) (hg.comp hΦinj)

/-! ### Non-vacuity: the family straddles the class -/

/-- A one-state machine: halts immediately, accepts everything. -/
def trivialTrue : Machine where
  State := Fin 1
  fin := inferInstance
  dec := inferInstance
  start := 0
  halt := fun _ => true
  δ := fun s _ => (s, none, (2 : Move))
  accept := fun _ => true

/-- The constant-true length language IS in the faithful `P` (clock `0`): the length
family is not disjoint from `InP` — the diagonal misses the class, not the family. -/
theorem inP_lengthLang_true : InP (lengthLang (fun _ => true)) :=
  ⟨trivialTrue, fun _ => 0, ⟨1, 0, fun _ => by simp⟩, fun _ => ⟨rfl, rfl⟩⟩

end PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal

#print axioms PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal.decides_langOf
#print axioms PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal.exists_lengthLang_not_inP
#print axioms PallLean.Paper93.DeepMath.PathB.UniformityGapDiagonal.inP_lengthLang_true
