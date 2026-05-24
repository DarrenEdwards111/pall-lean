/-
# Computational-depth (K^t) framing of P vs NP  — DEFINITIONS + one honest direction

Renders, in Lean, the computational-depth form of P vs NP obtained from the
N-frame observer-boundedness chapter (Edwards, *The Observer-Centric Universe*,
Ch. 4 §4.2 — the conscious observer as a computationally bounded agent) via
time-bounded Kolmogorov complexity K^t.

Picture (faithful translation, NOT a proof):
  * CORRECT OBJECT (important): a *single* satisfying assignment is only `n` bits,
    so K^t(a|φ) ≤ n + O(1) for any budget — it can NEVER be superpolynomially
    deep.  The right object is therefore the UNIFORM WITNESS-FINDING MAP across
    input lengths (the search function φ ↦ witness), the family-level object where
    K^t / MCSP / MINKT / easy-witness transport actually live — NOT the depth of
    one assignment.  (`ShallowSearch` below quantifies a single producer over ALL
    lengths, so it captures this map, not a single string.)
  * The observer's poly-time bound is the budget `t` in K^t.  "The less the
    constraint, the more it can see" = a stronger uniform compressor/decompressor
    finds witnesses at more lengths.
  * SHALLOW search = ONE uniform poly-budget producer outputs satisfying
    assignments at every length (P-side; the search function lies in FP).
  * DEEP search = no such producer (= ¬Shallow).  **This is the search form of
    P ≠ NP.**  OPEN; proved nowhere here; no axiom stands in for it.

HONEST STATUS:
  * `decider_of_shallow` proves the EASY, TRUE direction (Shallow ⇒ a decider
    exists: produce, then verify).  Clean axiom profile.
  * The converse (decider ⇒ Shallow) is classical Cook self-reducibility; it is
    deliberately NOT formalized (to avoid a `sorry`), only noted.  Together they
    give Shallow ⟺ P = NP (search form).
  * `DepthSeparation` only NAMES the target (:= `DeepSearch`); it is neither
    asserted nor proved.  Writing this file does NOT advance P vs NP.

Standalone: no imports.  A specification of the frontier object, not a result.
-/

namespace SATDepth

/-- Assignments to `n` Boolean variables. -/
abbrev Assignment (n : Nat) := Fin n → Bool

/-- A length-`n` SAT instance: a decidable satisfaction predicate (poly-time
verifier, kept abstract). -/
structure Instance (n : Nat) where
  Sat    : Assignment n → Prop
  decSat : DecidablePred Sat

attribute [instance] Instance.decSat

/-- φ is satisfiable. -/
@[reducible] def Satisfiable {n : Nat} (φ : Instance n) : Prop := ∃ a, φ.Sat a

/-- A uniform producer: at every length it maps an instance to a candidate
assignment.  `budget` records the (polynomial) step budget; the content is that
one fixed procedure works at every length — the K^poly-bounded "decompressor". -/
structure Producer where
  run    : (n : Nat) → Instance n → Assignment n
  budget : Nat → Nat

/-- SHALLOW search: some uniform producer outputs a *satisfying* assignment for
every satisfiable instance of the family `F`.  K^poly-shallow / P-side. -/
def ShallowSearch (F : (n : Nat) → Instance n) : Prop :=
  ∃ P : Producer, ∀ n : Nat, Satisfiable (F n) → (F n).Sat (P.run n (F n))

/-- A Boolean decider is correct for the family `F`. -/
def Decides (F : (n : Nat) → Instance n) (D : Nat → Bool) : Prop :=
  ∀ n : Nat, (D n = true ↔ Satisfiable (F n))

/-- EASY, TRUE direction of search/decision: a shallow producer yields a correct
decider (run the producer, then verify its output).  The honest provable half. -/
theorem decider_of_shallow (F : (n : Nat) → Instance n)
    (h : ShallowSearch F) : ∃ D : Nat → Bool, Decides F D := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun n => decide ((F n).Sat (P.run n (F n))), ?_⟩
  intro n
  show decide ((F n).Sat (P.run n (F n))) = true ↔ Satisfiable (F n)
  rw [decide_eq_true_eq]
  exact ⟨fun hwin => ⟨P.run n (F n), hwin⟩, fun hsat => hP n hsat⟩

/-- DEEP search: no uniform producer finds satisfying assignments — the K^poly
depth of SAT search is unbounded.  **This is the search form of P ≠ NP.**
OPEN: no theorem here proves it and no axiom stands in for it. -/
def DeepSearch (F : (n : Nat) → Instance n) : Prop := ¬ ShallowSearch F

/-- Names the separation target.  It is *definitionally* `DeepSearch`, i.e. it is
P ≠ NP (search form) itself — neither asserted nor proved here. -/
def DepthSeparation (F : (n : Nat) → Instance n) : Prop := DeepSearch F

/-- `DepthSeparation` is definitionally the open lower bound, so it cannot be
discharged without proving the separation. -/
theorem depthSeparation_iff_deep (F : (n : Nat) → Instance n) :
    DepthSeparation F ↔ DeepSearch F := Iff.rfl

end SATDepth

#print axioms SATDepth.decider_of_shallow
#print axioms SATDepth.depthSeparation_iff_deep
