import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseInterface

/-!
# One-step restriction of depth-3 ΣΠΣ circuits (the toy switching lemma)

**STATUS: REAL DETERMINISTIC ONE-STEP LEMMA, NOT HÅSTAD'S PROBABILISTIC LEMMA.**

The first solid piece toward the depth-3 collapse gate: a *single* restriction
step acting syntactically on a ΣΠΣ circuit.  This is fully deterministic and
fully proved.  It supplies exactly the two invariants any switching argument
iterates:

* **Semantic soundness** (`restrictCircuit_eval`): the restricted circuit computes
  the original under the extended assignment — `eval (restrict ρ D) x = eval D
  (override ρ x)`.  In particular a restriction preserves "refutes/decides"
  semantics.
* **Bottom width does not increase** (`restrictClause_width_le`): each surviving
  bottom clause is a sublist of the original, so its fan-in only drops.

Håstad's lemma — that a *random* restriction collapses a small depth-3 circuit to
a shallow decision tree with high probability — is the probabilistic statement
built on top of these deterministic steps; it is **not** proved here.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

variable {n : ℕ}

/-- Extend a partial assignment `ρ` by a total assignment `x` on the free coords. -/
def override (ρ : Fin n → Option Bool) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => (ρ i).getD (x i)

/-- The value `ρ` forces on a literal, if its variable is fixed (`none` = free). -/
def litFixedVal (ρ : Fin n → Option Bool) : Rung4Literal n → Option Bool
  | .pos i => ρ i
  | .neg i => (ρ i).map (fun b => !b)

/-- A literal's value under `override ρ x` is its forced value, or its free value. -/
theorem lit_eval_override (ρ : Fin n → Option Bool) (x : Fin n → Bool) (ℓ : Rung4Literal n) :
    ℓ.eval (override ρ x) = (litFixedVal ρ ℓ).getD (ℓ.eval x) := by
  cases ℓ with
  | pos i => simp [override, litFixedVal, Rung4Literal.eval]
  | neg i =>
    simp only [Rung4Literal.eval, override, litFixedVal]
    cases ρ i <;> simp

/-- `ρ` forces this literal true. -/
def litTrue (ρ : Fin n → Option Bool) (ℓ : Rung4Literal n) : Bool :=
  match litFixedVal ρ ℓ with | some true => true | _ => false

/-- `ρ` leaves this literal free. -/
def litFree (ρ : Fin n → Option Bool) (ℓ : Rung4Literal n) : Bool :=
  match litFixedVal ρ ℓ with | none => true | _ => false

/-- Disjunction soundness: an OR of literals under `override` is true iff some
literal is forced true or some surviving (free) literal is true. -/
theorem any_eval_override (ρ : Fin n → Option Bool) (x : Fin n → Bool)
    (lits : List (Rung4Literal n)) :
    lits.any (fun ℓ => ℓ.eval (override ρ x))
      = (lits.any (litTrue ρ) || (lits.filter (litFree ρ)).any (fun ℓ => ℓ.eval x)) := by
  induction lits with
  | nil => simp
  | cons ℓ rest ih =>
    rw [List.any_cons, lit_eval_override, ih, List.any_cons]
    cases hf : litFixedVal ρ ℓ with
    | none =>
      simp [litTrue, litFree, hf, List.filter_cons, List.any_cons,
        Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    | some b =>
      cases b with
      | true => simp [litTrue, litFree, hf]
      | false =>
        simp [litTrue, litFree, hf, List.filter_cons, List.any_cons,
          Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

/-- Restrict a bottom clause: `none` if `ρ` satisfies it (drop from the AND), else
the surviving (free-literal) clause. -/
def restrictClause (ρ : Fin n → Option Bool) (C : Clause n) : Option (Clause n) :=
  if C.lits.any (litTrue ρ) then none else some ⟨C.lits.filter (litFree ρ)⟩

/-- Clause soundness: `C` under `override` is `true` if dropped, else the surviving
clause's value. -/
theorem restrictClause_eval (ρ : Fin n → Option Bool) (x : Fin n → Bool) (C : Clause n) :
    C.eval (override ρ x) = (restrictClause ρ C).elim true (fun C' => C'.eval x) := by
  unfold Clause.eval restrictClause
  rw [any_eval_override]
  by_cases h : C.lits.any (litTrue ρ) <;> simp [h, Clause.eval]

/-- General `all`/`filterMap` collapse used at the AND level. -/
theorem all_filterMap_elim {α β : Type*} (f : α → Option β) (g : β → Bool)
    (l : List α) :
    (l.all (fun a => (f a).elim true g)) = (l.filterMap f).all g := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    rw [List.all_cons, List.filterMap_cons]
    cases f a with
    | none => simp [ih]
    | some b => rw [List.all_cons, ih]; simp

/-- Restrict a middle term: filter-map the bottom clauses (satisfied clauses drop). -/
def restrictTerm (ρ : Fin n → Option Bool) (T : Term n) : Term n :=
  ⟨T.clauses.filterMap (restrictClause ρ)⟩

/-- Term soundness. -/
theorem restrictTerm_eval (ρ : Fin n → Option Bool) (x : Fin n → Bool) (T : Term n) :
    T.eval (override ρ x) = (restrictTerm ρ T).eval x := by
  unfold Term.eval restrictTerm
  rw [show (fun C => C.eval (override ρ x))
      = (fun C => (restrictClause ρ C).elim true (fun C' => C'.eval x)) from
    funext (fun C => restrictClause_eval ρ x C)]
  exact all_filterMap_elim (restrictClause ρ) (fun C' => Clause.eval C' x) T.clauses

/-- Restrict the whole ΣΠΣ circuit (false terms evaluate false in the top OR). -/
def restrictCircuit (ρ : Fin n → Option Bool) (D : Circuit n) : Circuit n :=
  ⟨D.terms.map (restrictTerm ρ)⟩

/-- **One-step soundness.**  The restricted circuit computes the original under the
extended assignment — a restriction preserves the computed/refutation semantics. -/
theorem restrictCircuit_eval (ρ : Fin n → Option Bool) (x : Fin n → Bool) (D : Circuit n) :
    D.eval (override ρ x) = (restrictCircuit ρ D).eval x := by
  unfold Circuit.eval restrictCircuit
  rw [show (fun T => T.eval (override ρ x)) = (fun T : Term n => (restrictTerm ρ T).eval x) from
    funext (fun T => restrictTerm_eval ρ x T), List.any_map]
  rfl

/-- **Bottom fan-in does not increase.**  Each surviving bottom clause is a sublist
of the original, so its width only drops. -/
theorem restrictClause_width_le (ρ : Fin n → Option Bool) (C : Clause n) :
    (restrictClause ρ C).elim 0 Clause.width ≤ C.width := by
  unfold restrictClause Clause.width
  by_cases h : C.lits.any (litTrue ρ) <;> simp [h]
  exact List.length_filter_le _ _

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.restrictCircuit_eval
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.restrictClause_width_le
