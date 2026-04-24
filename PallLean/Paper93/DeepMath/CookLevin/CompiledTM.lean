import PallLean.Paper93.DeepMath.CookLevin.CookLevinGadget

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank

/-- Tableau index: (state, symbol, time). Corresponds to one cell in the Cook-Levin
    compilation tableau for a nondeterministic Turing machine. -/
structure TableauIndex (numStates numSymbols numTimesteps : ℕ) where
  state : Fin numStates
  symbol : Fin numSymbols
  time : Fin numTimesteps

namespace TableauIndex

variable {numStates numSymbols numTimesteps : ℕ}

/-- Equivalence between `TableauIndex` and the triple product
    `Fin numStates × Fin numSymbols × Fin numTimesteps`. -/
@[simps]
def equivProd :
    TableauIndex numStates numSymbols numTimesteps ≃
      (Fin numStates × Fin numSymbols × Fin numTimesteps) where
  toFun t := (t.state, t.symbol, t.time)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by
    intro t; cases t; rfl
  right_inv := by
    intro p; rcases p with ⟨_, _, _⟩; rfl

instance instFintype :
    Fintype (TableauIndex numStates numSymbols numTimesteps) :=
  Fintype.ofEquiv _ equivProd.symm

instance instDecidableEq :
    DecidableEq (TableauIndex numStates numSymbols numTimesteps) := by
  intro t1 t2
  rcases t1 with ⟨s1, sy1, ti1⟩
  rcases t2 with ⟨s2, sy2, ti2⟩
  by_cases h1 : s1 = s2
  · by_cases h2 : sy1 = sy2
    · by_cases h3 : ti1 = ti2
      · exact isTrue (by subst h1; subst h2; subst h3; rfl)
      · exact isFalse (fun h => h3 (by cases h; rfl))
    · exact isFalse (fun h => h2 (by cases h; rfl))
  · exact isFalse (fun h => h1 (by cases h; rfl))

end TableauIndex

/-- The tableau state space has cardinality `numStates * numSymbols * numTimesteps`. -/
theorem tableauIndex_card (numStates numSymbols numTimesteps : ℕ) :
    Fintype.card (TableauIndex numStates numSymbols numTimesteps)
      = numStates * numSymbols * numTimesteps := by
  rw [Fintype.card_congr TableauIndex.equivProd]
  simp [Fintype.card_prod, Fintype.card_fin, Nat.mul_assoc]

/-- The compiled TM matrix over the tableau index: wrap `cookLevinGadget α k`
    where `k = |TableauIndex|`. -/
noncomputable def compiledTMMatrix
    (numStates numSymbols numTimesteps : ℕ) (α : ℝ) :
    Matrix (TableauIndex numStates numSymbols numTimesteps)
           (TableauIndex numStates numSymbols numTimesteps) ℝ :=
  let k := Fintype.card (TableauIndex numStates numSymbols numTimesteps)
  let e : TableauIndex numStates numSymbols numTimesteps ≃ Fin k :=
    Fintype.equivFin _
  (cookLevinGadget α k).submatrix e e

end PallLean.Paper93.DeepMath.CookLevin
