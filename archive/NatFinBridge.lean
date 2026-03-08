import Mathlib

open scoped BigOperators

namespace SpdpNatFinBridge

section

variable {N : Nat}

/-- Nat-level variable set for a 3-literal clause. -/
def clauseVarSetNat (v1 v2 v3 : Nat) : Finset Nat := {v1, v2, v3}

/-- Fin-level variable set, assuming in-range vars. -/
def clauseVarSetFin (v1 v2 v3 : Nat)
    (h1 : v1 < N) (h2 : v2 < N) (h3 : v3 < N) : Finset (Fin N) :=
  {⟨v1, h1⟩, ⟨v2, h2⟩, ⟨v3, h3⟩}

/-- Helper: if v < N, then Fin.mk (v % N) = Fin.mk v. -/
lemma fin_mk_mod_eq_mk (hN : 0 < N) (v : Nat) (hv : v < N) :
    (⟨v % N, Nat.mod_lt _ hN⟩ : Fin N) = ⟨v, hv⟩ := by
  exact Fin.eq_of_val_eq (Nat.mod_eq_of_lt hv)

/-- Main bridge: Nat-level disjointness + in-range → Fin-level disjointness. -/
lemma disjoint_nat_to_fin (hN : 0 < N)
    (a1 a2 a3 b1 b2 b3 : Nat)
    (ha1 : a1 < N) (ha2 : a2 < N) (ha3 : a3 < N)
    (hb1 : b1 < N) (hb2 : b2 < N) (hb3 : b3 < N)
    (hdisj : Disjoint (clauseVarSetNat a1 a2 a3) (clauseVarSetNat b1 b2 b3)) :
    Disjoint (clauseVarSetFin (N := N) a1 a2 a3 ha1 ha2 ha3)
             (clauseVarSetFin (N := N) b1 b2 b3 hb1 hb2 hb3) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro x hxA hxB
  simp only [clauseVarSetFin, Finset.mem_insert, Finset.mem_singleton] at hxA hxB
  -- x is one of {a1,a2,a3} and one of {b1,b2,b3} as Fin values
  -- Extract the Nat value and show it's in both Nat sets → contradiction
  have hnatA : x.val ∈ clauseVarSetNat a1 a2 a3 := by
    simp only [clauseVarSetNat, Finset.mem_insert, Finset.mem_singleton]
    rcases hxA with rfl | rfl | rfl <;> simp
  have hnatB : x.val ∈ clauseVarSetNat b1 b2 b3 := by
    simp only [clauseVarSetNat, Finset.mem_insert, Finset.mem_singleton]
    rcases hxB with rfl | rfl | rfl <;> simp
  exact absurd hnatB (Finset.disjoint_left.mp hdisj hnatA)

end

end SpdpNatFinBridge
