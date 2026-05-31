import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingAssembly

/-!
# Existence of a collapsing restriction (switching lemma, step 5)

**STATUS: REAL CONDITIONAL.  THE HÅSTAD PARAMETER BALANCE IS THE EXPLICIT GATE.**

The semantic conclusion of the switching lemma, kept honest as a conditional: a
restriction with a **short canonical path** (which therefore collapses the
circuit to a shallow decision tree) **exists**, provided the bad restrictions are
outnumbered.

* `Bad` is concrete: the restrictions of a universe `U` whose canonical path
  selects `≥ s` coordinates.
* `circuit_bad_card_le` bounds `|Bad|` by `|Short| · ((2^w)^m)^numTerms`.
* A pigeonhole then gives a restriction with `< s` selected coordinates — by
  `circuitPath_decides`, fixing those `< s` coordinates already decides the
  circuit, i.e. the residual has a depth-`< s` decision tree.

The only remaining content is the **parameter inequality**
`|Short| · ((2^w)^m)^numTerms < |U|` — Håstad's balance of restriction
probability `p`, path length `s`, width `w`, and size — supplied here as an
explicit hypothesis (`hgate`).  It is a concrete `ℕ` inequality about concrete
finsets, to be discharged by the restriction-class cardinalities; it is **not**
an abstract socket, and no depth-3 lower bound is asserted unconditionally.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- **Existence of a short-canonical-path (collapsing) restriction.**  If the bad
restrictions of `U` (canonical path of length `≥ s`) are outnumbered — the
switching count `|Short| · ((2^w)^m)^numTerms` is below `|U|` — then some `ρ ∈ U`
has a canonical path of length `< s`. -/
theorem exists_short_canonical_path (ts : List (Term n)) (a : Fin n → Bool) {w m s : ℕ}
    (U : Finset (Restriction n))
    (hw : ∀ T ∈ ts, ∀ C ∈ T.clauses, C.width ≤ w) (hm : ∀ T ∈ ts, T.clauses.length ≤ m)
    (hgate : ((U.filter (fun ρ => s ≤ (circuitSel ρ ts a).card)).image
        (fun ρ => fixOn ρ (circuitSel ρ ts a) a)).card * ((2 ^ w) ^ m) ^ ts.length < U.card) :
    ∃ ρ ∈ U, (circuitSel ρ ts a).card < s := by
  have hcard : (U.filter (fun ρ => s ≤ (circuitSel ρ ts a).card)).card
      ≤ ((U.filter (fun ρ => s ≤ (circuitSel ρ ts a).card)).image
          (fun ρ => fixOn ρ (circuitSel ρ ts a) a)).card * ((2 ^ w) ^ m) ^ ts.length :=
    circuit_bad_card_le ts a (fun _ => a) hw hm (fun ρ hρ => Finset.mem_image_of_mem _ hρ)
  have hlt : (U.filter (fun ρ => s ≤ (circuitSel ρ ts a).card)).card < U.card :=
    lt_of_le_of_lt hcard hgate
  have hsplit := Finset.card_filter_add_card_filter_not (s := U)
    (p := fun ρ => s ≤ (circuitSel ρ ts a).card)
  have hpos : 0 < (U.filter (fun ρ => ¬ s ≤ (circuitSel ρ ts a).card)).card := by omega
  obtain ⟨ρ, hρ⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hρ
  exact ⟨ρ, hρ.1, not_le.mp hρ.2⟩

/-- **The short-path restriction collapses the circuit.**  For a restriction whose
canonical path selects the coordinates `circuitSel ρ ts a`, fixing exactly those
coordinates leaves every clause of every term decided (no surviving free literal).
Combined with `exists_short_canonical_path`, this exhibits a restriction fixing
`< s` coordinates that decides the whole circuit — the switching collapse. -/
theorem short_path_decides (ρ : Restriction n) (ts : List (Term n)) (a : Fin n → Bool)
    (T : Term n) (hT : T ∈ ts) (C : Clause n) (hC : C ∈ T.clauses) :
    C.lits.filter (Depth3.litFree (circuitPath ρ ts a)) = [] :=
  circuitPath_decides ρ ts a T hT C hC

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.exists_short_canonical_path
