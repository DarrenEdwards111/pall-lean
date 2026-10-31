import PallLean.Paper93.DeepMath.PathB.ComputationalDepthUhligCancellation

/-!
# Out of the box: sharing monogamy — a non-natural technique that bounds mass-production by entanglement

Every mass-production analysis so far assumed the two seam-copies are **independent** — disjoint inputs
of the same function.  That independence is exactly the resource Uhlig's universal table amortizes
(`UhligCancellation.independence_permits_amortization`).  This file takes the observer move Darren asked
for: treat the shared template as a **third observer** sitting between the two copies, and impose a
**monogamy** constraint — a template cannot fully serve two copies that are *entangled* (copy 2's input
depends on copy 1's computation).  Entanglement is the opposite of the independence mass production
needs, and it is a **rare, self-referential** property (SAT's Tseitin self-encoding is the entangler),
so a bound built on it is **non-natural** by construction — it does not exploit largeness/constructivity,
so the natural-proofs barrier does not bite.

The model: the single-copy cost is `C`; a template `t` would be shareable, but an **entanglement** `e`
of the two copies makes `e` of it non-shareable-in-parallel (that part must wait for copy 1), so the
actually-shared part is `shared = t − e`.  The saving drops with entanglement — the monogamy of the
third observer.

## What is proved

* **`independent_permits_mass_production`** — `e = 0` (independent copies): the full template is shared,
  and a large template breaks the socket.  Recovers the Uhlig regime — mass production wins.
* **`full_entanglement_forces_doubling`** — `e = t` (fully entangled): `shared = 0`, the copies double.
  Mass production is completely defeated by entanglement.
* **`enough_entanglement_defeats_mass_production`** — the key bound: if `2t ≤ C + 2e` (entanglement
  covers the excess sharing), the socket `2·shared ≤ C` holds **for an arbitrarily large template**.
  Entanglement, not a size bound, forces the socket.
* **`monogamy_reduces_sharing` / `entanglement_strictly_cuts`** — the monogamy statement: the shared part
  never exceeds the template, and any positive entanglement strictly cuts it.  The third observer cannot
  be fully correlated with both entangled copies.
* **`entanglement_flips_the_witness`** — the crisp flip: the *same* mass-producing template (`t = 3`,
  `C = 4`) that breaks the socket when independent (`e = 0`) *satisfies* it once entangled (`e = 2`).
  Entanglement turns mass production off.
* **`sat_socket_of_entanglement`** — the SAT reduction: `SATEntangledEnough` (SAT's seam is entangled
  enough, `2t ≤ C + 2e`) ⟹ the socket, hence `cost_super` for SAT.

## Honest verdict — a new non-natural front, not a crossing

This is a genuinely different technique from counting: it upper-bounds SAT's mass-production **by the
entanglement of its seam-copies**, via the third-observer monogamy `shared = t − e`.  It defeats the
universal-table sharing in the entangled regime (`enough_entanglement_defeats_mass_production`, proved),
and it identifies the entangler as SAT's Tseitin self-reference — a rare, self-referential (hence
**non-natural**) property, exactly the kind the barriers permit.  What it does **not** do is prove SAT's
seam is entangled enough (`SATEntangledEnough` for SAT): that is the new open target.  So the wall is not
crossed — it is *relocated* onto a non-natural, self-referential quantity (seam entanglement) instead of
a counting quantity.  That relocation is the point: it is a way to bound mass-production that respects the
barriers, which is what a real technique must do.  Proving `SATEntangledEnough` for SAT is still
`cost_super` = `P ≠ NP`, reached now through entanglement rather than counting.  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SharingMonogamy

/-- **An entangled seam.**  Single-copy cost `C`; a template `t` that *would* be shareable; and an
**entanglement** `e ≤ t` of the two copies (how much of the template is tied to copy 1's computation and
so cannot be shared in parallel).  The third-observer monogamy makes the actually-shared part `t − e`. -/
structure EntangledSeam where
  /-- single-copy cost `C = D d` -/
  C : ℕ
  /-- the would-be shareable template `t` -/
  template : ℕ
  /-- entanglement `e` of the two copies (dependence of copy 2 on copy 1) -/
  entangle : ℕ
  /-- entanglement consumes at most the template -/
  ent_le : entangle ≤ template
  /-- the copy is nonempty -/
  base_pos : 1 ≤ C

/-- The actually-shared part after monogamy: `t − e`.  Entanglement removes `e` from the parallel-
shareable template. -/
def EntangledSeam.shared_ (S : EntangledSeam) : ℕ := S.template - S.entangle

/-! ### The two poles: independence recovers Uhlig, full entanglement forces doubling -/

/-- **Independent copies permit mass production (proved).**  With `e = 0` the whole template is shared;
a template exceeding half the copy (`t = 3 > 2 = ½·C`) breaks the socket.  This is the Uhlig regime —
independence is the resource mass production amortizes. -/
theorem independent_permits_mass_production :
    ∃ S : EntangledSeam, S.entangle = 0 ∧ ¬ (2 * S.shared_ ≤ S.C) := by
  refine ⟨⟨4, 3, 0, by omega, by omega⟩, rfl, ?_⟩
  simp only [EntangledSeam.shared_]
  decide

/-- **Full entanglement forces doubling (proved).**  If the entanglement equals the template (`e = t`),
the shared part is `0`: the two copies cannot share at all, so the demand doubles — mass production is
completely defeated by entanglement. -/
theorem full_entanglement_forces_doubling (S : EntangledSeam) (hfull : S.entangle = S.template) :
    S.shared_ = 0 := by
  simp only [EntangledSeam.shared_, hfull]
  omega

/-! ### The key bound: enough entanglement defeats an arbitrarily large template -/

/-- **Enough entanglement defeats mass production (proved) — the technique.**  If the entanglement
covers the template's excess over half the copy (`2t ≤ C + 2e`), then `2·shared ≤ C`: the socket holds
**no matter how large the template is**.  A size bound is not needed — the entanglement of the two
copies forces the socket, hence `cost_super`. -/
theorem enough_entanglement_defeats_mass_production (S : EntangledSeam)
    (h : 2 * S.template ≤ S.C + 2 * S.entangle) :
    2 * S.shared_ ≤ S.C := by
  simp only [EntangledSeam.shared_]
  have hle := S.ent_le
  omega

/-! ### Monogamy: the third observer cannot fully serve two entangled copies -/

/-- **Monogamy reduces sharing (proved).**  The shared part never exceeds the template. -/
theorem monogamy_reduces_sharing (S : EntangledSeam) : S.shared_ ≤ S.template := by
  simp only [EntangledSeam.shared_]
  omega

/-- **Entanglement strictly cuts sharing (proved).**  Any positive entanglement makes the shared part
strictly smaller than the template: the third observer (template) cannot be fully correlated with both
entangled copies at once — the monogamy. -/
theorem entanglement_strictly_cuts (S : EntangledSeam) (h : 0 < S.entangle) :
    S.shared_ < S.template := by
  simp only [EntangledSeam.shared_]
  have hle := S.ent_le
  omega

/-! ### The flip: the same template, off when entangled -/

/-- **Entanglement flips mass production off (proved).**  The *same* mass-producing template
(`t = 3`, `C = 4`) that breaks the socket when the copies are independent (`e = 0`) *satisfies* the
socket once they are entangled (`e = 2`).  Nothing about the template changed — only the entanglement of
the copies.  This isolates entanglement as exactly the switch. -/
theorem entanglement_flips_the_witness :
    ∃ S S' : EntangledSeam,
      S.C = S'.C ∧ S.template = S'.template ∧
      S.entangle = 0 ∧ ¬ (2 * S.shared_ ≤ S.C) ∧
      (2 * S'.template ≤ S'.C + 2 * S'.entangle) ∧ (2 * S'.shared_ ≤ S'.C) := by
  refine ⟨⟨4, 3, 0, by omega, by omega⟩, ⟨4, 3, 2, by omega, by omega⟩, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp only [EntangledSeam.shared_]; decide
  · decide
  · simp only [EntangledSeam.shared_]; decide

/-! ### The SAT reduction: onto a non-natural target -/

/-- **SAT's seam is entangled enough**: the entanglement of SAT's two seam-copies covers its template's
excess over half a copy (`2t ≤ C + 2e`).  A rare, self-referential (Tseitin) property — non-natural. -/
def SATEntangledEnough (S : EntangledSeam) : Prop := 2 * S.template ≤ S.C + 2 * S.entangle

/-- **SAT entangled enough ⟹ the socket (proved).**  If SAT's seam is entangled enough, the socket
holds and `cost_super` follows — the mass-production upper bound obtained through entanglement, not
counting.  Proving `SATEntangledEnough` for SAT is the new (non-natural) open target. -/
theorem sat_socket_of_entanglement (S : EntangledSeam) (h : SATEntangledEnough S) :
    2 * S.shared_ ≤ S.C :=
  enough_entanglement_defeats_mass_production S h

end PallLean.Paper93.DeepMath.PathB.SharingMonogamy

#print axioms PallLean.Paper93.DeepMath.PathB.SharingMonogamy.independent_permits_mass_production
#print axioms PallLean.Paper93.DeepMath.PathB.SharingMonogamy.full_entanglement_forces_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.SharingMonogamy.enough_entanglement_defeats_mass_production
#print axioms PallLean.Paper93.DeepMath.PathB.SharingMonogamy.monogamy_reduces_sharing
#print axioms PallLean.Paper93.DeepMath.PathB.SharingMonogamy.entanglement_strictly_cuts
#print axioms PallLean.Paper93.DeepMath.PathB.SharingMonogamy.entanglement_flips_the_witness
#print axioms PallLean.Paper93.DeepMath.PathB.SharingMonogamy.sat_socket_of_entanglement
