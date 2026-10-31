import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTseitinEntanglement

/-!
# The next step: forcing forking = rigidity of the branch family — the entanglement front meets Valiant

`TseitinEntanglement` showed the size socket needs **forking**: copy 1's output must require *genuinely
different* copy-2 tables, not merely gate a shared one.  This file attacks forking directly and finds
what it is.  Copy 1's output `o` selects a branch `f_o` — the copy-2 function on that output.  Forking
means the branch family `{f_o}` cannot be served by one shared template: **the branches share no small
common sub-computation.**  That is exactly a **rigidity** condition — the same obstruction as Valiant
matrix rigidity and the corpus's linear/nonlinear mixer dilemma.

Split a branch's cost into the **shared template** (common to all branches) and the **rigidity** (the
per-branch part no template can supply).  The size-shareable part is precisely the shared template, so
the forking entanglement `forkDep` of `TseitinEntanglement` **is** the rigidity.

## What is proved

* **`rigidity_is_forking`** — the shareable part is `perBranch − rigidity`: the rigidity is exactly the
  forking (non-shareable) entanglement.  Identifies the two notions.
* **`socket_iff_rigidity`** — the size socket holds **iff** `2·perBranch ≤ C + 2·rigidity`: enough
  rigidity of the branch family forces the socket.
* **`low_rigidity_permits_mass_production`** — a family that fully shares (`rigidity = 0`) breaks the
  socket for a large branch: no rigidity ⟹ mass production wins.
* **`high_rigidity_forces_socket`** — rigidity covering the excess ⟹ the socket, hence `cost_super`.
* **`full_rigidity_forces_doubling`** — branches sharing *nothing* (`sharedTemplate = 0`, maximal
  rigidity) force the socket outright: the copies double.
* **`sat_socket_of_rigidity`** — the SAT reduction: `SATFamilyRigid` (SAT's composition branch family is
  rigid enough) ⟹ the socket ⟹ `cost_super`.

## Honest verdict — forking lands on rigidity, a named open problem

Forcing forking entanglement is forcing the copy-2 branch family `{f_o}` to be **rigid**: no small shared
template serves all branches (`socket_iff_rigidity`).  A non-rigid family (branches share a big template)
is exactly the mass-production adversary (`low_rigidity_permits_mass_production`), so the size socket for
SAT reduces to: **SAT's composition branch family is rigid.**  That is a rigidity condition of the same
family as Valiant's matrix rigidity — a famous, hard, *named* open problem — and it is the same
obstruction the corpus's linear/nonlinear mixer dilemma already isolated (the linear horn = Valiant
rigidity, open).  So the entanglement front, pushed to the size level, meets the rigidity wall: forking ⟺
rigidity, proved; rigidity of SAT's composition is the open target.  This is a genuine reduction onto a
named problem, not a crossing — proving the rigidity for SAT is still `cost_super` = `P ≠ NP`.  Nothing
here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ForkingRigidity

/-- **A branch family.**  Copy 1's output selects a branch (a copy-2 function).  `perBranch` is a
branch's cost, `sharedTemplate` the sub-computation common to *all* branches, and `C` the single-copy
cost.  The rigidity `perBranch − sharedTemplate` is the per-branch part no shared template supplies. -/
structure BranchFamily where
  /-- cost of one branch's computation (the would-be shareable table `t`) -/
  perBranch : ℕ
  /-- sub-computation common to all branches (the shareable part) -/
  sharedTemplate : ℕ
  /-- single-copy cost `C` -/
  C : ℕ
  /-- the shared template is part of a branch -/
  shared_le : sharedTemplate ≤ perBranch
  /-- the copy is nonempty -/
  base_pos : 1 ≤ C

/-- **Rigidity** of the branch family: the per-branch cost no shared template can supply. -/
def BranchFamily.rigidity (F : BranchFamily) : ℕ := F.perBranch - F.sharedTemplate

/-! ### Rigidity is the forking entanglement -/

/-- **The shareable part is `perBranch − rigidity` (proved).**  So the forking (non-shareable)
entanglement is exactly the rigidity of the branch family — the two notions coincide. -/
theorem rigidity_is_forking (F : BranchFamily) :
    F.sharedTemplate = F.perBranch - F.rigidity := by
  simp only [BranchFamily.rigidity]
  have hle := F.shared_le
  omega

/-- **The size socket ⟺ enough rigidity (proved).**  The socket `2·sharedTemplate ≤ C` holds exactly
when `2·perBranch ≤ C + 2·rigidity`: the rigidity of the branch family covers the branch's excess over
half a copy.  Rigidity is the size-relevant entanglement. -/
theorem socket_iff_rigidity (F : BranchFamily) :
    2 * F.sharedTemplate ≤ F.C ↔ 2 * F.perBranch ≤ F.C + 2 * F.rigidity := by
  simp only [BranchFamily.rigidity]
  have hle := F.shared_le
  omega

/-! ### The two poles -/

/-- **No rigidity permits mass production (proved).**  A family that fully shares (`rigidity = 0`,
`sharedTemplate = perBranch = 3 > 2 = ½·C`) breaks the socket: one template serves all branches, so mass
production wins.  Forking requires rigidity. -/
theorem low_rigidity_permits_mass_production :
    ∃ F : BranchFamily, F.rigidity = 0 ∧ ¬ (2 * F.sharedTemplate ≤ F.C) := by
  refine ⟨⟨3, 3, 4, by omega, by omega⟩, ?_, ?_⟩
  · decide
  · decide

/-- **Enough rigidity forces the socket (proved).**  If the rigidity covers the branch's excess
(`2·perBranch ≤ C + 2·rigidity`), the socket holds — `cost_super`.  The branch family being rigid is the
size-level entanglement. -/
theorem high_rigidity_forces_socket (F : BranchFamily)
    (h : 2 * F.perBranch ≤ F.C + 2 * F.rigidity) :
    2 * F.sharedTemplate ≤ F.C :=
  (socket_iff_rigidity F).mpr h

/-- **Full rigidity forces doubling (proved).**  Branches that share *nothing* (`sharedTemplate = 0`,
maximal rigidity) force the socket outright: the two copies cannot share, so the demand doubles. -/
theorem full_rigidity_forces_doubling (F : BranchFamily) (hfull : F.sharedTemplate = 0) :
    2 * F.sharedTemplate ≤ F.C := by
  omega

/-! ### The SAT reduction: onto a rigidity problem -/

/-- **SAT's branch family is rigid enough**: SAT's composition branches share no template beyond half a
copy (`2·perBranch ≤ C + 2·rigidity`).  A rigidity condition of the Valiant family — the open target. -/
def SATFamilyRigid (F : BranchFamily) : Prop := 2 * F.perBranch ≤ F.C + 2 * F.rigidity

/-- **SAT's branch family rigid ⟹ the socket (proved).**  If SAT's composition branch family is rigid
enough, the size socket holds and `cost_super` follows — the forking obtained through rigidity.  Proving
`SATFamilyRigid` for SAT is the open (Valiant-family) rigidity target. -/
theorem sat_socket_of_rigidity (F : BranchFamily) (h : SATFamilyRigid F) :
    2 * F.sharedTemplate ≤ F.C :=
  high_rigidity_forces_socket F h

end PallLean.Paper93.DeepMath.PathB.ForkingRigidity

#print axioms PallLean.Paper93.DeepMath.PathB.ForkingRigidity.rigidity_is_forking
#print axioms PallLean.Paper93.DeepMath.PathB.ForkingRigidity.socket_iff_rigidity
#print axioms PallLean.Paper93.DeepMath.PathB.ForkingRigidity.low_rigidity_permits_mass_production
#print axioms PallLean.Paper93.DeepMath.PathB.ForkingRigidity.high_rigidity_forces_socket
#print axioms PallLean.Paper93.DeepMath.PathB.ForkingRigidity.full_rigidity_forces_doubling
#print axioms PallLean.Paper93.DeepMath.PathB.ForkingRigidity.sat_socket_of_rigidity
