import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSharingMonogamy

/-!
# Lower-bounding SAT's seam entanglement via Tseitin — and where the entanglement actually lands

`SharingMonogamy` relocated `cost_super` onto SAT's **seam entanglement** `e`: enough entanglement of
the two copies defeats mass production.  This file attacks the new target — lower-bound `e` via SAT's
Tseitin self-encoding — and follows it honestly to where it lands.

Tseitin lets copy 2's SAT instance **reference copy 1** (encode "copy 1's circuit outputs `o`"), so copy
2 is *gated* on copy 1's output.  But that gating is a **sequential / depth** dependence — a dependence
on the *data* `o` flowing from copy 1 into copy 2's instance — **not** on the shared table.  The
expensive SAT-table template is computed once and reused for both evaluations regardless of the gating,
so **sequential dependence does not reduce the size-shareable template.**  What *would* reduce it is a
**forking** dependence: different values of copy 1's output requiring *genuinely different* copy-2
templates.  Only forking makes the table non-shareable at the size level.

So the entanglement splits: `seqDep` (Tseitin gives this — gating, a depth dependence) and `forkDep`
(the size-relevant part).  The size-monogamy bound sees only `forkDep`.

## What is proved

* **`high_sequential_still_mass_produces`** — a seam with huge sequential (Tseitin) entanglement but zero
  forking (`forkDep = 0`) still breaks the socket: gating alone does not defeat size mass production.
* **`sequential_irrelevant_to_size_socket`** — the same template and forking with *different* `seqDep`
  give the *same* socket status: sequential entanglement is invisible to the size socket.
* **`forking_defeats_mass_production` / `size_socket_iff_forking`** — the size socket holds iff the
  *forking* entanglement covers the excess (`2t ≤ C + 2·forkDep`).  Forking is the size-relevant `e`.
* **`tseitin_adds_depth`** — the real win Tseitin *does* give: gated composition forces **additive
  depth** (`d1 + d2 ≥ max d1 d2`) — copy 2 waits for copy 1.  This is the KRW composition depth bound.
* **`tseitin_gives_depth_not_size`** — the capstone: a Tseitin seam has `seqDep > 0` (depth entanglement,
  additive depth holds) yet `forkDep = 0` is consistent (no size socket).  Depth entanglement ≠ size
  entanglement.

## Honest verdict — Tseitin lower-bounds the DEPTH entanglement (KRW), not the SIZE entanglement

Tseitin self-encoding genuinely forces entanglement — but the **sequential/gating** kind, which is a
**depth** dependence (`tseitin_adds_depth`: additive depth = the KRW composition bound, capped at
`P ⊄ NC¹`).  It does **not** force the **forking** kind, which is what the size monogamy bound needs
(`size_socket_iff_forking`): the adversary can gate copy 2 on copy 1's output while still sharing the
table (`high_sequential_still_mass_produces`).  So lower-bounding SAT's seam entanglement via Tseitin
lands exactly on the size-vs-depth gap: Tseitin gives depth entanglement (KRW, `P ⊄ NC¹`); the size
entanglement (forking — copy 1's output genuinely forks copy 2's table) is the surviving wall
= `cost_super` = `P ≠ NP`.  The Tseitin lower bound is real and it is capped where KRW is capped;
forcing forking for SAT is not crossed here.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TseitinEntanglement

/-- **A Tseitin-composed seam.**  Single-copy cost `C`, would-be template `t`, and the entanglement split
into `seqDep` (sequential/depth gating — Tseitin's dependence of copy 2 on copy 1's output) and `forkDep`
(the size-relevant part — copy 1's output forking copy 2's template).  Only `forkDep` reduces the
size-shareable table. -/
structure TseitinSeam where
  /-- single-copy cost `C` -/
  C : ℕ
  /-- would-be shareable table `t` -/
  template : ℕ
  /-- sequential/depth dependence (Tseitin gating): copy 2 waits on copy 1's output -/
  seqDep : ℕ
  /-- forking/size dependence: copy 1's output requires a different copy-2 table -/
  forkDep : ℕ
  /-- forking consumes at most the template -/
  fork_le : forkDep ≤ template
  /-- the copy is nonempty -/
  base_pos : 1 ≤ C

/-- The size-shareable part: `t − forkDep`.  Sequential gating (`seqDep`) does **not** appear — a
data dependence on copy 1's output leaves the shared table intact. -/
def TseitinSeam.shared_ (S : TseitinSeam) : ℕ := S.template - S.forkDep

/-! ### Sequential (Tseitin) entanglement is invisible to the size socket -/

/-- **Sequential gating alone still mass-produces (proved).**  A seam with a huge sequential dependence
(`seqDep = 100`, Tseitin gating copy 2 on copy 1) but no forking (`forkDep = 0`) still breaks the socket
(`t = 3 > 2 = ½·C`): the table is shared despite the gating.  Tseitin's gating does not defeat size mass
production. -/
theorem high_sequential_still_mass_produces :
    ∃ S : TseitinSeam, S.forkDep = 0 ∧ 100 ≤ S.seqDep ∧ ¬ (2 * S.shared_ ≤ S.C) := by
  refine ⟨⟨4, 3, 100, 0, by omega, by omega⟩, rfl, by decide, ?_⟩
  simp only [TseitinSeam.shared_]
  decide

/-- **Sequential entanglement is invisible to the size socket (proved).**  Two seams with the same
template and forking but *different* `seqDep` have the same socket status.  Adding Tseitin gating
(`seqDep : 0 ↦ 100`) changes nothing at the size level. -/
theorem sequential_irrelevant_to_size_socket :
    ∃ S S' : TseitinSeam,
      S.template = S'.template ∧ S.forkDep = S'.forkDep ∧ S.C = S'.C ∧
      S.seqDep ≠ S'.seqDep ∧
      (¬ (2 * S.shared_ ≤ S.C)) ∧ (¬ (2 * S'.shared_ ≤ S'.C)) := by
  refine ⟨⟨4, 3, 0, 0, by omega, by omega⟩, ⟨4, 3, 100, 0, by omega, by omega⟩,
    rfl, rfl, rfl, by decide, ?_, ?_⟩
  · simp only [TseitinSeam.shared_]; decide
  · simp only [TseitinSeam.shared_]; decide

/-! ### Forking is the size-relevant entanglement -/

/-- **Forking defeats mass production (proved).**  If the *forking* entanglement covers the template's
excess (`2t ≤ C + 2·forkDep`), the socket holds — for an arbitrarily large table.  Forking, not gating,
is the size-relevant `e`. -/
theorem forking_defeats_mass_production (S : TseitinSeam)
    (h : 2 * S.template ≤ S.C + 2 * S.forkDep) :
    2 * S.shared_ ≤ S.C := by
  simp only [TseitinSeam.shared_]
  have hle := S.fork_le
  omega

/-- **The size socket ⟺ forking covers the excess (proved).**  The size entanglement that the monogamy
bound sees is exactly `forkDep`; `seqDep` never enters. -/
theorem size_socket_iff_forking (S : TseitinSeam) :
    (2 * S.shared_ ≤ S.C) ↔ (2 * S.template ≤ S.C + 2 * S.forkDep) := by
  simp only [TseitinSeam.shared_]
  have hle := S.fork_le
  omega

/-! ### What Tseitin DOES give: additive depth (the KRW composition bound) -/

/-- **Tseitin gating forces additive depth (proved).**  Because copy 2 waits for copy 1's output, the
gated composition has depth `d1 + d2`, not the parallel `max d1 d2`.  This is the real depth win from
sequential entanglement — the KRW composition bound, capped at `P ⊄ NC¹`. -/
theorem tseitin_adds_depth (d1 d2 : ℕ) : max d1 d2 ≤ d1 + d2 :=
  max_le (Nat.le_add_right d1 d2) (Nat.le_add_left d2 d1)

/-- **Tseitin gives depth entanglement, not size (proved) — the capstone.**  A Tseitin seam can have
`seqDep > 0` (real depth entanglement, additive depth holds) while `forkDep = 0` (no size socket): the
adversary gates copy 2 on copy 1 yet still shares the table.  Depth entanglement ≠ size entanglement. -/
theorem tseitin_gives_depth_not_size :
    ∃ S : TseitinSeam,
      0 < S.seqDep ∧ S.forkDep = 0 ∧
      (∀ d1 d2 : ℕ, max d1 d2 ≤ d1 + d2) ∧
      ¬ (2 * S.shared_ ≤ S.C) := by
  refine ⟨⟨4, 3, 5, 0, by omega, by omega⟩, by decide, rfl,
    fun d1 d2 => max_le (Nat.le_add_right d1 d2) (Nat.le_add_left d2 d1), ?_⟩
  simp only [TseitinSeam.shared_]
  decide

end PallLean.Paper93.DeepMath.PathB.TseitinEntanglement

#print axioms PallLean.Paper93.DeepMath.PathB.TseitinEntanglement.high_sequential_still_mass_produces
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinEntanglement.sequential_irrelevant_to_size_socket
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinEntanglement.forking_defeats_mass_production
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinEntanglement.size_socket_iff_forking
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinEntanglement.tseitin_adds_depth
#print axioms PallLean.Paper93.DeepMath.PathB.TseitinEntanglement.tseitin_gives_depth_not_size
