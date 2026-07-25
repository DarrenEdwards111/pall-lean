# Scope: unconditional super-log **monotone** formula-depth lower bound in Lean

Goal: an explicit monotone function `f` with `mdepth f = ω(log n)` — i.e. `monotone-P ⊄ monotone-NC¹`.
This is the one direction that is **non-circular** (query→communication lifting is unconditional for
monotone KW games). Ceiling is monotone-P vs monotone-NC¹, **not** P vs NP.

## Reusable infrastructure (already in repo)
- `Khrapchenko.HasProtocol` / `formula_gives_protocol` / `protocol_gives_formula` (general KW; the
  monotone versions are direct adaptations).
- `Khrapchenko.onesOf` / `zerosOf`, `kwCC`, `kw_theorem` (general KW theorem, template for monotone).
- `ProtocolModel` (Protocol tree, transcripts, rectangle property), `InfoTheory1-8`.
- Fooling-set (KRW16), partition bound (KRW17), round-elimination skeleton (KRW19 `RoundElimStep`).

## Phase 1 — monotone model  ✅ DONE (`ComputationalDepthMonotoneKW.lean`)
- `MTree` (monotone formulas), `eval`, `dep`; `MTree.eval_mono` (axiom-free); `mdepth`.

## Phase 2 — monotone KW theorem  (easy dir DONE; ~3–5 bricks remaining, TRACTABLE)
- ✅ `HasMProtocol`, `mformula_gives_mprotocol`, `mkwCC`, `mkwCC_le_of_mformula` (easy: `mkwCC ≤ mdepth`).
- ☐ B-conv: `mprotocol_gives_mformula` — protocol ⇒ monotone formula (adapt `protocol_gives_formula`;
  Bob-node ⇒ `∧`, Alice-node ⇒ `∨`, leaf-coord `i` with `x_i=1,y_i=0` ⇒ the variable `var i`).
- ☐ B-univ: monotone universality — every monotone `f` has a monotone formula (monotone DNF over
  minimal 1-inputs), so `mdepth` is well-defined / achieved.
- ☐ B-thm: `mkw_theorem`: `mkwCC f ≤ mdepth f ≤ mkwCC f + 1` (assemble). **Clean unconditional result.**

## Phase 3 — the communication lower bound  ← THE RESEARCH CORE (hard, high risk)
Need a **deterministic** CC lower bound `ω(log n)` for an *explicit* monotone KW game. No shortcut:
fooling sets give only `Ω(log n)` (nondeterministic); super-log needs the round structure.

- **Target 3a — `st`-connectivity, `Ω(log² n)` (Karchmer–Wigderson 1988, "Fork" game).** Most
  self-contained. Sub-bricks: define `st`-conn as a monotone function on edge-indicators; reduce its
  mKW game to the Fork game on a path/tree; a progress-measure / round-elimination argument (each
  round advances `O(log n)` on a depth-`log n` structure ⇒ `Ω(log n)` rounds × `Ω(log n)` per round).
  Estimate ~15–40 bricks; **same difficulty class as the repo's already-stubbed `RoundElimStep`/GMWW.**
- **Target 3b — Raz–McKenzie lifting, `n^{Ω(1)}` monotone depth.** Stronger but heavier: a gadget
  (Indexing), a query-complexity lower bound for an explicit search problem, and the lifting
  simulation (structured/"thick" rectangles). Research-paper-scale; not recommended first.

## Recommendation
Finish **Phase 2** — it yields the clean, unconditional *monotone Karchmer–Wigderson theorem*
(`mdepth = mkwCC ± 1`), a genuine standalone result and the exact interface Phase 3 consumes.
**Phase 3 is a real multi-week research formalization** with a live risk of hitting the deterministic-
lower-bound wall (the same one `RoundElimStep` stubs). Enter it eyes-open; target 3a first.

Nothing in this programme is `P ≠ NP`. Its ceiling, fully built, is monotone-P ⊄ monotone-NC¹.
