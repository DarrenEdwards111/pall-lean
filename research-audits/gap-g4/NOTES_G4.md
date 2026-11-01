# Phase 4 — G4 (Def. 12 measure and easy-function ceiling)

Cycle run 01 Nov 2026, 06:05–08:40 GMT. Branch `research/gap-g4` (from research/gap-g3 45ab9a05), worktree
`/workspace/pvsnp/wt-g4`. Content commits **63bbb2da** (G4-a) and **98659ea8** (G4-b + Lemma 18 family); the notes
commit follows. Tags: [K] kernel-checked, [C] computed (exact unless marked mod-p), [I] informal argument, [O] open.
**Nothing here proves or claims P ≠ NP or P = NP.** No other branch or worktree was modified, and no PR was opened.

Lean file: `research-audits/gap-g4/Def12Measure.lean`. It imports only Mathlib, and checking it takes about 11 s:
`cd pall-lean && lake env lean <path>`. It contains no `sorry`, `native_decide` or `axiom`. All 14 `#print axioms`
outputs are exactly `[propext, Classical.choice, Quot.sound]` (log `def12_axioms.log`).

## G4.0 Current lemma / reading of Def. 12
* **Paper text** (arXiv v5, p. 31–32, paper.txt lines 1509–1525) is quoted verbatim in the file header.
* **Formalisation:**
  * `def12Rank c B κ ℓ p = if deg p + ℓ < κ then 0 else finrank (span def12Rows)`.
  * The rows are `colRestrict D (convML c (monomial u 1 * pderivMulti τ p))` for every `τ : Fin N →₀ ℕ` and
    `u : Fin N →₀ ℕ`, with `weight τ = κ` (exactly κ, repeats allowed), the literal block condition
    `(blockSupport B τ).card ≤ κ`, and `weight u ≤ ℓ` (any monomial in all N variables).
  * `D = deg p + ℓ − κ` (ℕ-subtraction, which equals the paper's max{0,·}).
  * `c ∈ {drop, reduce}`: `drop` is the repository's `mlProj` (copied verbatim), and `reduce` is x^a ↦ x^{min(a,1)}.
  * `∂^τ` is the iterated derivative along `(toMultiset τ).toList`. The order does not matter, by `pderiv_comm` and
    `iterDerivList_perm` [K].
* **Block condition:** vacuous (`blockCondition_vacuous` [K]).
* **Column condition:** harmless (`row_colRestrict_eq` [K]: every row already lies in the columns). Both the
  "monomials of deg ≤ D" and the "multilinear monomials of deg ≤ D" readings give the same rank, since after drop or
  reduce every row is multilinear.
* **`finrank` is the genuine matrix rank:** `def12Span_finiteDimensional` [K]. `def12Rank_le_columns` [K] bounds the
  rank by #columns.
* **Repeated variables:** for multilinear p, any τ with some τ_i ≥ 2 gives ∂^τ p = 0, and under drop any non-multilinear
  u gives 0. So the effective rows are (S, U) with |S| = κ and U multilinear, |U| ≤ ℓ [I; standard, not formalised].
* **Lean measure:** restated locally **verbatim**. `BlockPartition`, `isBlockAdmissible` and `iterDerivList` come from
  SPDPDefs.lean l.24–29, 104–107. `Finsupp.IsMultilinear`, `mlProjHom`, `mlProj`, `mlBlockedSpdpSubspace` and
  `mlBlockedSpdpRank` come from MultilinearSPDP.lean l.30–31, 81–88, 118–131, with `Classical.dec` as in l.20.
  The reason is that MultilinearSPDP imports NPWitness, Compiler, IdentityMinor and LowDegAnnihilation (non-Mathlib).
  **Caveat:** the comparison theorem is about the local copy. Fidelity rests on the textual copy, not on a kernel link
  to `SPDP.mlBlockedSpdpRank`.

## G4.1 Results table
| # | Lean name | exact statement | witness | status / known? |
|---|---|---|---|---|
| D1 | `Def12Measure.lean_le_def12_drop` | ∀ N F B κ ℓ p, `mlBlockedSpdpRank B κ ℓ p ≤ def12Rank .drop B κ ℓ p` (strict Lean measure, every partition, every p) | — | [K] 63bbb2da. **New** as a theorem; the content was stated [I] in G3.4 |
| D2 | `Def12Measure.and_def12_lower` | ∀ c B κ (h : κ ≤ N), `Σ_{j∈range(κ+1)} C(N,j) ≤ def12Rank c B κ κ (andPoly κ h)`, with `andPoly_eq_prod : andPoly κ h = ∏ i:Fin κ, X (castLE h i)` = x₁⋯x_κ | AND monomial | [K] 63bbb2da, both conventions. **New** (G3.4 had it [C] only at N=6,8). Equality "= Σ" is [C]+[I]: the upper bound is `def12Rank_le_columns`, but #colSet = Σ is not formalised |
| D3 | `Def12Measure.subset_def12_lower` | ∀ c B κ ℓ m (hκ : κ ≤ m), `C(m,κ) · Σ_{j≤ℓ} C(m,j) ≤ def12Rank c B κ ℓ (subsetPoly m κ)` on N = m+m variables, where `subsetPoly m κ = Σ_{S⊆[m],|S|=κ} x^S · δ_S(y)` and δ_S(y) = ∏_{j∈S} y_j ∏_{j∉S}(1−y_j) | f(x,y) = [\|y\| = κ ∧ y ≤ x], a single linear scan | [K] 98659ea8, both conventions, every partition, every field. **New** |
| D4 | `Def12Measure.lemma18_fails_subset_family` | ∀ c B m (4 ≤ m), `C(2m,1)·2¹ < def12Rank c B 1 1 (subsetPoly m 1)` | subsetPoly m 1 (a Boolean characteristic polynomial) | [K] 98659ea8. **New:** an infinite family of Boolean counterexamples to paper Lemma 18. The single instance x₁+x₂x₃ was known (G3.3) |
| D5 | `pderiv_comm`, `iterDerivList_perm`, `pderivMulti_ofList`, `coeff_pderiv`, `support_iterDerivList`, `iterDerivList_eq_zero_of_lt`, `row_colRestrict_eq`, `blockCondition_vacuous`, `def12Span_finiteDimensional`, `def12Rank_le_columns`, `card_small_finsets`, `pderivMulti_subsetPoly` | infrastructure; e.g. `pderivMulti (xExp S) (subsetPoly m κ) = delta S` for \|S\| = κ | — | [K]. Mathlib-level facts (commuting partials and degree drop are standard), new as Lean lemmas here |
| D6 | (script) `scripts/gap_g4/check_subset_mle.py` | subsetPoly m κ = χ_f (Def. 13) exactly, for all m ≤ 5, κ ≤ m | — | [C] (integer Möbius transform); the general identity is [I] (product of MLEs on disjoint variables) |

**Computed ranks [C]** (`scripts/gap_g4/def12_rank.py`, FLINT exact `fmpz_mat.rank`; "modp" means the rank mod
2⁶¹−1, which is a lower bound on the rank over ℚ and is exact when it meets a ceiling). κ = ℓ; data in
`sweep_*.jsonl` / `sweep_subset.txt`. Ceiling = min(rows C(N,κ)·Σ_{j≤ℓ}C(N,j), cols Σ_{j≤D}C(N,j)).

| N | κ=ℓ | Lean | SUBSET drop/red | SCANNER drop/red | MAJ drop/red | IP drop/red | PARITY drop/red | SAT_N drop/red | RAND drop/red | row ceiling | proven LB (D3) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 8 | 1 | 16 max | 62/52 | 42/42 | 44/36 | 36/54 | 37/37 | 22/22 | 72/72 | 72 | 20 |
| 10 | 1 | 20 max | 95/80 | 63/63 | 65/55 | 55/85 | 56/56 | 65/38 | 110/110 | 110 | 30 |
| 10 | 2 | 180 max | 871/766 | 450/449 | 550/385 | 386/691 | 386/386 | 467/168 | 1024/1024 (cols) | 2520 | 160 |
| 12 | 1 | 24 max | 135/114 | 88/88 | — | — | — | 123/104 | 156/156 | 156 | 42 |
| 12 | 2 | 264 max | ≥2246/≥1821 (modp) | 933/932 | — | — | — | ≥1625/≥926 (modp) | 4096 (cols) | 5214 | 330 |
| **15** | 1 | 30 max | 196/168 | 133/133 | — | — | — | **202/190** | 240/240 | 240 | 56 (m=7) |

SAT_N is `languageCharacteristic SATLang N`, an exact Python port of the branch's `decodeFormula'` coordinate codec
and `Satisfiable`. **N = 15 = `unitSourceLength 1` is exactly the branch's source length at n/3 = 1**, so the row
`SAT_15` is the smallest faithful instance of `machineSource_eq_SATCharacteristic` (unitSourceLength = 15, 31, 49 for
n/3 = 1, 2, 3). At larger lengths the exact SAT MLE is out of reach (2^31 truth-table entries).

## G4.2 Verdict (G4-b answer)
1. **Yes. A linear-time function reaches the Def. 12 ceiling up to a polynomial factor, in both conventions.**
   * **[K] lower bound:** D3 gives Γ(subsetPoly) ≥ C(m,κ)·Σ_{j≤ℓ}C(m,j) with N = 2m.
   * **[I] ceiling:** for every multilinear p on N variables, Γ^{Def12}_{κ,ℓ}(p) ≤ C(N,κ)·Σ_{j≤ℓ}C(N,j), because the
     effective rows are as in G4.0. Random functions attain it exactly whenever rows < cols ([C]: N = 8…15, κ = 1).
   * **Gap:** the ratio is Π_{i<κ}(2m−i)/(m−i) · Σ_{j≤ℓ}C(2m,j)/Σ_{j≤ℓ}C(m,j) ≤ 4^{κ+ℓ} for κ, ℓ ≤ m/2 [I]. At
     κ = ℓ = log₂N it is ≈ 1.05·N² (computed: N = 32, 128, 512, 2048 give ratios 1626, 21647, 296806, 4402746 against
     N² = 1024, 16384, 262144, 4194304).
   * **Consequence (extends C1–C4 to Def. 12) [K lower + I upper]:** every multilinear p, including the SAT MLE on
     `unitInputLength` bits, satisfies Γ^{Def12}(p) ≤ ~4^{κ+ℓ}·Γ^{Def12}(subsetPoly) = n^{O(1)}·Γ(easy). So **no rank
     threshold separates SAT from linear-time functions by more than a polynomial factor under Def. 12 either.** At
     κ = ℓ = ⌊log₂ n⌋ the factor is n^{O(1)}, against n under the Lean measure (C1–C4).
   * When N is odd (e.g. 15), use subsetPoly on N−1 variables plus one dummy variable. Rank does not decrease when a
     variable is added, because the rows embed [I].
2. **Where SAT sits [C, tiny sizes only]:**
   * At the branch's real smallest length (N = 15, κ = ℓ = 1), SAT_15 has rank 202 (drop) / 190 (reduce), against a
     ceiling of 240, SUBSET 196/168, SCANNER 133/133, and a Lean measure ≤ 30.
   * At N = 10–12 the SAT MLE lies between SCANNER and SUBSET.
   * SAT is not above the easy functions by any visible margin. These sizes are guidance only; the asymptotic statement
     is item 1.
3. **Which easy functions do NOT reach the ceiling:**
   * AND: Def12-drop rank = Lean rank (G3-C item 3).
   * Under reduce, OR (= 1 − ∏(1 − x_i)) also collapses to the AND value: OR-reduce = AND = 7, 22 at N = 6 and 9, 37 at N = 8, for κ = 1, 2.
   * PARITY, MAJ, IP and SCANNER sit at a constant fraction of the ceiling at small N. Asymptotics: [O], and not
     needed since SUBSET suffices.
4. **Milestone:**
   * D3 is a kernel-checked statement that kills the "Def. 12 rescues the measure" route for the upper-bound direction.
     Under the paper's own Def. 12, a linear-time Boolean function already has quasi-polynomial rank
     n^{Θ(log n)}·…, within poly(n) of the maximum over all functions. A P-side bound "poly-time ⇒ Γ^{Def12} ≤ n^{O(1)}"
     is **refuted** by D3 (C(m,κ) ≥ (m/κ)^κ is superpolynomial at κ = log m). The NP-side bound cannot exceed the
     easy value by more than poly(n) [I-ceiling].
   * D4 strengthens the Lemma 18 refutation from one polynomial to an infinite Boolean family.
   * D3 is also a much stronger Def. 12 counterexample to the "P-side small rank" claims than x₁⋯x_κ (D2). For example,
     at N = 128, κ = ℓ = 7, D3 gives ≥ 4.4·10¹⁷, against Lemma 18's claimed ceiling C(128,7)·2⁷ ≈ 1.2·10¹³.

## G4.3 Attempts / counterexamples / adversarial review (G4-c)
Review of each formal statement against paper.txt and the informal claim:
1. **D1 is the strict-κ Lean measure only.** The inclusive `…Inc` variant is not compared, and Def. 12 is strict
   anyway. Fidelity of the local Lean copy is textual, see G4.0 (**downgrade noted**). Lean ≤ Def12-reduce is **not**
   claimed in general. It holds for multilinear p [I], because then Lean rows u·∂_S p with vars(u) ⊆ S are already
   multilinear, so drop and reduce agree. For non-multilinear p it is unproven.
2. **"deg p" = `totalDegree p` of the unreduced p.** For non-multilinear p the paper might mean the degree after
   reduction. That would only shrink D. `row_colRestrict_eq` uses totalDegree, so for non-multilinear p under that
   alternative reading the column restriction could cut rows. All p in D2–D4 are multilinear, so they are unaffected.
3. **Field:** all theorems hold over every field F, a superset of the paper's "char 0 or p > poly(n)". No
   characteristic assumption is hidden; the coefficients that appear are 1.
4. **Boundary parameters:**
   * κ = 0: D2 gives Γ_{0,0}(1) ≥ 1 (correct, = 1). D3 gives Γ_{0,ℓ}(∏(1−y_j)) ≥ Σ_{j≤ℓ}C(m,j) (correct).
   * ℓ = 0: D3 gives C(m,κ) ≤ Γ (correct: the distinct δ_S are independent).
   * κ = 1, 2 are covered by the sweeps, and all computed ranks satisfy D3's bound (no violations in any jsonl).
   * m = 0 / N = 0: D3 with κ = 0 gives 1 ≤ Γ(1) = 1. D2 with N = κ = 0 is fine.
   * κ > N or κ > m is excluded by hypothesis (otherwise the bound is 0 anyway).
   * Degree guard: D3 proves it does not fire (the derivative is nonzero). D2 uses deg(andPoly) = κ.
5. **Off-by-one checks:**
   * `Finset.range (ℓ+1)` is j ≤ ℓ.
   * `D = deg p + ℓ − κ` uses ℕ-subtraction, matching max{0,·}.
   * D4 uses C(2m,1)·2¹ = 4m < m(m+1) ⇔ m ≥ 4. The m = 3 boundary gives 12 = 12, which is not a violation, so the
     hypothesis is tight.
6. **Vacuity:** none of D1–D4 has a hypothesis that could be unsatisfiable. D1 has none, and D2–D4 only need κ ≤ N or
   κ ≤ m (D4 needs m ≥ 4).
7. **"Easy" is [I]:** f(x,y) = [|y| = κ ∧ y ≤ x] is computed by one pass (count the 1s of y and check y_j → x_j),
   which is O(N) time. κ = ⌊log₂ n⌋ is computable from the length, so the family is one uniform linear-time language
   [I]. This is not formalised as a `ComposableMachine`, unlike the branch's scanner.
8. **subsetPoly = χ_f** is [C] for m ≤ 5 and [I] in general. The theorem D3 itself is about the polynomial, so it
   holds regardless.
9. **The ceiling (item G4.2.1) is [I], not [K].** This is the one informal link in "SAT ≤ poly · easy under Def. 12".
   Next action: formalise it.
10. **No known failed assumption is reintroduced.** Nothing assumes Lemma 18, the shift restriction or the refuted
    gadget axioms.
11. **SAT port fidelity:** `decodeNat`, `decodeVar'` (with Mathlib `Nat.pair`), `decodeLit'`, `decodeClause'` and
    `decodeFormula'` were ported line by line from ComputationalDepthCookLevinEmitCodec.lean @21921958. `wordOfFin`
    is assumed to list a 0..L−1 in order; this was not re-verified against its Lean definition [I]. `Satisfiable`
    uses a brute force over the occurring variables, and an empty clause means unsatisfiable. The data is
    guidance only.
12. **Mod-p entries:** at N = 12, κ = 2, the SAT and SUBSET entries are lower bounds; this is marked in the table.

## G4.4 Next actions
1. (small, [K] target) Formalise the row ceiling: for multilinear p, Γ^{Def12}_{κ,ℓ}(p) ≤ C(N,κ)·Σ_{j≤ℓ}C(N,j). Then
   "SAT ≤ 4^{κ+ℓ}·subset" becomes fully kernel-checked. Ingredients: τ with a repeat gives 0, non-multilinear u is
   killed (drop) or reduced (reduce), and a span-of-indexed-family cardinality bound.
2. (optional) Formalise `#colSet N D = Σ_{j≤D} C(N,j)` to get D2 as an equality.
3. (optional) Model f as a `ComposableMachine` at 21921958 (like `scanner`) to make "easy" formal.
4. The project-level recommendation is unchanged (G3.5 / NO_GO_STATUS.md): the architecture is blocked on all known
   routes. Under both the Lean measure and Def. 12, the SAT MLE is within poly(n) of a linear-time function.
