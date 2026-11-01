# Phase 4 — G4 (Def. 12 measure and easy-function ceiling)

Cycle run 01 Nov 2026, 06:05–07:05 GMT (box clock). Branch `research/gap-g4` (from research/gap-g3 45ab9a05),
worktree `/workspace/pvsnp/wt-g4`. Content commits:
* **63bbb2da** (G4-a);
* **98659ea8** (D3 subset lower bound and D4 Lemma 18 family);
* **417c32a6** (D7 row ceiling, D8/D9 4^{κ+ℓ} comparison);
* the final commit (D10 rename monotonicity, D11 odd-length headline, docs). Its hash is in the commit log and the
  report. Tags: [K] kernel-checked, [C] computed (exact unless marked mod-p), [I] informal argument, [O] open.
**Nothing here proves or claims P ≠ NP or P = NP.** No other branch or worktree was modified, and no PR was opened.

Lean file: `research-audits/gap-g4/Def12Measure.lean`. It imports only Mathlib, and checking it takes about 11 s:
`cd pall-lean && lake env lean <path>`. It contains no `sorry`, `native_decide` or `axiom`. All 22 `#print axioms`
outputs are `[propext, Classical.choice, Quot.sound]` or a subset of it; `choose_two_mul_le` uses only
`[propext, Quot.sound]` (log `def12_axioms.log`).

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
| D7 | `Def12Measure.def12Rank_le_rowCeiling` | ∀ c B κ ℓ p, `IsMultilinear p → def12Rank c B κ ℓ p ≤ C(N,κ) · Σ_{j≤ℓ} C(N,j)` (`IsMultilinear` copied verbatim from MultilinearSPDP l.25–27) | — | [K]. **New** as a Lean theorem; standard content (the effective rows are (S,U)). Ingredients are also [K]: `pderivMulti_eq_zero_of_not_ml` (a repeated variable gives 0), `dropML_monomial_mul_eq_zero`, `reduceML_monomial_mul` |
| D8 | `Def12Measure.multilinear_le_ratio_mul_subset` | on N = m+m with κ ≤ m: `Γ(p)·[C(m,κ)Σ_{j≤ℓ}C(m,j)] ≤ [C(2m,κ)Σ_{j≤ℓ}C(2m,j)]·Γ(subsetPoly m κ)` for multilinear p | subsetPoly | [K]. **New** |
| D9 | `Def12Measure.multilinear_le_four_pow_mul_subset` | on N = m+m with 3κ ≤ 2m and 3ℓ ≤ 2m: `IsMultilinear p → def12Rank c B κ ℓ p ≤ 4^(κ+ℓ) · def12Rank c B κ ℓ (subsetPoly m κ)`, both conventions, every partition. Uses `choose_two_mul_le : 3j ≤ 2m → C(2m,j) ≤ 4^j C(m,j)` | subsetPoly | [K]. **New, headline:** at κ = ℓ = ⌊log₂ N⌋ the factor is ≤ N⁴ |
| D10 | `Def12Measure.def12Rank_le_rename` | `def12Rank c B κ ℓ p ≤ def12Rank c B' κ ℓ (rename Fin.castSucc p)` for all p (not only multilinear), all partitions B and B'. Supporting lemma `convML_rename`: drop and reduce commute with the renaming | — | [K]. **New**. This is G3-A transfer property (c), previously [I] (G3.0), now proven for the embedding Fin N ↪ Fin (N+1) |
| D11 | `Def12Measure.multilinear_le_four_pow_mul_subset_odd` | on N = m+m+1 with 3κ ≤ 2m and 3ℓ ≤ 2m: `IsMultilinear p → def12Rank c B' κ ℓ p ≤ 4^(κ+ℓ+1) · def12Rank c B' κ ℓ (rename castSucc (subsetPoly m κ))` | subsetPoly ignoring the last bit | [K]. **New.** It covers the branch's lengths: `unitSourceLength n'` = (2n'+1) + 2·Σ_i(3 + \|encodeVar' i\|) is always odd (15, 31, 49, …) |
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
   * **[K] ceiling:** D7 gives Γ(p) ≤ C(N,κ)·Σ_{j≤ℓ}C(N,j) for every multilinear p. Random functions attain it exactly
     whenever rows < cols ([C]: N = 8…15, κ = 1).
   * **[K] comparison:** D9 (even N) and D11 (odd N) give Γ(p) ≤ 4^{κ+ℓ}·Γ(easy) and Γ(p) ≤ 4^{κ+ℓ+1}·Γ(easy),
     whenever 3κ, 3ℓ ≤ 2⌊N/2⌋.
   * **The true ratio [C]** at κ = ℓ = log₂N is ≈ 1.05·N²: N = 32, 128, 512, 2048 give ratios 1626, 21647, 296806 and
     4402746, against N² = 1024, 16384, 262144 and 4194304.
   * **Consequence (extends C1–C4 to Def. 12, now fully kernel-checked):** the SAT MLE `languageCharacteristic SATLang L`
     on L = `unitSourceLength (n/3)` bits is multilinear ([I]: it is the interpolation polynomial; in the branch,
     `normalize_isMultilinear`). It therefore satisfies Γ^{Def12}(SAT_L) ≤ 4^{κ+ℓ+1}·Γ^{Def12}(easy_L). At
     κ = ℓ = ⌊log₂ n⌋ this is ≤ 4·n⁴·Γ(easy_L) (L = unitSourceLength(n/3) ≥ 15·(n/3) ≫ log₂ n, so 3κ, 3ℓ ≤ 2⌊L/2⌋ holds throughout the paper window n ≥ 2^804 [I]). **No rank threshold
     separates SAT from a linear-time function by more than a polynomial factor under Def. 12**, in either convention.
     Under the Lean measure the factor was n (C1–C4).
   * **Only remaining [I] links:**
     * SAT_L is multilinear. This holds by construction, but our `IsMultilinear` is a local copy, so it cannot be
       linked to the branch's constant without importing the branch chain.
     * "easy" means linear time (G4.3 item 7).
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
   * D3, D7 and D9–D11 are kernel-checked statements that kill the "Def. 12 rescues the measure" route.
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
9. **Ceiling: now [K]** (D7, D9, D11). Check: the hypotheses 3κ ≤ 2m and 3ℓ ≤ 2m are needed only for the clean
   factor 4^j in `choose_two_mul_le`. D8 holds for any κ ≤ m. Boundary: κ = ℓ = 0 gives Γ(p) ≤ 1·Γ(easy) with
   Γ(easy) ≥ 1, which is consistent with Γ(p) ≤ 1 from D7.
10. **No known failed assumption is reintroduced.** Nothing assumes Lemma 18, the shift restriction or the refuted
    gadget axioms.
11. **SAT port fidelity:** `decodeNat`, `decodeVar'` (with Mathlib `Nat.pair`), `decodeLit'`, `decodeClause'` and
    `decodeFormula'` were ported line by line from ComputationalDepthCookLevinEmitCodec.lean @21921958. `wordOfFin`
    is assumed to list a 0..L−1 in order; this was not re-verified against its Lean definition [I]. `Satisfiable`
    uses a brute force over the occurring variables, and an empty clause means unsatisfiable. The data is
    guidance only.
12. **Mod-p entries:** at N = 12, κ = 2, the SAT and SUBSET entries are lower bounds; this is marked in the table.

## G4.4 Next actions
1. **Done this cycle:** the row ceiling (D7) and the comparisons (D9, D11).
2. (optional) A formal link to the branch: state D11 for `languageCharacteristic SATLang (unitSourceLength n)` inside
   the 21921958 import chain, using the trimmed build of G3.7. That needs the branch's `IsMultilinear`/interpolate
   lemma, and the box can do it in about 4 min.
3. (optional) Formalise `#colSet N D = Σ_{j≤D} C(N,j)` to get D2 as an equality.
4. (optional) Model f as a `ComposableMachine` at 21921958 (like `scanner`) to make "easy" formal.
5. The project-level recommendation is unchanged (G3.5 / NO_GO_STATUS.md): the architecture is blocked on all known
   routes. Under both the Lean measure and Def. 12, the SAT MLE is within poly(n) of a linear-time function.

## G4.6 (01 Nov 2026 09:05 GMT) Kernel link to the branch SAT characteristic
`G4SATLink.lean` (build: `build_link.sh`; log `link_axioms.log`). Theorems `satChar_isMultilinear`, `satChar_def12_le_even`,
`satChar_def12_le_odd`, `satChar_def12_le_easy`, and `satChar_def12_le_easy_paper`: for n ≥ 128, L = unitSourceLength(n/3), κ = ℓ = ⌊log₂ n⌋,
every partition, both conventions, Γ^{Def12}(languageCharacteristic SATLang L) ≤ 4·n⁴·Γ^{Def12}(embedded subsetPoly). Axioms are clean.
This closes the multilinearity [I] link of G4.2.

## G4.4 item 3 done (01 Nov 2026 15:xx GMT)
* New [K] `ColSetCount.lean` (imports Def12Measure only; Mathlib): `card_colSet`: #colSet N D = Σ_{j≤D} C(N,j) for all N, D;
  `def12Rank_le_binomialSum`: Γ^{Def12}_{κ,ℓ}(p) ≤ Σ_{j ≤ deg p+ℓ−κ} C(N,j) for every field, convention, partition, p.
  Axioms: [propext, Classical.choice, Quot.sound] (log `colset_axioms.log`). Sanity: N=3, D=1 gives 4 = {∅,{0},{1},{2}}.
* Formal hygiene only: it does not bear on the missing implication. Remaining optional: item 4 (ComposableMachine for subsetPoly).

## G4.4 item 4 (01 Nov 2026 18:20 GMT): `ComposableMachine` model of the "easy" function
File `SubsetMachine.lean` (build: `build_subset_machine.sh`; log `subset_machine_axioms.log`, 24 `#print axioms`, all ⊆
[propext, Classical.choice, Quot.sound]; no sorry, no native_decide; three `decide` boundary examples only). Statements are
about the branch's own `PallLean.Paper93.DeepMath.PathB.ComposableMachine.{Machine, Decides, InP}` @21921958 and
`G4SATLink.easyEven` (checked with pp.fullNames).
* **[K] Model fact `decides_append_false`:** `Decides M L T → ∀ x, L (x ++ [false]) = L x` (any clock), and
  `decides_append_replicate_false`. Reason: blank cells read `false` and `init` writes no end marker, so a run on x and on
  x ++ [false] has identical states (`run_rel`). Example: `evenLength_not_decided`.
* **[K] Negative (new finding): the G4.3 item-7 claim is FALSE in the branch's model.** `no_decider_has_easyEven_char_family`:
  for every schedule κ(m) and every m₁ ≥ 1 with κ(m₁) ≤ m₁, no `ComposableMachine` with any clock decides a language whose
  `languageCharacteristic` equals `easyEven` at length 2m₁ (parameter κ(m₁)) and at length 4m₁ (parameter κ(2m₁)).
  Corollaries: `no_decider_has_easyEven_char` (any fixed κ, all even lengths) and `_log` (κ = ⌊log₂ m⌋). Proof: pad an
  m₁-point with 2m₁ zeros; the y-block becomes empty, so the padded value is [κ(2m₁) = 0] for both a value-1 and a value-0
  point. Non-vacuity: `easyEven_char_exists` (a classical language with characteristic exactly `easyEven` at every even length).
  The block layout f(x,y) = [|y| = κ ∧ y ⊆ x] is linear-time only for TMs that can see the input length.
* **[K] Positive in-model replacement:** `contMachine` (6 states, no writes) decides `contLang` (triples (c,x,y): accept at the
  first c = 0, including blanks; reject at the first y ∧ ¬x) within `|w| + 3` steps (`cont_decides`, `contSteps_le`);
  `contLang_inP : ComposableMachine.InP contLang`. Boundary cases (empty word, odd tails, reject in 1st or 2nd triple) are kernel `decide`d.
* **[C] Def. 12 rank of χ_contLang:** `cont_check.py` → `cont_check.jsonl`, N = 3..12, κ ≤ min(m,3), ℓ ≤ 2, both conventions:
  Γ ≥ C(m,κ)·Σ_{j≤ℓ}C(m,j) (m = ⌊N/3⌋) in all cases (0 violations; usually far above).
* **[I] Proof sketch for the missing lower bound:** rows x^A·∂_{x_S}χ (|S| = κ, |A| ≤ ℓ). The y-degree-κ part of each row is
  x^A y^S c_0⋯c_{max S} (Σ_{k>max S} C_k telescopes). Those monomials are distinct and higher-y-degree terms cannot cancel them,
  under both conventions, so the rows are independent.
* **[C] SAT is consistent with the model fact:** SATLang(w ++ [false]) = SATLang(w) for all 131071 words with |w| ≤ 16 (`sat_pad.py`,
  Python port of the codec). So the model restriction does not make `SAT_not_in_P` vacuous at these sizes. A Lean proof is open.
* **Not proved:** (a) the Def. 12 lower bound for `languageCharacteristic contLang L` and hence the in-model corollary
  "Γ^{Def12}(SAT_L) ≤ poly(n)·Γ^{Def12}(χ of an InP language)". (b) SATLang padding invariance in Lean.
* **Consequence for the G4 headline:** "SAT within poly(n) of a linear-time function" holds for standard (length-aware) TMs.
  Inside the branch's `ComposableMachine` model, the comparison function `easyEven` is not even decidable. The in-model version
  needs (a). Under the Lean (not Def. 12) measure, the branch's own `scanner` already gives the in-model binomial minor.
