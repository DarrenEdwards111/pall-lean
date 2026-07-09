# Constructing the NP-hard, shortcut-free residual family — how far it actually goes

*The hard-residual socket's last fence is `not_easy_linear_payload`: a residual family that is provably
NP-hard **and** provably shortcut-free (no P-solver decides it without distinguishing the exponentially many
labels). This note does the construction honestly. The **NP-hard** half is built concretely below. The
**shortcut-free** half is proved to be **exactly `P ≠ NP`** — so it cannot be discharged by any construction,
only by the theorem. Nothing here is `P ≠ NP`.*

---

## 1. The concrete NP-hard residual family (this part is real)

Fix a family of 3-CNF formulas `{φ_n}` on `n` variables. Split the variables of `φ_n` into an **address
block** `A = {x_1,…,x_m}` (`m = m(n)`) and a **data block** `B = {x_{m+1},…,x_n}` (`k = n−m`).

- **Instance map.** For `a ∈ {0,1}^m`, `instanceOf(a) := φ_n|_a` — the 3-CNF on `B` obtained by fixing `A`
  to `a`. (A distinct, poly-size sub-formula for each `a`.)
- **Label map.** `label(a) := a`.
- **FoolingResidualFamily.** The `2^m` instances have `2^m` distinct labels; `label` is injective. ✔
- **NP-hardness.** `φ_n ∈ SAT ⟺ ∃ a, φ_n|_a ∈ SAT`, and deciding SAT of the residuals is 3-SAT restricted
  to these instances. Choosing `{φ_n}` to range over all 3-CNFs makes the family **NP-complete**. ✔

So `HardSATResidualFamily.fam`, `label_injective`, and `residual_semantics`/`np_complete_payload` are all
**genuinely dischargeable** — the NP-hard family is a real, concrete object.

## 2. The shortcut-free predicate

`not_easy_linear_payload` = **shortcut-free against general P**:

> There is **no** polynomial-time algorithm `D` that correctly decides SAT of the residuals `{φ_n|_a}`
> across the family.

Equivalently (the socket's `decode_correct_of_decides` form): any correct P-time `D`'s transcript, projected
to a polynomial boundary, must distinguish the `2^m` residuals — which a `< 2^m`-cell boundary cannot do.

## 3. Shortcut-free ⟺ `P ≠ NP` (the airtight step)

Let `L` = the SAT language of the residual family (`∈ NP`, and NP-**complete** by §1).

- **(⇒)** If the family is shortcut-free, then `L ∉ P` by definition. `L` is NP-complete and `L ∉ P`, so
  `P ≠ NP`.
- **(⇐)** If `P ≠ NP`, then SAT `∉ P`; instantiate `{φ_n}` as SAT itself (address block empty or trivial) and
  the family is shortcut-free.

Therefore **"provably NP-hard ∧ provably shortcut-free" ⟺ "a proof of `P ≠ NP`."** The `not_easy_linear_payload`
fence is not a lemma one discharges by choosing a clever family; discharging it *is* the theorem. Every
concrete `{φ_n}` we can write down is in exactly one of two states:

| the family | shortcut-free? | why |
|---|---|---|
| structured (Tseitin/linear, Horn, 2-SAT, …) | **NO** | an explicit P-solver decides it (Gaussian elimination, unit propagation, …) without distinguishing labels — the kill-basis shortcut |
| generic hard 3-SAT | **UNKNOWN** | shortcut-freeness = 3-SAT `∉ P` = the open question |

There is no third column. A family with a *proven* "NO shortcut" is a proof that that family `∉ P`, i.e.
`P ≠ NP`.

## 4. What *is* constructible-and-provable: shortcut-freeness against RESTRICTED solvers

Against a **restricted** solver class (not all of P), shortcut-freeness is real and proved — that is exactly
what the repo's capstones are:

| Restricted solver class | Concrete shortcut-free family | Capstone |
|---|---|---|
| `AC⁰[p]`, `p` prime | `PARITY`, `MOD_q` | `PRIME_ACC0_CAPSTONE.md` |
| De Morgan formulas | Nečiporuk hard function (`Ω(N²/log N)`) | `NECIPORUK_CAPSTONE.md` |
| UPP / sign-rank | Walsh–Hadamard | `FORSTER_CAPSTONE.md` |
| resolution proof-space | expander Tseitin (`Ω(\|V\|)` space) | `TSEITIN_SPACE_CAPSTONE.md` |

Each is a genuine NP-hard-flavoured / explicit family with a **proved** no-shortcut result — *against that
class*. None extends to general P, because extending it is `P ≠ NP` (and, for the P-easy objects like Tseitin
and parity, an explicit P-shortcut exists — they are shortcut-free only against the weak class).

## 5. Verdict

- **NP-hard residual family: constructed** (§1) — real, concrete, dischargeable in the socket for
  `fam`/`label_injective`/`residual_semantics`/`np_complete_payload`.
- **Shortcut-free against general P: not constructible** — it is `P ≠ NP` (§3). No family carries a *proof*
  of general-P shortcut-freeness without being a proof of the theorem.
- **Shortcut-free against a restricted class: constructed and proved** — the five capstones (§4).

So the honest maximum is exactly this: the NP-hard family is built; the shortcut-free fence
(`not_easy_linear_payload`) is the theorem, and it is provable only after weakening "general P" to a
restricted class — at which point it is one of the capstones. Any Lean instance that *discharges*
`not_easy_linear_payload` for general P with a concrete family is either using a family that isn't actually
shortcut-free (a hidden shortcut) or has proved `P ≠ NP`.

*Companions: `PRIME_ACC0_CAPSTONE.md` (the master ledger), `NON_NATURAL_CANDIDATE_TRIAGE.md` (the same wall
from the measure side). Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.*
