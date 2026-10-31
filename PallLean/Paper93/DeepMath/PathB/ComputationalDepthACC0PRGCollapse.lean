import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DerandCollapse

/-!
# PRG collapse — the seed-enumeration mechanism (proved), the fooling residue isolated

Workstream A, step 3 (residue internals).  This opens the most self-contained residue — `PRGCollapsesMAtoNP`
(`PRGExists → MA ⊆ NP`) — and proves its **seed-enumeration collapse mechanism**, isolating the genuine
pseudorandomness core (`PRGFools`).  Mirrors the guessable-prover decomposition (`…ACC0GuessableProver`).

**The mechanism.**  An `MA` computation accepts `x` iff some Merlin witness `w` makes the randomized verifier `V x w r`
accept with high probability.  A PRG fooling `V` lets us replace the true coins `r` by the *finite* list of PRG outputs
`seeds`, and accept iff a **majority** of seeds accept — a deterministic, decidable check.  So:

* **seedAccept** (sub-bricks 1, 4) — `seeds.length < 2 · #{ r ∈ seeds | V x w r }`: the finite seed enumeration +
  majority threshold, **decidable** (`instDecidableSeedAccept`), with the count bounded by `seeds.length`
  (`seed_count_le`).
* **PRGFools** (sub-bricks 2, 3) — `∀ x w, probAccept x w ↔ seedAccept …`: the completeness (prob ≥ 2/3 ⇒ seed
  majority) and soundness (prob ≤ 1/3 ⇒ seed minority) transfer, bundled as the count-level equivalence — the genuine
  pseudorandomness property the PRG supplies.
* **`maLang_eq_npLang`** — given `PRGFools`, the `MA` language (`∃ w, probAccept`) *equals* the `NP` language
  (`∃ w, seedAccept`, a deterministic seed-majority check).
* **`prgCollapsesMAtoNP_of_realizes`** — hence `PRGCollapsesMAtoNP` discharged from the realized form (every `MA`
  language is such a `probAccept`-language with a fooling PRG whose seed-majority language is in `NP`).

## What is proved (clean axioms, no `sorry`)

* **`seedAccept`, `instDecidableSeedAccept`, `seed_count_le`** — the finite, decidable seed-majority NP verifier.
* **`maLang_eq_npLang`** — `PRGFools` ⟹ `MALang probAccept = NPLang seedAccept`.
* **`maLang_mem_np`** — `PRGFools` + the seed-language `∈ NP` ⟹ the `MA` language `∈ NP`.
* **`prgCollapsesMAtoNP_of_realizes`** — discharges `PRGCollapsesMAtoNP` from the realized form (`PRGRealizesCollapse`).

## Honest scope

This proves the **seed-enumeration collapse mechanism** — replacing true coins by a finite seed-majority is sound *given*
the PRG fools the verifier (`maLang_eq_npLang`) — and the seed verifier is concrete and decidable.  So `PRGCollapsesMAtoNP`
is reduced to the genuine pseudorandomness residue **`PRGFools`** (the count-level completeness+soundness transfer), now
a precise named statement, isolated.  The deep residue that remains — that a PRG from a hard function actually fools
`V` — is `HardFunction → PRGExists` (the next workstream-A target, the NW/IW construction).  The collapse glue around it
is proved.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PRGCollapse

open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsMetaTheorem (Lang CClass)
open PallLean.Paper93.DeepMath.PathB.ACC0DerandCollapse (PRGCollapsesMAtoNP)

/-- **The seed-majority NP verifier (sub-bricks 1, 4).**  Accept `(x, w)` iff a strict majority of the finite PRG-seed
outputs accept: `seeds.length < 2 · #{ r ∈ seeds | V x w r }`.  A deterministic, finite check over the enumerated
seeds. -/
def seedAccept {W Coins : Type} (V : List Bool → W → Coins → Bool) (seeds : List Coins)
    (x : List Bool) (w : W) : Prop :=
  seeds.length < 2 * (seeds.filter (fun r => V x w r)).length

/-- **The seed-majority check is decidable (PROVED).**  It is a `Nat` comparison over a finite count — a deterministic
verifier step. -/
instance instDecidableSeedAccept {W Coins : Type} (V : List Bool → W → Coins → Bool)
    (seeds : List Coins) (x : List Bool) (w : W) : Decidable (seedAccept V seeds x w) :=
  Nat.decLt _ _

/-- **The accepting-seed count is finite/bounded (PROVED, sub-brick 1).**  At most `seeds.length` seeds accept. -/
theorem seed_count_le {W Coins : Type} (V : List Bool → W → Coins → Bool) (seeds : List Coins)
    (x : List Bool) (w : W) : (seeds.filter (fun r => V x w r)).length ≤ seeds.length :=
  List.length_filter_le _ seeds

/-- The `MA` language: some Merlin witness makes the randomized verifier accept with high probability. -/
def MALang {W : Type} (probAccept : List Bool → W → Prop) : Lang :=
  fun x => ∃ w, probAccept x w

/-- The `NP` language: some Merlin witness passes the deterministic seed-majority check. -/
def NPLang {W Coins : Type} (V : List Bool → W → Coins → Bool) (seeds : List Coins) : Lang :=
  fun x => ∃ w, seedAccept V seeds x w

/-- **The PRG fooling property (sub-bricks 2, 3).**  The seed-majority agrees with the true-randomness acceptance:
`∀ x w, probAccept x w ↔ seedAccept V seeds x w` — completeness (`prob ≥ 2/3 ⇒ seed majority`) and soundness
(`prob ≤ 1/3 ⇒ seed minority`) transfer, bundled.  This is the genuine pseudorandomness property the PRG supplies. -/
def PRGFools {W Coins : Type} (probAccept : List Bool → W → Prop)
    (V : List Bool → W → Coins → Bool) (seeds : List Coins) : Prop :=
  ∀ x w, probAccept x w ↔ seedAccept V seeds x w

/-- **The seed-enumeration collapse mechanism (PROVED).**  Given the PRG fools `V`, the `MA` language equals the `NP`
seed-majority language: replacing true coins by the seed-majority changes nothing on either side (`exists_congr`). -/
theorem maLang_eq_npLang {W Coins : Type} (probAccept : List Bool → W → Prop)
    (V : List Bool → W → Coins → Bool) (seeds : List Coins)
    (h : PRGFools probAccept V seeds) :
    MALang probAccept = NPLang V seeds := by
  funext x
  exact propext (exists_congr (fun w => h x w))

/-- **The `MA` language is in `NP` (PROVED).**  Given `PRGFools` and that the seed-majority language is in `NP`, the
`MA` language — equal to it — is in `NP`. -/
theorem maLang_mem_np {W Coins : Type} {NP : CClass} (probAccept : List Bool → W → Prop)
    (V : List Bool → W → Coins → Bool) (seeds : List Coins)
    (h : PRGFools probAccept V seeds) (hmem : NPLang V seeds ∈ NP) :
    MALang probAccept ∈ NP := by
  rw [maLang_eq_npLang probAccept V seeds h]; exact hmem

/-- The realized PRG-collapse: under `PRGExists`, every `MA` language is a `probAccept`-language with a fooling PRG whose
seed-majority `NP` language is in `NP`. -/
def PRGRealizesCollapse (PRGExists : Prop) (MA NP : CClass) : Prop :=
  PRGExists → ∀ L ∈ MA, ∃ (W Coins : Type) (probAccept : List Bool → W → Prop)
    (V : List Bool → W → Coins → Bool) (seeds : List Coins),
      L = MALang probAccept ∧ PRGFools probAccept V seeds ∧ NPLang V seeds ∈ NP

/-- **`PRGCollapsesMAtoNP` discharged from the realized form (PROVED glue).**  From `PRGRealizesCollapse` — every `MA`
language realizes as a `probAccept`-language with a fooling PRG and an `NP` seed-majority language — the seed-enumeration
mechanism (`maLang_eq_npLang`) gives `MA ⊆ NP` under `PRGExists`, i.e. `PRGCollapsesMAtoNP`. -/
theorem prgCollapsesMAtoNP_of_realizes (PRGExists : Prop) (MA NP : CClass)
    (h : PRGRealizesCollapse PRGExists MA NP) :
    PRGCollapsesMAtoNP PRGExists MA NP := by
  intro hprg L hL
  obtain ⟨W, Coins, probAccept, V, seeds, hLeq, hfool, hmem⟩ := h hprg L hL
  rw [hLeq, maLang_eq_npLang probAccept V seeds hfool]
  exact hmem

/-!
**The PRG-collapse seed-enumeration mechanism, proved.**  The deterministic seed-majority verifier is concrete and
decidable (`seedAccept`, `instDecidableSeedAccept`, `seed_count_le`); replacing true coins by it is sound given the PRG
fools `V` (`maLang_eq_npLang`); so `PRGCollapsesMAtoNP` reduces to the genuine pseudorandomness residue `PRGFools` (the
count-level completeness+soundness transfer), now a precise named statement (`prgCollapsesMAtoNP_of_realizes`).  The
deep residue that remains — a PRG from a hard function fools `V` — is the next target `HardFunction → PRGExists` (the
NW/IW construction).  Not faked, not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PRGCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PRGCollapse.maLang_eq_npLang
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PRGCollapse.maLang_mem_np
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PRGCollapse.prgCollapsesMAtoNP_of_realizes
