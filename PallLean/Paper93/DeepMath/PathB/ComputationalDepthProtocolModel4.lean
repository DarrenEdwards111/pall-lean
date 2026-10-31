import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProtocolModel3

/-!
# Communication protocol model 4: cost and round structure

Two worst-case combinatorial measures on the protocol tree, the substrate a
round-elimination argument inducts on.

* **`cost`** — the communication cost: the maximum transcript length over all
  inputs (the depth of the tree measured in bits);
* **`Player` / `roundsAux` / `rounds`** — the round count: the maximum number of
  maximal same-speaker blocks along any root-to-leaf path.  A node starts a new
  round exactly when its speaker differs from the current block's speaker.
* **`trans_length_le_cost` (proved)** — every transcript has length at most `cost`;
* **`rounds_le_cost` (proved)** — the round count is at most the communication cost
  (each round costs at least one message).

The round count is precisely the quantity a per-round information lemma (GMWW /
KRW19 `RoundElimStep`) would bound; that analytic step is still open.  Nothing here
is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CommProtocol

variable {α β τ : Type*}

/-- Which party speaks. -/
inductive Player
  | A
  | B
  deriving DecidableEq

/-- The communication cost: the maximum transcript length over all inputs. -/
def cost : Protocol α β τ → ℕ
  | .leaf _ => 0
  | .alice _ l r => 1 + max (cost l) (cost r)
  | .bob _ l r => 1 + max (cost l) (cost r)

/-- Worst-case number of speaker-blocks below a node, given the speaker `lp` of the
current (parent) block.  A node adds a new block (`+1`) exactly when its speaker
differs from `lp`. -/
def roundsAux : Option Player → Protocol α β τ → ℕ
  | _, .leaf _ => 0
  | lp, .alice _ l r =>
      (if lp = some Player.A then 0 else 1)
        + max (roundsAux (some Player.A) l) (roundsAux (some Player.A) r)
  | lp, .bob _ l r =>
      (if lp = some Player.B then 0 else 1)
        + max (roundsAux (some Player.B) l) (roundsAux (some Player.B) r)

/-- The round count: worst-case number of speaker-blocks along a root-to-leaf path. -/
def rounds (P : Protocol α β τ) : ℕ := roundsAux none P

/-- **Every transcript is bounded by the cost (proved)**. -/
theorem trans_length_le_cost (P : Protocol α β τ) (x : α) (y : β) :
    (trans P x y).length ≤ cost P := by
  induction P with
  | leaf t => simp [trans, cost]
  | alice f l r ihl ihr =>
    simp only [trans, cost, List.length_cons]
    cases f x with
    | false => simp only [cond_false]; omega
    | true => simp only [cond_true]; omega
  | bob g l r ihl ihr =>
    simp only [trans, cost, List.length_cons]
    cases g y with
    | false => simp only [cond_false]; omega
    | true => simp only [cond_true]; omega

/-- **Rounds are bounded by cost (proved)**, for any parent-block speaker. -/
theorem roundsAux_le_cost (lp : Option Player) (P : Protocol α β τ) :
    roundsAux lp P ≤ cost P := by
  induction P generalizing lp with
  | leaf t => simp [roundsAux, cost]
  | alice f l r ihl ihr =>
    simp only [roundsAux, cost]
    have h1 := ihl (some Player.A)
    have h2 := ihr (some Player.A)
    split_ifs <;> omega
  | bob g l r ihl ihr =>
    simp only [roundsAux, cost]
    have h1 := ihl (some Player.B)
    have h2 := ihr (some Player.B)
    split_ifs <;> omega

/-- **The round count is at most the communication cost (proved)**. -/
theorem rounds_le_cost (P : Protocol α β τ) : rounds P ≤ cost P :=
  roundsAux_le_cost none P

end PallLean.Paper93.DeepMath.PathB.CommProtocol

#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.trans_length_le_cost
#print axioms PallLean.Paper93.DeepMath.PathB.CommProtocol.rounds_le_cost
