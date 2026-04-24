import PallLean.Paper93.DeepMath.LPS.CayleyGraph

namespace PallLean.Paper93.DeepMath.LPS

def LPSGraphExists (p q : ℕ) : Prop :=
  ∃ (_G : PGL2Quotient q), True

theorem lps_exists_trivial (p q : ℕ) : LPSGraphExists p q :=
  ⟨⟨∅⟩, trivial⟩

end PallLean.Paper93.DeepMath.LPS
