import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef

namespace PallLean.Paper93.DeepMath.LPS

open PallLean.Paper93.DeepMath.GraphSpectral

/-- K_n Laplacian is symmetric. -/
theorem completeAdj_laplacian_isSymm (n : ℕ) :
    (laplacian (completeAdj n)).IsSymm :=
  laplacian_isSymm _ (completeAdj_symm n)

end PallLean.Paper93.DeepMath.LPS
