import PallLean.Paper93.DeepMath.LPS.CayleyGraph
import PallLean.Paper93.DeepMath.LPS.LPSAdjacency

namespace PallLean.Paper93.DeepMath.LPS

theorem regularGraph_edge_count (N d : ℕ) : 2 * ((N * d) / 2) ≤ N * d := by omega

theorem lpsEdgeCount (p q : ℕ) : ((pgl2Size q) * (lpsDegree p)) / 2 ≤
    (pgl2Size q) * (lpsDegree p) := by omega

end PallLean.Paper93.DeepMath.LPS
