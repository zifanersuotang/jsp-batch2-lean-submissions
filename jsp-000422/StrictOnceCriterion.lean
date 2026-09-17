/-
Candidate validation status and exact byte hashes are recorded in the accompanying attempt logs.
This adds the explicit hypothesis forall n, a n < 1; it is not the full JSP422 claim.
-/
import ErdosProblems.Erdos526
import FiniteHeadBridge

namespace JSP422FiniteHead

open Filter MeasureTheory Erdos526
open scoped Topology

/-- The source's full-coverage criterion transfers to once-coverage in the strict branch. -/
theorem strict_once_criterion {a b : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n < 1)
    (halim : Tendsto a atTop (nhds 0)) (hdiv : ¬ Summable a)
    (hrearr : IsDecreasingRearrangement a b) :
    sampleMeasure (onceCoverageEvent a) = 1 ↔ SheppCondition b := by
  exact (once_eq_one_iff_full_eq_one ha₀ ha₁).trans
    (Erdos526.erdos_526_resolution_for_rearrangement ha₀ halim hdiv hrearr)

#print axioms strict_once_criterion

end JSP422FiniteHead
