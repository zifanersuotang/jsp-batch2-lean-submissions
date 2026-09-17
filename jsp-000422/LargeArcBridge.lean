/-
Candidate validation status and exact byte hashes are recorded in the accompanying attempt logs.
Endpoint extension in the pinned Core model arc z l = Metric.ball z (l / 2).
The classical Shepp paper assumes lengths strictly below one; this file
extends the model to the unrestricted lengths in the abbreviated web statement.
-/
import StrictOnceCriterion

namespace JSP422FiniteHead

open Filter MeasureTheory ProbabilityTheory Set Erdos526
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

def antipode (z : Erdos526.Circle) : Erdos526.Circle := z + ((1 / 2 : ℝ) : Erdos526.Circle)

lemma circle_dist_le_half (x z : Erdos526.Circle) : dist x z ≤ (1 / 2 : ℝ) := by
  rw [dist_eq_norm]
  simpa only [abs_one] using
    (AddCircle.norm_le_half_period (1 : ℝ) (x := x - z) (by norm_num))

lemma mem_arc_of_one_lt {l : ℝ} (hl : 1 < l) (x z : Erdos526.Circle) :
    x ∈ arc z l := by
  change dist x z < l / 2
  have := circle_dist_le_half x z
  linarith

/-- On the unit additive circle the only point at distance one half from zero is one half. -/
lemma eq_half_of_norm_ge {d : Erdos526.Circle} (hd : (1 / 2 : ℝ) ≤ ‖d‖) :
    d = ((1 / 2 : ℝ) : Erdos526.Circle) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective d
  have hu : ‖(r : Erdos526.Circle)‖ ≤ (1 / 2 : ℝ) := by
    simpa only [abs_one] using
      (AddCircle.norm_le_half_period (1 : ℝ) (x := (r : Erdos526.Circle)) (by norm_num))
  have habs : |r - (round r : ℝ)| = (1 / 2 : ℝ) := by
    simpa only [UnitAddCircle.norm_eq] using le_antisymm hu hd
  have hround : (((round r : ℤ) : ℝ) : Erdos526.Circle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨round r, by simp⟩
  have hclass : ((r - (round r : ℝ) : ℝ) : Erdos526.Circle) = (r : Erdos526.Circle) := by
    rw [AddCircle.coe_sub, hround, sub_zero]
  by_cases hr : 0 ≤ r - (round r : ℝ)
  · rw [abs_of_nonneg hr] at habs
    rw [habs] at hclass
    exact hclass.symm
  · rw [abs_of_neg (lt_of_not_ge hr)] at habs
    have hneg : r - (round r : ℝ) = -(1 / 2 : ℝ) := by linarith
    rw [hneg] at hclass
    have hperiod : ((-(1 / 2 : ℝ)) : Erdos526.Circle) = ((1 / 2 : ℝ) : Erdos526.Circle) := by
      calc
        ((-(1 / 2 : ℝ)) : Erdos526.Circle) = ((-(1 / 2 : ℝ) + 1 : ℝ) : Erdos526.Circle) :=
          (AddCircle.coe_add_period (1 : ℝ) (-(1 / 2 : ℝ))).symm
        _ = ((1 / 2 : ℝ) : Erdos526.Circle) := by norm_num
    exact hclass.symm.trans hperiod

lemma eq_antipode_of_not_mem_unit_arc {x z : Erdos526.Circle} (hx : x ∉ arc z 1) :
    x = antipode z := by
  have hdist : (1 / 2 : ℝ) ≤ ‖x - z‖ := by
    apply le_of_not_gt
    simpa only [arc, Metric.mem_ball, dist_eq_norm] using hx
  have hhalf : x - z = ((1 / 2 : ℝ) : Erdos526.Circle) := eq_half_of_norm_ge hdist
  calc
    x = (x - z) + z := (sub_add_cancel x z).symm
    _ = antipode z := by rw [hhalf]; simp only [antipode, add_comm]

/-- A fixed point is almost surely hit by an independent tail with divergent total length. -/
lemma ae_fixedPoint_tail_hit {a : ℕ → ℝ} (N : ℕ)
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, N ≤ n → a n ≤ 1)
    (hdiv : ¬ Summable a) (x : Erdos526.Circle) :
    ∀ᵐ ω ∂sampleMeasure, ∃ n, N ≤ n ∧ x ∈ arc (ω n) (a n) := by
  let b : ℕ → ℝ := sequenceTail a N
  have hb₀ : ∀ n, 0 ≤ b n := fun n ↦ ha₀ (n + N)
  have hb₁ : ∀ n, b n ≤ 1 := by
    intro n
    exact ha₁ (n + N) (by omega)
  have hbdiv : ¬ Summable b := by
    intro hb
    apply hdiv
    change Summable (fun n : ℕ ↦ a (n + N)) at hb
    exact (summable_nat_add_iff (f := a) N).mp hb
  have hlim : ∀ᵐ τ ∂sampleMeasure, τ ∈ limsup (hitEvent b x) atTop :=
    (mem_ae_iff_prob_eq_one
      (MeasurableSet.measurableSet_limsup (measurableSet_hitEvent b x))).mpr
      (measure_fixedPoint_limsup_eq_one b hb₀ hb₁ hbdiv x)
  have hhit : ∀ᵐ τ ∂sampleMeasure, ∃ n, x ∈ arc (τ n) (b n) := by
    filter_upwards [hlim] with τ hτ
    obtain ⟨n, hn⟩ := (mem_limsup_iff_frequently_mem.mp hτ).exists
    exact ⟨n, (mem_hitEvent_iff b x n τ).mp hn⟩
  have hpull : ∀ᵐ ω ∂sampleMeasure,
      ∃ n, x ∈ arc (sampleTail N ω n) (b n) := by
    apply ae_of_ae_map (μ := sampleMeasure)
      (p := fun τ : Sample ↦ ∃ n, x ∈ arc (τ n) (b n))
      (measurable_sampleTail N).aemeasurable
    rw [map_sampleTail_sampleMeasure N]
    exact hhit
  filter_upwards [hpull] with ω hω
  obtain ⟨n, hn⟩ := hω
  exact ⟨n + N, by omega, by simpa only [sampleTail, b, sequenceTail] using hn⟩

/-- A unit-length open arc and an independent nonsummable small tail cover almost surely. -/
theorem once_eq_one_of_unit_arc {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (halim : Tendsto a atTop (nhds 0))
    (hdiv : ¬ Summable a) (k : ℕ) (hk : a k = 1) :
    sampleMeasure (onceCoverageEvent a) = 1 := by
  have hevent : ∀ᶠ n : ℕ in atTop, a n < 1 :=
    (tendsto_order.1 halim).2 1 (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  let N : ℕ := max K (k + 1)
  have hkN : k < N := by dsimp [N]; omega
  have htail_bound : ∀ n, N ≤ n → a n ≤ 1 := by
    intro n hn
    apply (hK n ?_).le
    dsimp [N] at hn
    omega
  have hhead : ∀ ξ : Sample, ∀ᵐ ω ∂sampleMeasure,
      CoversOnce a (splice N (ω, ξ)) := by
    intro ξ
    have hhit := ae_fixedPoint_tail_hit N ha₀ htail_bound hdiv (antipode (ξ k))
    filter_upwards [hhit] with ω hω
    obtain ⟨n, hn, hhit⟩ := hω
    intro x
    by_cases hx : x ∈ arc (ξ k) 1
    · refine ⟨k, Nat.zero_le _, ?_⟩
      simpa only [splice, if_pos hkN, hk] using hx
    · have hxanti : x = antipode (ξ k) := eq_antipode_of_not_mem_unit_arc hx
      refine ⟨n, Nat.zero_le _, ?_⟩
      simpa only [splice, if_neg (not_lt.mpr hn), hxanti] using hhit
  have hmeas : MeasurableSet {p : Sample × Sample | CoversOnce a (splice N p)} :=
    (measurableSet_onceCoverageEvent a).preimage (measurable_splice N)
  have hheadAE : ∀ᵐ ξ ∂sampleMeasure, ∀ᵐ ω ∂sampleMeasure,
      CoversOnce a (splice N (ω, ξ)) := Filter.Eventually.of_forall hhead
  have hsections : ∀ᵐ ω ∂sampleMeasure, ∀ᵐ ξ ∂sampleMeasure,
      CoversOnce a (splice N (ω, ξ)) := (Measure.ae_ae_comm hmeas).mpr hheadAE
  have hprod : ∀ᵐ p ∂sampleMeasure.prod sampleMeasure,
      CoversOnce a (splice N p) := (Measure.ae_prod_iff_ae_ae hmeas).mpr hsections
  have hmapped : ∀ᵐ η ∂(sampleMeasure.prod sampleMeasure).map (splice N),
      CoversOnce a η :=
    (ae_map_iff (measurable_splice N).aemeasurable
      (measurableSet_onceCoverageEvent a)).mpr hprod
  rw [map_splice N] at hmapped
  exact (mem_ae_iff_prob_eq_one (measurableSet_onceCoverageEvent a)).mp hmapped

theorem once_eq_one_of_large_arc {a : ℕ → ℝ} (k : ℕ) (hk : 1 < a k) :
    sampleMeasure (onceCoverageEvent a) = 1 := by
  have hall : onceCoverageEvent a = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro ω x
    exact ⟨k, Nat.zero_le _, mem_arc_of_one_lt hk x (ω k)⟩
  rw [hall, measure_univ]

theorem once_eq_one_of_exists_ge_one {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (halim : Tendsto a atTop (nhds 0))
    (hdiv : ¬ Summable a) (hlarge : ∃ k, 1 ≤ a k) :
    sampleMeasure (onceCoverageEvent a) = 1 := by
  obtain ⟨k, hk⟩ := hlarge
  rcases eq_or_lt_of_le hk with heq | hlt
  · exact once_eq_one_of_unit_arc ha₀ halim hdiv k heq.symm
  · exact once_eq_one_of_large_arc k hlt

/-- Proposed unrestricted once criterion in Core's open-ball model.
The accompanying attempt logs record elaboration, axiom and kernel verification status. -/
theorem unrestricted_once_criterion {a b : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (halim : Tendsto a atTop (nhds 0))
    (hdiv : ¬ Summable a) (hrearr : IsDecreasingRearrangement a b) :
    sampleMeasure (onceCoverageEvent a) = 1 ↔
      (∃ n, 1 ≤ a n) ∨ SheppCondition b := by
  constructor
  · intro honce
    by_cases hlarge : ∃ n, 1 ≤ a n
    · exact Or.inl hlarge
    · have ha₁ : ∀ n, a n < 1 := by
        intro n
        exact lt_of_not_ge (fun hn ↦ hlarge ⟨n, hn⟩)
      exact Or.inr ((strict_once_criterion ha₀ ha₁ halim hdiv hrearr).mp honce)
  · rintro (hlarge | hshepp)
    · exact once_eq_one_of_exists_ge_one ha₀ halim hdiv hlarge
    · have hfull :=
        (Erdos526.erdos_526_resolution_for_rearrangement ha₀ halim hdiv hrearr).mpr hshepp
      simpa only [onceCoverageEvent_eq] using
        (measure_fullCoverageEvent_eq_one_iff a).mp hfull 0

/-- The same proposed criterion for an arbitrary input sequence, with a rearrangement supplied
by the original source's existence theorem. See the accompanying validation record. -/
theorem unrestricted_once_exists_rearrangement {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (halim : Tendsto a atTop (nhds 0))
    (hdiv : ¬ Summable a) :
    ∃ b : ℕ → ℝ, IsDecreasingRearrangement a b ∧
      (sampleMeasure (onceCoverageEvent a) = 1 ↔
        (∃ n, 1 ≤ a n) ∨ SheppCondition b) := by
  obtain ⟨b, hrearr, _⟩ := Erdos526.erdos_526 ha₀ halim hdiv
  exact ⟨b, hrearr, unrestricted_once_criterion ha₀ halim hdiv hrearr⟩

#print axioms once_eq_one_of_unit_arc
#print axioms unrestricted_once_criterion
#print axioms unrestricted_once_exists_rearrangement

end

end JSP422FiniteHead
