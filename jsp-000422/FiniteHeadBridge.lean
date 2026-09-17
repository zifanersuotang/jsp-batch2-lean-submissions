/-
Candidate validation status and exact byte hashes are recorded in the accompanying attempt logs.
Finite-prefix bridge for the original open-arc definitions of Erdos526.Core.
Upstream: plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
This candidate does not handle a prefix length equal to or greater than one.
-/
import ErdosProblems.Erdos526.Core

namespace JSP422FiniteHead

open Filter MeasureTheory ProbabilityTheory Set Erdos526
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-- Keep the tail of the first sample and resample the finite head from the second. -/
def splice (N : ℕ) (p : Sample × Sample) : Sample :=
  fun n ↦ if n < N then p.2 n else p.1 n

lemma measurable_splice (N : ℕ) : Measurable (splice N) := by
  apply measurable_pi_iff.mpr
  intro n
  by_cases hn : n < N
  · simpa only [splice, if_pos hn, Function.comp_def] using
      (measurable_pi_apply n).comp
        (measurable_snd : Measurable (Prod.snd : Sample × Sample → Sample))
  · simpa only [splice, if_neg hn, Function.comp_def] using
      (measurable_pi_apply n).comp
        (measurable_fst : Measurable (Prod.fst : Sample × Sample → Sample))

/-- Independent finite-head resampling leaves the law of the center sequence unchanged. -/
lemma map_splice (N : ℕ) :
    (sampleMeasure.prod sampleMeasure).map (splice N) = sampleMeasure := by
  classical
  change (sampleMeasure.prod sampleMeasure).map (splice N) =
    Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)
  apply Measure.eq_infinitePi
  intro s t ht
  have hbox : (splice N) ⁻¹' Set.pi (s : Set ℕ) t =
      Set.pi (↑(s.filter (fun n ↦ ¬ n < N)) : Set ℕ) t ×ˢ
        Set.pi (↑(s.filter (fun n ↦ n < N)) : Set ℕ) t := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi,
      Finset.mem_coe, Finset.mem_filter]
    constructor
    · intro h
      constructor
      · intro n hn
        simpa only [splice, if_neg hn.2] using h n hn.1
      · intro n hn
        simpa only [splice, if_pos hn.2] using h n hn.1
    · rintro ⟨hTail, hHead⟩ n hn
      by_cases hN : n < N
      · simpa only [splice, if_pos hN] using hHead n ⟨hn, hN⟩
      · simpa only [splice, if_neg hN] using hTail n ⟨hn, hN⟩
  rw [Measure.map_apply (measurable_splice N)
    (MeasurableSet.pi s.countable_toSet (fun n _ ↦ ht n)), hbox,
    Measure.prod_prod]
  change Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)
      (Set.pi (↑(s.filter (fun n ↦ ¬ n < N)) : Set ℕ) t) *
    Measure.infinitePi (fun _ : ℕ ↦ uniformCircle)
      (Set.pi (↑(s.filter (fun n ↦ n < N)) : Set ℕ) t) = _
  rw [Measure.infinitePi_pi _ (fun n _ ↦ ht n),
    Measure.infinitePi_pi _ (fun n _ ↦ ht n)]
  exact Finset.prod_filter_not_mul_prod_filter s (fun n ↦ n < N)
    (fun n ↦ uniformCircle (t n))

/-- The finite-head miss formula only needs bounds on the coordinates in that head. -/
lemma measureReal_head_miss {a : ℕ → ℝ} (N : ℕ) (x : Erdos526.Circle)
    (ha₀ : ∀ n < N, 0 ≤ a n) (ha₁ : ∀ n < N, a n ≤ 1) :
    sampleMeasure.real (⋂ n ∈ Finset.range N, missEvent a x n) =
      ∏ n ∈ Finset.range N, (1 - a n) := by
  let b : ℕ → ℝ := fun n ↦ if n < N then a n else 0
  have hb₀ : ∀ n, 0 ≤ b n := by
    intro n
    by_cases hn : n < N
    · simpa only [b, if_pos hn] using ha₀ n hn
    · simp only [b, if_neg hn, le_refl]
  have hb₁ : ∀ n, b n ≤ 1 := by
    intro n
    by_cases hn : n < N
    · simpa only [b, if_pos hn] using ha₁ n hn
    · simp only [b, if_neg hn, zero_le_one]
  have hset : (⋂ n ∈ Finset.range N, missEvent b x n) =
      ⋂ n ∈ Finset.range N, missEvent a x n := by
    apply iInter_congr
    intro n
    apply iInter_congr
    intro hn
    simp only [missEvent, hitEvent, b, if_pos (Finset.mem_range.mp hn)]
  calc
    sampleMeasure.real (⋂ n ∈ Finset.range N, missEvent a x n) =
        ∏ n ∈ Finset.range N, (1 - b n) := by
      rw [← hset]
      exact measureReal_iInter_missEvent N x hb₀ hb₁
    _ = ∏ n ∈ Finset.range N, (1 - a n) := by
      apply Finset.prod_congr rfl
      intro n hn
      simp only [b, if_pos (Finset.mem_range.mp hn)]

lemma head_miss_positive {a : ℕ → ℝ} (N : ℕ) (x : Erdos526.Circle)
    (ha₀ : ∀ n < N, 0 ≤ a n) (ha₁ : ∀ n < N, a n < 1) :
    0 < sampleMeasure.real (⋂ n ∈ Finset.range N, missEvent a x n) := by
  rw [measureReal_head_miss N x ha₀ (fun n hn ↦ (ha₁ n hn).le)]
  apply Finset.prod_pos
  intro n hn
  exact sub_pos.mpr (ha₁ n (Finset.mem_range.mp hn))

set_option maxHeartbeats 800000 in
/-- If every independent head almost surely repairs a fixed tail, that tail already covers.
The missing point is chosen only after fixing the tail; no measurable selection is used. -/
lemma coversFrom_of_ae_spliced_once {a : ℕ → ℝ} (N : ℕ) (ω : Sample)
    (ha₀ : ∀ n < N, 0 ≤ a n) (ha₁ : ∀ n < N, a n < 1)
    (h : ∀ᵐ ξ ∂sampleMeasure, CoversOnce a (splice N (ω, ξ))) :
    CoversFrom a ω N := by
  intro x
  by_contra hx
  have htail : ∀ n, N ≤ n → x ∉ arc (ω n) (a n) := by
    intro n hn hhit
    exact hx ⟨n, hn, hhit⟩
  let B : Set Sample := ⋂ n ∈ Finset.range N, missEvent a x n
  have hBzero : sampleMeasure B = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [h] with ξ hξ hB
    obtain ⟨n, _, hhit⟩ := hξ x
    by_cases hn : n < N
    · have hmiss : ξ ∈ missEvent a x n :=
        Set.mem_iInter.mp (Set.mem_iInter.mp hB n) (Finset.mem_range.mpr hn)
      have hhit' : ξ ∈ hitEvent a x n := by
        apply (mem_hitEvent_iff a x n ξ).mpr
        simpa only [splice, if_pos hn] using hhit
      exact hmiss hhit'
    · apply htail n (Nat.le_of_not_gt hn)
      simpa only [splice, if_neg hn] using hhit
  have hpos : 0 < sampleMeasure.real B := head_miss_positive N x ha₀ ha₁
  have hreal : sampleMeasure.real B = 0 := by
    rw [measureReal_def, hBzero, ENNReal.toReal_zero]
  rw [hreal] at hpos
  exact (lt_irrefl 0) hpos

/-- Main finite-prefix bridge. Bounds are required only on the removed prefix. -/
theorem measure_coversFrom_eq_one_of_once {a : ℕ → ℝ} (N : ℕ)
    (ha₀ : ∀ n < N, 0 ≤ a n) (ha₁ : ∀ n < N, a n < 1)
    (honce : sampleMeasure (onceCoverageEvent a) = 1) :
    sampleMeasure (coversFromEvent a N) = 1 := by
  have honceAE : ∀ᵐ η ∂sampleMeasure, CoversOnce a η :=
    (mem_ae_iff_prob_eq_one (measurableSet_onceCoverageEvent a)).mpr honce
  have hsplice : ∀ᵐ p ∂sampleMeasure.prod sampleMeasure,
      CoversOnce a (splice N p) := by
    apply ae_of_ae_map (measurable_splice N).aemeasurable
    rw [map_splice N]
    exact honceAE
  have hsections : ∀ᵐ ω ∂sampleMeasure, ∀ᵐ ξ ∂sampleMeasure,
      CoversOnce a (splice N (ω, ξ)) := Measure.ae_ae_of_ae_prod hsplice
  apply (mem_ae_iff_prob_eq_one (measurableSet_coversFromEvent a N)).mp
  filter_upwards [hsections] with ω hω
  exact coversFrom_of_ae_spliced_once N ω ha₀ ha₁ hω

/-- Once-coverage and infinite coverage have the same probability-one criterion
when every length is nonnegative and strictly smaller than one. -/
theorem once_eq_one_iff_full_eq_one {a : ℕ → ℝ}
    (ha₀ : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n < 1) :
    sampleMeasure (onceCoverageEvent a) = 1 ↔
      sampleMeasure (fullCoverageEvent a) = 1 := by
  constructor
  · intro honce
    apply (measure_fullCoverageEvent_eq_one_iff a).mpr
    intro N
    exact measure_coversFrom_eq_one_of_once N (fun n _ ↦ ha₀ n)
      (fun n _ ↦ ha₁ n) honce
  · intro hfull
    simpa only [onceCoverageEvent_eq] using
      (measure_fullCoverageEvent_eq_one_iff a).mp hfull 0

#print axioms measure_coversFrom_eq_one_of_once
#print axioms once_eq_one_iff_full_eq_one

end

end JSP422FiniteHead
