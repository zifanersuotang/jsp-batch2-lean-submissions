import JSP410GaugeCore
import ErdosProblems.Erdos511

/-!
Private integration of the independently written gauge core with the retained
upstream construction API. Only declaration contracts and the necessary data
definitions were supplied to this implementation. This file does not vendor
the upstream construction or certify its redistribution permissions.
-/

open Lean Elab Term

/-- Resolve only the private declarations listed in the API handoff. The private
index is a numeric name component. Ordinary elaboration checks every use's type. -/
elab "e511Api% " shortName:ident : term => do
  let short := shortName.getId.toString
  let allowed : Array String := #[
    "mkPoint", "centerHeight", "boxGauge", "coreSegment", "constructionRadius",
    "barrierMargin", "target", "halfHeight", "continuous_boxGauge",
    "boxGauge_le_one_mem_closedBall", "barrierMargin_pos",
    "target_norm_ge_one_add_barrierMargin_on_boxGauge_eq_one",
    "center_mem_coreSegment", "center_not_mem_other_openBox",
    "coreSegment_subset_lemniscate", "isPreconnected_coreSegment",
    "exists_monic_approx_target"]
  unless allowed.contains short do
    throwError "declaration is not in the retained upstream API contract: {short}"
  let moduleName := Name.str (Name.str (Name.str Name.anonymous
    "_private") "ErdosProblems") "Erdos511"
  let privateNamespace := Name.str (Name.num moduleName 0) "Erdos511"
  let kernelName := Name.str privateNamespace short
  let _ ← getConstInfo kernelName
  Lean.Meta.mkConstWithFreshMVarLevels kernelName

namespace JSP410Independent
namespace ConstructionAPI

noncomputable section

abbrev point : ℝ → ℝ → ℂ := e511Api% mkPoint
abbrev height : (k : ℕ) → Fin k → ℝ := e511Api% centerHeight
abbrev gauge : (k : ℕ) → Fin k → ℂ → ℝ := e511Api% boxGauge
abbrev core : (k : ℕ) → Fin k → Set ℂ := e511Api% coreSegment
abbrev radius : ℝ := e511Api% constructionRadius
abbrev margin : ℕ → ℝ := e511Api% barrierMargin
abbrev approxTarget : ℕ → ℂ → ℂ := e511Api% target
abbrev heightHalf : ℕ → ℝ := e511Api% halfHeight

theorem approximation_exists (k : ℕ) :
    ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ z : ℂ, ‖z‖ ≤ radius →
        ‖p.eval z - approxTarget k z‖ < margin k / 2 :=
  (e511Api% exists_monic_approx_target) k

theorem continuous_gauge (k : ℕ) (j : Fin k) : Continuous (gauge k j) :=
  (e511Api% continuous_boxGauge) k j

theorem gauge_envelope (k : ℕ) (j : Fin k) (z : ℂ)
    (hz : gauge k j z ≤ 1) : ‖z‖ ≤ radius := by
  have hb := (e511Api% boxGauge_le_one_mem_closedBall) k j hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hb

theorem positive_margin (k : ℕ) : 0 < margin k :=
  (e511Api% barrierMargin_pos) k

theorem boundary_barrier (k : ℕ) (j : Fin k) (z : ℂ)
    (hz : gauge k j z = 1) : 1 + margin k ≤ ‖approxTarget k z‖ :=
  (e511Api% target_norm_ge_one_add_barrierMargin_on_boxGauge_eq_one) k j hz

theorem core_isPreconnected (k : ℕ) (j : Fin k) : IsPreconnected (core k j) :=
  (e511Api% isPreconnected_coreSegment) k j

theorem center_in_core (k : ℕ) (j : Fin k) : point 0 (height k j) ∈ core k j :=
  (e511Api% center_mem_coreSegment) k j

theorem other_center_outside (k : ℕ) (i j : Fin k) (hij : i ≠ j) :
    ¬ gauge k i (point 0 (height k j)) < 1 :=
  (e511Api% center_not_mem_other_openBox) k hij

theorem core_in_closedSublevel (k : ℕ) (p : Polynomial ℂ)
    (happrox : ∀ z : ℂ, ‖z‖ ≤ radius →
      ‖p.eval z - approxTarget k z‖ < margin k / 2) (j : Fin k) :
    core k j ⊆ closedSublevel p := by
  intro z hz
  have hopen := (e511Api% coreSegment_subset_lemniscate) k p happrox j hz
  change ‖p.eval z‖ < 1 at hopen
  change ‖p.eval z‖ ≤ 1
  exact le_of_lt hopen

/-- This uses only the supplied point and gauge data definitions. -/
theorem center_gauge_lt (k : ℕ) (j : Fin k) :
    gauge k j (point 0 (height k j)) < 1 := by
  change max
    (|(((0 : ℂ) + (height k j : ℂ) * Complex.I).re)| / (2 / 3 : ℝ))
    (|(((0 : ℂ) + (height k j : ℂ) * Complex.I).im) - height k j| /
      heightHalf k) < 1
  simp

/-- Both explicit endpoints belong to the supplied interval image. -/
theorem left_endpoint_in_core (k : ℕ) (j : Fin k) :
    point (-(5 / 8 : ℝ)) (height k j) ∈ core k j := by
  change point (-(5 / 8 : ℝ)) (height k j) ∈
    (fun x : ℝ => point x (height k j)) '' Set.Icc (-(5 / 8 : ℝ)) (5 / 8 : ℝ)
  refine ⟨-(5 / 8 : ℝ), ?_, rfl⟩
  constructor <;> norm_num

theorem right_endpoint_in_core (k : ℕ) (j : Fin k) :
    point (5 / 8 : ℝ) (height k j) ∈ core k j := by
  change point (5 / 8 : ℝ) (height k j) ∈
    (fun x : ℝ => point x (height k j)) '' Set.Icc (-(5 / 8 : ℝ)) (5 / 8 : ℝ)
  refine ⟨(5 / 8 : ℝ), ?_, rfl⟩
  constructor <;> norm_num

/-- The endpoint distance is established here, rather than assumed as an API. -/
theorem endpoint_distance (y : ℝ) :
    dist (point (-(5 / 8 : ℝ)) y) (point (5 / 8 : ℝ) y) = (5 / 4 : ℝ) := by
  change dist (((-(5 / 8 : ℝ) : ℝ) : ℂ) + (y : ℂ) * Complex.I)
    (((5 / 8 : ℝ) : ℂ) + (y : ℂ) * Complex.I) = (5 / 4 : ℝ)
  rw [dist_add_right, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
  norm_num

end
end ConstructionAPI

open ConstructionAPI

/-- Membership in the upstream component family follows from the public
subtype-image description of a component. -/
theorem component_mem_componentsIn {S : Set ℂ} {c : ℂ} (hc : c ∈ S) :
    connectedComponentIn S c ∈ Erdos511.componentsIn S := by
  refine ⟨⟨c, hc⟩, ?_⟩
  exact connectedComponentIn_eq_image hc

/-- Arbitrarily many distinct actual closed-sublevel components have diameter
strictly greater than the fixed threshold `6/5`. -/
theorem arbitrarily_many_large_closed_components (N : ℕ) :
    ∃ p : Polynomial ℂ, p.Monic ∧
      ∃ family : Fin N → Set ℂ, Function.Injective family ∧
        ∀ i, family i ∈ Erdos511.componentsIn {z : ℂ | ‖p.eval z‖ ≤ 1} ∧
          (6 / 5 : ℝ) < Metric.diam (family i) := by
  obtain ⟨p, hmonic, happrox⟩ := approximation_exists N
  let c : Fin N → ℂ := fun i => point 0 (height N i)
  have hcore : ∀ i, core N i ⊆ closedSublevel p :=
    core_in_closedSublevel N p happrox
  have hc : ∀ i, c i ∈ closedSublevel p :=
    fun i => hcore i (center_in_core N i)
  have hinside : ∀ i, gauge N i (c i) < 1 := center_gauge_lt N
  have havoid : ∀ i z, z ∈ closedSublevel p → gauge N i z ≠ 1 := by
    intro i
    exact closedSublevel_avoids_gauge_one (positive_margin N) happrox
      (gauge_envelope N i) (boundary_barrier N i)
  refine ⟨p, hmonic, (fun i => connectedComponentIn (closedSublevel p) (c i)), ?_, ?_⟩
  · exact component_family_injective c (gauge N) (continuous_gauge N)
      havoid hc hinside (other_center_outside N)
  · intro i
    refine ⟨component_mem_componentsIn (hc i), ?_⟩
    have hbounded := closedSublevel_component_isBounded (continuous_gauge N i)
      (havoid i) (hc i) (hinside i) (gauge_envelope N i)
    have hdiam : (5 / 4 : ℝ) ≤
        Metric.diam (connectedComponentIn (closedSublevel p) (c i)) := by
      apply le_component_diam_of_core (core_isPreconnected N i)
        (center_in_core N i) (hcore i) hbounded
        (left_endpoint_in_core N i) (right_endpoint_in_core N i)
      exact le_of_eq (endpoint_distance (height N i)).symm
    linarith

/-- The single fixed threshold already refutes a uniform finite bound for every
real threshold greater than one. -/
theorem no_uniform_bound_for_large_closed_components :
    ¬ (∀ d : ℝ, 1 < d → ∃ B : ℕ,
      ∀ p : Polynomial ℂ, p.Monic →
        ¬ (∃ family : Fin (B + 1) → Set ℂ, Function.Injective family ∧
          ∀ i, family i ∈ Erdos511.componentsIn {z : ℂ | ‖p.eval z‖ ≤ 1} ∧
            d < Metric.diam (family i))) := by
  intro hbound
  obtain ⟨B, hB⟩ := hbound (6 / 5 : ℝ) (by norm_num)
  obtain ⟨p, hp, family, hinj, hfamily⟩ :=
    arbitrarily_many_large_closed_components (B + 1)
  exact hB p hp ⟨family, hinj, hfamily⟩

end JSP410Independent
