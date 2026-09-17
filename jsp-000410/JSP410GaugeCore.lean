import Mathlib

/-!
Generic component certificates obtained from continuous real-valued gauges.

This module was written from the supplied mathematical interface and public
mathlib APIs, without consulting the former problem-specific bridge.
-/

namespace JSP410Independent

section Topology

variable {X : Type*} [TopologicalSpace X]

/-- A component containing a point below the gauge barrier stays below it. -/
theorem component_subset_gauge_lt
    {S : Set X} {c : X} {g : X → ℝ}
    (hg : Continuous g)
    (havoid : ∀ x ∈ S, g x ≠ 1)
    (hc : c ∈ S) (hgc : g c < 1) :
    connectedComponentIn S c ⊆ {x | g x < 1} := by
  intro x hx
  exact (isPreconnected_connectedComponentIn (F := S) (x := c)).gt_of_ne
    hg.continuousOn
    (fun y hy => havoid y (connectedComponentIn_subset S c hy))
    ⟨c, mem_connectedComponentIn hc, hgc⟩ hx

/-- Connected cores belong to the actual component of their marked point. -/
theorem core_subset_component
    {S K : Set X} {c : X}
    (hK : IsPreconnected K) (hc : c ∈ K) (hKS : K ⊆ S) :
    K ⊆ connectedComponentIn S c :=
  hK.subset_connectedComponentIn hc hKS

/-- The marked components are distinct when every other mark is outside the
corresponding gauge region. No disjointness of the entire gauge regions is used. -/
theorem component_family_injective
    {I : Type*} {S : Set X} (c : I → X) (g : I → X → ℝ)
    (hg : ∀ i, Continuous (g i))
    (havoid : ∀ i x, x ∈ S → g i x ≠ 1)
    (hc : ∀ i, c i ∈ S)
    (hinside : ∀ i, g i (c i) < 1)
    (houtside : ∀ i j, i ≠ j → ¬ g i (c j) < 1) :
    Function.Injective (fun i => connectedComponentIn S (c i)) := by
  intro i j hij
  change connectedComponentIn S (c i) = connectedComponentIn S (c j) at hij
  by_contra hne
  have hj : c j ∈ connectedComponentIn S (c i) := by
    rw [hij]
    exact mem_connectedComponentIn (hc j)
  exact houtside i j hne
    (component_subset_gauge_lt (hg i) (havoid i) (hc i) (hinside i) hj)

end Topology

section Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A bounded envelope for a gauge region also bounds its marked component. -/
theorem component_isBounded
    {S A : Set X} {c : X} {g : X → ℝ}
    (hg : Continuous g)
    (havoid : ∀ x ∈ S, g x ≠ 1)
    (hc : c ∈ S) (hgc : g c < 1)
    (hA : Bornology.IsBounded A)
    (henvelope : ∀ x, g x < 1 → x ∈ A) :
    Bornology.IsBounded (connectedComponentIn S c) := by
  apply hA.subset
  intro x hx
  exact henvelope x (component_subset_gauge_lt hg havoid hc hgc hx)

/-- A pair of points in a connected core gives a diameter lower bound for a
bounded component. Boundedness is explicit because `Metric.diam` is real-valued. -/
theorem le_component_diam_of_core
    {S K : Set X} {c a b : X} {d : ℝ}
    (hK : IsPreconnected K) (hc : c ∈ K) (hKS : K ⊆ S)
    (hbounded : Bornology.IsBounded (connectedComponentIn S c))
    (ha : a ∈ K) (hb : b ∈ K) (hd : d ≤ dist a b) :
    d ≤ Metric.diam (connectedComponentIn S c) := by
  exact hd.trans (Metric.dist_le_diam_of_mem hbounded
    (core_subset_component hK hc hKS ha)
    (core_subset_component hK hc hKS hb))

/-- Sets which are actual marked components of `S` and have diameter at least `d`. -/
def largeComponents (S : Set X) (d : ℝ) : Set (Set X) :=
  {C | (∃ c ∈ S, C = connectedComponentIn S c) ∧ d ≤ Metric.diam C}

/-- Package a family of distinct, large actual components as an embedding. -/
theorem largeComponents_embedding
    {I : Type*} {S : Set X} {d : ℝ} (c : I → X)
    (hc : ∀ i, c i ∈ S)
    (hinj : Function.Injective (fun i => connectedComponentIn S (c i)))
    (hdiam : ∀ i, d ≤ Metric.diam (connectedComponentIn S (c i))) :
    Nonempty (I ↪ {C : Set X // C ∈ largeComponents S d}) := by
  refine ⟨⟨fun i => ⟨connectedComponentIn S (c i), ?_⟩, ?_⟩⟩
  · exact ⟨⟨c i, hc i, rfl⟩, hdiam i⟩
  · intro i j hij
    exact hinj (congrArg Subtype.val hij)

end Metric

section Polynomial

/-- The closed polynomial sublevel set occurring in the problem. -/
def closedSublevel (p : Polynomial ℂ) : Set ℂ :=
  {z | ‖p.eval z‖ ≤ 1}

/-- A strict approximation inside the construction ball transfers the target
barrier to exclusion of the gauge level from the closed sublevel set. -/
theorem closedSublevel_avoids_gauge_one
    {p : Polynomial ℂ} {T : ℂ → ℂ} {g : ℂ → ℝ} {R δ : ℝ}
    (hδ : 0 < δ)
    (happrox : ∀ z, ‖z‖ ≤ R → ‖p.eval z - T z‖ < δ / 2)
    (hball : ∀ z, g z ≤ 1 → ‖z‖ ≤ R)
    (hbarrier : ∀ z, g z = 1 → 1 + δ ≤ ‖T z‖) :
    ∀ z ∈ closedSublevel p, g z ≠ 1 := by
  intro z hz hgz
  have hp : ‖p.eval z‖ ≤ 1 := hz
  have he := happrox z (hball z hgz.le)
  have ht := hbarrier z hgz
  have hn := norm_le_norm_add_norm_sub (p.eval z) (T z)
  linarith

/-- The norm envelope in the construction contract bounds the trapped component. -/
theorem closedSublevel_component_isBounded
    {p : Polynomial ℂ} {c : ℂ} {g : ℂ → ℝ} {R : ℝ}
    (hg : Continuous g)
    (havoid : ∀ z ∈ closedSublevel p, g z ≠ 1)
    (hc : c ∈ closedSublevel p) (hgc : g c < 1)
    (hball : ∀ z, g z ≤ 1 → ‖z‖ ≤ R) :
    Bornology.IsBounded (connectedComponentIn (closedSublevel p) c) := by
  apply component_isBounded hg havoid hc hgc
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R))
  intro z hz
  change dist z 0 ≤ R
  simpa only [dist_zero_right] using hball z hz.le

end Polynomial

end JSP410Independent
