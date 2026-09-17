import ErdosProblems.Erdos229
import ErdosProblems.Erdos511
import JSP410GaugeCore
import JSP410IndependentClosed

set_option pp.universes true

#print JSP410Independent.closedSublevel

#print JSP410Independent.largeComponents

#print Erdos511.componentsIn

#print JSP410Independent.ConstructionAPI.point

#print JSP410Independent.ConstructionAPI.height

#print JSP410Independent.ConstructionAPI.gauge

#print JSP410Independent.ConstructionAPI.core

#print JSP410Independent.ConstructionAPI.radius

#print JSP410Independent.ConstructionAPI.margin

#print JSP410Independent.ConstructionAPI.approxTarget

#print JSP410Independent.ConstructionAPI.heightHalf

#check @JSP410Independent.component_subset_gauge_lt
#print axioms JSP410Independent.component_subset_gauge_lt

#check @JSP410Independent.core_subset_component
#print axioms JSP410Independent.core_subset_component

#check @JSP410Independent.component_family_injective
#print axioms JSP410Independent.component_family_injective

#check @JSP410Independent.component_isBounded
#print axioms JSP410Independent.component_isBounded

#check @JSP410Independent.le_component_diam_of_core
#print axioms JSP410Independent.le_component_diam_of_core

#check @JSP410Independent.largeComponents_embedding
#print axioms JSP410Independent.largeComponents_embedding

#check @JSP410Independent.closedSublevel_avoids_gauge_one
#print axioms JSP410Independent.closedSublevel_avoids_gauge_one

#check @JSP410Independent.closedSublevel_component_isBounded
#print axioms JSP410Independent.closedSublevel_component_isBounded

#check @JSP410Independent.ConstructionAPI.approximation_exists
#print axioms JSP410Independent.ConstructionAPI.approximation_exists

#check @JSP410Independent.ConstructionAPI.continuous_gauge
#print axioms JSP410Independent.ConstructionAPI.continuous_gauge

#check @JSP410Independent.ConstructionAPI.gauge_envelope
#print axioms JSP410Independent.ConstructionAPI.gauge_envelope

#check @JSP410Independent.ConstructionAPI.positive_margin
#print axioms JSP410Independent.ConstructionAPI.positive_margin

#check @JSP410Independent.ConstructionAPI.boundary_barrier
#print axioms JSP410Independent.ConstructionAPI.boundary_barrier

#check @JSP410Independent.ConstructionAPI.core_isPreconnected
#print axioms JSP410Independent.ConstructionAPI.core_isPreconnected

#check @JSP410Independent.ConstructionAPI.center_in_core
#print axioms JSP410Independent.ConstructionAPI.center_in_core

#check @JSP410Independent.ConstructionAPI.other_center_outside
#print axioms JSP410Independent.ConstructionAPI.other_center_outside

#check @JSP410Independent.ConstructionAPI.core_in_closedSublevel
#print axioms JSP410Independent.ConstructionAPI.core_in_closedSublevel

#check @JSP410Independent.ConstructionAPI.center_gauge_lt
#print axioms JSP410Independent.ConstructionAPI.center_gauge_lt

#check @JSP410Independent.ConstructionAPI.left_endpoint_in_core
#print axioms JSP410Independent.ConstructionAPI.left_endpoint_in_core

#check @JSP410Independent.ConstructionAPI.right_endpoint_in_core
#print axioms JSP410Independent.ConstructionAPI.right_endpoint_in_core

#check @JSP410Independent.ConstructionAPI.endpoint_distance
#print axioms JSP410Independent.ConstructionAPI.endpoint_distance

#check @JSP410Independent.component_mem_componentsIn
#print axioms JSP410Independent.component_mem_componentsIn

#check @JSP410Independent.arbitrarily_many_large_closed_components
#print axioms JSP410Independent.arbitrarily_many_large_closed_components

#check @JSP410Independent.no_uniform_bound_for_large_closed_components
#print axioms JSP410Independent.no_uniform_bound_for_large_closed_components
