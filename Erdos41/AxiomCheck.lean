/-
Copyright 2026 Lucas Parobek.
Licensed under the Apache License, Version 2.0.

Kernel axiom audit for all 16 theorems in `Erdos41.Proofs`.
Running `lean Erdos41/AxiomCheck.lean` or `lake --wfail build` verifies that no theorem
depends on `sorryAx` or any custom axiom.
-/
import Erdos41.Proofs

#print axioms Erdos41.erdos_41.variants.b3_harmonic_conservation_numerator
#print axioms Erdos41.erdos_41.variants.bose_chowla_pigeonhole_compressed_span
#print axioms Erdos41.erdos_41.variants.intrashell_triple_negative_cone_localization
#print axioms Erdos41.erdos_41.variants.full_cube_second_moment_combinatorial_identity
#print axioms Erdos41.erdos_41.variants.one_sided_subcone_first_moment_weight
#print axioms Erdos41.erdos_41.variants.three_hemisphere_cardinality_decomposition
#print axioms Erdos41.erdos_41.variants.upper_plus_lower_hemisphere_full_cube_sum
#print axioms Erdos41.erdos_41.variants.am_gm_cubic_cutoff_factorization
#print axioms Erdos41.erdos_41.variants.quadratic_injection_ray_sum_identity
#print axioms Erdos41.erdos_41.variants.dyadic_shell_21_vandermonde_decomposition
#print axioms Erdos41.erdos_41.variants.kkt_cubic_shell_increment_convexity
#print axioms Erdos41.erdos_41.variants.discrete_legendre_fenchel_b3_fiber_excess
#print axioms Erdos41.erdos_41.variants.normalized_integrality_excess_bound_b3
#print axioms Erdos41.erdos_41.variants.binary_subblock_variance_splitting_b3
#print axioms Erdos41.greedyB3Prefix10_is_b3
#print axioms Erdos41.optimalB3RulerN345_is_b3
