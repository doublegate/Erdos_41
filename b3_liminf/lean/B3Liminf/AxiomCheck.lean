/-
Copyright 2026 Lucas Parobek.
Licensed under the Apache License, Version 2.0.

Kernel axiom audit. Each `#print axioms` below should report only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool`).
-/
import B3Liminf.Theorem1
import B3Liminf.NonVacuity
import B3Liminf.HelmCount

#print axioms B3Liminf.card_mul_succ_le_two_mul_sum
#print axioms B3Liminf.card_idx
#print axioms B3Liminf.w_injOn
#print axioms B3Liminf.sum_w_eq
#print axioms B3Liminf.card_mul_succ_le_two_mul_sum_of_count
#print axioms B3Liminf.countR_of_B3
#print axioms B3Liminf.seq_false_of_countR
#print axioms B3Liminf.seq_false
#print axioms B3Liminf.theorem1
#print axioms B3Liminf.theorem1_liminf
#print axioms B3Liminf.isB3_pow_four
#print axioms B3Liminf.theorem1_hypotheses_satisfiable
#print axioms B3Liminf.helmValue_injOn
#print axioms B3Liminf.helmTriples_finite
#print axioms B3Liminf.helm_count_le
