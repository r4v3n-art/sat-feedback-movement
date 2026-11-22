import SatWalk.UpperBound
import SatWalk.FlipCount
import SatWalk.LowerBound
import SatWalk.Separation
import SatWalk.ResourceBound
import SatWalk.MistakeTail
import SatWalk.SimplexCalibration
import SatWalk.PriorityCalibration

/-! Note 1 declarations available for kernel replay. Each entry names a proved
claim against the shared oracle model. -/

#print axioms SatWalk.theorem_upper_bound
#print axioms SatWalk.total_flips
#print axioms SatWalk.paritySolver_independent
#print axioms SatWalk.paritySolver_progress
#print axioms SatWalk.paritySolver_at_budget
#print axioms SatWalk.theorem_upper_bound_solves
#print axioms SatWalk.theorem_bit_complexity
#print axioms SatWalk.ResourceBound.progress
#print axioms SatWalk.DenseMachine.update_eq

#print axioms SatWalk.CodeLowerBound.code_charge
#print axioms SatWalk.CodeLowerBound.binomial_domination
#print axioms SatWalk.CodeLowerBound.fair_binomial
#print axioms SatWalk.PriorityCalibration.exact_mean
#print axioms SatWalk.CodeLowerBound.uniform_expected_charge
#print axioms SatWalk.SimplexCalibration.exact_moves
#print axioms SatWalk.SimplexCalibration.exact_average
#print axioms SatWalk.SimplexCalibration.optimal
#print axioms SatWalk.CodeLowerBound.randomized_code_charge
#print axioms SatWalk.ParityGadget.compilation
#print axioms SatWalk.ParityGadget.preserves_distance
#print axioms SatWalk.theorem_lower_bound
#print axioms SatWalk.theorem_memoryless_separation
#print axioms SatWalk.SignedLearner.equivariant
#print axioms SatWalk.SignedLearner.clause_congr
#print axioms SatWalk.Memoryless.uniform
