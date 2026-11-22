import SatWalk.UpperBound
import SatWalk.LowerBound
import SatWalk.Separation
import SatWalk.ResourceBound

/-! Note 1 declarations available for kernel replay. Each entry names a proved
claim against the shared oracle model. -/

#print axioms SatWalk.theorem_upper_bound
#print axioms SatWalk.paritySolver_independent
#print axioms SatWalk.paritySolver_progress
#print axioms SatWalk.paritySolver_at_budget
#print axioms SatWalk.theorem_upper_bound_solves
#print axioms SatWalk.theorem_bit_complexity
#print axioms SatWalk.ResourceBound.progress
#print axioms SatWalk.DenseMachine.update_eq

#print axioms SatWalk.CodeLowerBound.code_charge
#print axioms SatWalk.CodeLowerBound.randomized_code_charge
#print axioms SatWalk.ParityGadget.compilation
#print axioms SatWalk.ParityGadget.preserves_distance
#print axioms SatWalk.theorem_lower_bound
#print axioms SatWalk.theorem_memoryless_separation
#print axioms SatWalk.SignedLearner.equivariant
#print axioms SatWalk.SignedLearner.clause_congr
#print axioms SatWalk.Memoryless.uniform
