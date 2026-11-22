import SatWalk.FeedbackLearner

namespace SatWalk
open FeedbackCube FeedbackBatches FeedbackLearner

/-- The point in the solver's memory is synchronized with the public point on
every reachable history. The solver has no access to the hidden formula. -/
def paritySolver (n B : Nat) : Model.Solver n (State n) where
  initial := initial
  respond := fun s _ c => advance B s c

private theorem learner_history {F : Model.Formula n} {B : Nat} (pos : 0 < B)
    {x w : Point n} (promise : Model.OddWitness F.clauses w) {m s y}
    (run : Model.Run B F (paritySolver n B) x m s y) :
    y = s.point ∧ FeedbackLearner.Run B F.clauses x m s := by
  induction run with
  | init => exact ⟨rfl, .start⟩
  | @step m s y c t p prior report response legal ih =>
    obtain ⟨rfl, history⟩ := ih
    obtain ⟨mem, broken⟩ := report
    obtain ⟨t', p', update, _, hlegal, _⟩ :=
      advance_spec pos (run_bound pos promise history).1 (promise _ mem) broken
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (update.symm.trans response))
    exact ⟨hlegal.resultingPoint.symm, .step history mem broken update⟩

/-- Every nonempty selection of the learned echelon rows has nonzero binary
sum. Thus their count in the movement bound is the coefficient rank. -/
theorem paritySolver_independent {F : Model.Formula n} {B : Nat} (pos : 0 < B)
    {w x : Point n} (promise : Model.OddWitness F.clauses w) {m s y}
    (run : Model.Run B F (paritySolver n B) x m s y) {rows : FeedbackBasis.Basis n}
    (sel : rows.Sublist s.basis) (ne : rows ≠ []) :
    ∃ i ∈ FeedbackBasis.pivots s.basis, FeedbackBasis.sumCoeff rows i = true :=
  FeedbackBasis.independent (run_bound pos promise (learner_history pos promise run).2).1.echelon sel ne

/-- For each possible next rejection the actual solver produces a legal move.
This excludes vacuous finite-prefix bounds for machines that refuse to move. -/
theorem paritySolver_progress {F : Model.Formula n} {B : Nat} (pos : 0 < B)
    {w x : Point n} (promise : Model.OddWitness F.clauses w) {m s y c}
    (run : Model.Run B F (paritySolver n B) x m s y) (report : Model.Honest F y (some c)) :
    ∃ t p, (paritySolver n B).respond s y c = some (t,p) ∧ Model.LegalMove B c p := by
  obtain ⟨rfl, history⟩ := learner_history pos promise run
  obtain ⟨t, p, update, _, legal, _⟩ := advance_spec pos (run_bound pos promise history).1
    (promise c report.1) report.2
  exact ⟨t, p, update, legal.distinct, legal.withinBudget, legal.includesReported⟩

/-- A pathwise move bound for every history of the actual hidden-clause game.
Here r is the number of independent pivot rows learned on this very history.
budget B r is the sum of ceil(i/B) for i from 1 through r. -/
theorem theorem_upper_bound {F : Model.Formula n} {B : Nat} (pos : 0 < B)
    {w x : Point n} (promise : Model.OddWitness F.clauses w) {m s y}
    (run : Model.Run B F (paritySolver n B) x m s y) :
    let r := s.basis.length
    r ≤ n ∧ m + turns B (gap y s.guide) ≤ budget B r ∧
      m ≤ r + r*(r+1)/(2*B) ∧ (B = 1 → m ≤ r*(r+1)/2) := by
  obtain ⟨rfl, history⟩ := learner_history pos promise run
  obtain ⟨inv, charge⟩ := run_bound pos promise history
  let r := s.basis.length
  have count : m ≤ budget B r := Nat.le_trans (Nat.le_add_right ..) charge
  have tri : Feedback.allowance r = r*(r+1)/2 := by
    rw [← Feedback.allowance_closed]; omega
  refine ⟨FeedbackBasis.rank_le inv.echelon, charge, ?_, ?_⟩
  · have bound := Nat.le_trans count (paper_bound pos r)
    rwa [tri, Nat.div_div_eq_div_mul] at bound
  · rintro rfl
    rw [budget_one, tri] at count
    exact count

/-- Any history using the global move budget ends at a satisfying point.
This conclusion permits arbitrary adaptive clause selection. -/
theorem paritySolver_at_budget {F : Model.Formula n} {B : Nat} (pos : 0 < B)
    {w x : Point n} (promise : Model.OddWitness F.clauses w) {s y}
    (run : Model.Run B F (paritySolver n B) x (budget B n) s y) : Model.Solved F.clauses y := by
  obtain ⟨rfl, history⟩ := learner_history pos promise run
  exact solved_at_budget pos promise history

/-- With any honest reporter, running the executable driver on the given start
returns an assignment satisfying the hidden CNF within its finite move budget. -/
theorem theorem_upper_bound_solves (F : Model.Formula n) {B : Nat} (pos : 0 < B)
    (w x : Point n) (promise : Model.OddWitness F.clauses w)
    (report : Nat → Point n → Option (Clause n)) (honest : ∀ m y, Model.Honest F y (report m y)) :
    Model.Solved F.clauses (play B report (budget B n) 0 (initial x)).point := by
  apply play_solves pos F.clauses x w promise
  · intro m y eq
    simpa [eq, Model.Honest] using honest m y
  · intro m y c eq
    simpa [eq, Model.Honest] using honest m y

end SatWalk
