import SatWalk.DenseSeparation
import SatWalk.SparseSeparation
import SatWalk.SignedLearner

noncomputable section
namespace SatWalk
open FeedbackCube Model
open scoped ENNReal

/-- Every frame gives the learner a legal response until it accepts, and a
quadratic bound on every history of the very same formula and start. -/
def LearnerBound (F : Formula n) : Prop :=
  ∀ (g : SignedLearner.Frame n) (start : Point n) m s x,
    Run 1 F (SignedLearner.solver g 1) start m s x →
      m ≤ n*(n+1)/2 ∧ (m = n*(n+1)/2 → Solved F.clauses x) ∧
      ∀ c, Honest F x (some c) →
        ∃ t p, (SignedLearner.solver g 1).respond s x c = some (t,p) ∧ LegalMove 1 c p

private theorem learnerBound {F : Formula n} {w} (hw : OddWitness F.clauses w) : LearnerBound F := by
  intro g start m s x run
  exact ⟨SignedLearner.pathwise g hw run, fun eq => SignedLearner.at_budget g hw (eq ▸ run),
    fun _ h => SignedLearner.progress g hw run h⟩

/-- Uniform violated-clause feedback. The same explicit history-aware solver
works on both families. The dense bound holds for every unsolved start and after
uniform initialization. The sparse exponent can approach two at bounded degree.
Both bounds quantify over every signed-equivariant memoryless policy. -/
theorem theorem_memoryless_separation :
    (∀ n ≥ 8, ∃ F : Formula n, OddWitness F.clauses (fun _ => true) ∧ LearnerBound F ∧
      ∀ P : Memoryless.Policy n,
        (∀ x, PlantedWalk.level x < n →
          ENNReal.ofReal ((2:ℝ)^n/3584) ≤ Memoryless.mean P F x ∧
          Memoryless.mean P F x ≤ ENNReal.ofReal (4*(2:ℝ)^n)) ∧
        ENNReal.ofReal ((2:ℝ)^n/3584)/2 ≤ Memoryless.startMean P F ∧
        Memoryless.startMean P F ≤ ENNReal.ofReal (4*(2:ℝ)^n)) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C K N : Nat, ∀ n ≥ N, ∃ F : Formula n,
      OddWitness F.clauses (fun _ => true) ∧ F.clauses.length ≤ C*n ∧
      (∀ i, Occurrences.count F.clauses i ≤ K) ∧ LearnerBound F ∧
      ∀ P : Memoryless.Policy n,
        (∀ x, PlantedWalk.level x ≤ n/2 → ENNReal.ofReal ((2-ε)^n/4) ≤ Memoryless.mean P F x) ∧
        ENNReal.ofReal ((2-ε)^n/4)/2 ≤ Memoryless.startMean P F) := by
  constructor
  · intro n big
    let ts := DenseSeparation.triples n
    have simple := Memoryless.planted_simple ts
    have odd := PlantedWalk.promised ts
    refine ⟨_,odd,learnerBound odd,fun P => ?_⟩
    simp only [Memoryless.mean_eq P _ simple,Memoryless.start_eq P _ simple]
    exact ⟨fun x h => ⟨DenseSeparation.walk_lower big x h,DenseSeparation.walk_upper x⟩,
      DenseSeparation.shared_start big⟩
  · intro ε h₁ h₂
    obtain ⟨C,K,N,h⟩ := SparseSeparation.shared_start ε h₁ h₂
    refine ⟨C,K,N,fun n hn => ?_⟩
    obtain ⟨F,odd,simple,len,occ,point,avg⟩ := h n hn
    refine ⟨F,odd,len,occ,learnerBound odd,fun P => ?_⟩
    simpa only [Memoryless.mean_eq P _ simple,Memoryless.start_eq P _ simple] using And.intro point avg

end SatWalk
