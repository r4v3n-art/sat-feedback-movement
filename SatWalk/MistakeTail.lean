import SatWalk.CodeLowerBound
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace SatWalk.CodeLowerBound
open Model FeedbackCube FeedbackBatches

/-- The fair-bit tail in counts out of 2^k, with accumulated cost z and
one distance charge h for each error. Its two branches have equal mass. -/
def fairTail (h cutoff : Nat) : Nat → Nat → Nat
  | 0,z => if cutoff ≤ z then 1 else 0
  | k+1,z => fairTail h cutoff k z + fairTail h cutoff k (z+h)

private theorem fair_mono (h t k : Nat) : Monotone (fairTail h t k) := by
  induction k with
  | zero => intro a b le; simp only [fairTail]; split <;> split <;> omega
  | succ k ih => intro a b le; exact Nat.add_le_add (ih le) (ih (Nat.add_le_add_right le h))

/-- Count binary flags of length k with exactly j mistakes. -/
theorem fair_binomial (h t k z : Nat) : fairTail h t k z =
    ∑ j ∈ Finset.range (k+1), k.choose j * (if t ≤ z+j*h then 1 else 0) := by
  induction k generalizing z with
  | zero => simp [fairTail]
  | succ k ih =>
    rw [fairTail,ih,ih,Finset.sum_range_succ' (f := fun j => (k+1).choose j * (if t ≤ z+j*h then 1 else 0))]
    simp only [Nat.choose_zero_right,Nat.zero_mul,Nat.add_zero,Nat.one_mul]
    simp only [Nat.choose_succ_succ,Nat.add_mul,Finset.sum_add_distrib]
    have shift : (∑ j ∈ Finset.range (k+1), k.choose (j+1) * (if t ≤ z+(j+1)*h then 1 else 0)) +
        (if t ≤ z then 1 else 0) =
        ∑ j ∈ Finset.range (k+1), k.choose j * (if t ≤ z+j*h then 1 else 0) := by
      have E := Finset.sum_range_succ' (fun j => k.choose j*(if t ≤ z+j*h then 1 else 0)) (k+1)
      simpa [Finset.sum_range_succ (n := k+1), Nat.choose_eq_zero_of_lt (by omega : k < k+1)] using E.symm
    simp only [Nat.add_mul,Nat.one_mul] at *
    simp_rw [show ∀ j, z+h+j*h = z+(j*h+h) by intro j; omega]
    rw [←shift]; ac_rfl

/-- For each fixed tape and every threshold, the number of secrets taking
at least that many moves is bounded below by the fair binomial tail. -/
theorem binomial_domination {B d : Nat} (pos : 0<B) (alg : Solver n σ) (x : Point n)
    (D : Formula n) (dist : Separated D d) (cs : List (Fin n))
    (finish : allLeaves (fun G => ∃ t, Hit B alg G x t) D cs) (cutoff : Nat) :
    fairTail (turns B d) cutoff cs.length 0 ≤
      leafSum (fun G => if cutoff ≤ first B alg G x then 1 else 0) D cs := by
  have aux (F : Formula n) (sub : restriction D F) (ls : List (Fin n))
      (fin : allLeaves (fun G => ∃ t, Hit B alg G x t) F ls) :
      fairTail (turns B d) cutoff ls.length (first B alg F x) ≤
        leafSum (fun G => if cutoff ≤ first B alg G x then 1 else 0) F ls := by
    induction ls generalizing F with
    | nil => exact le_rfl
    | cons i ls ih =>
      have hit (b : Bool) := prefix_terminates (fin b)
      let tick := first B alg F x
      let guess := (trajectory B alg F x tick).2 i
      have same (b : Bool) : tick ≤ first B alg (pin F i b) x := (prefix_first ⟨_,rfl⟩ (hit b)).2.1
      have wrong : ∀ b, guess ≠ b → tick+turns B d ≤ first B alg (pin F i b) x :=
        wrong_child pos sub dist i hit
      have next (b : Bool) := ih _ (under_pin sub i b) (fin b)
      have m := fair_mono (turns B d) cutoff ls.length
      change fairTail _ _ _ tick + fairTail _ _ _ (tick+_) ≤ _ + _
      cases g : guess with
      | false =>
        exact Nat.add_le_add ((m (same false)).trans (next false)) ((m (wrong true (by simp [g]))).trans (next true))
      | true =>
        rw [Nat.add_comm]
        exact Nat.add_le_add ((m (wrong false (by simp [g]))).trans (next false)) ((m (same true)).trans (next true))
  exact (fair_mono _ _ _ (Nat.zero_le _)).trans (aux D ⟨[],by simp⟩ cs finish)

end SatWalk.CodeLowerBound
