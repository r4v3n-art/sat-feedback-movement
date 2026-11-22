import SatWalk.Feedback

namespace SatWalk.FeedbackBatches

/-- Batches needed to cover a fixed distance with positive budget B. -/
def turns (B d : Nat) := (d + B - 1) / B

theorem turns_le {B : Nat} (pos : 0 < B) (d k : Nat) :
    turns B d ≤ k ↔ d ≤ k * B := by
  rw [turns, Nat.div_le_iff_le_mul pos]
  omega

theorem covered {B : Nat} (pos : 0 < B) (d : Nat) : d ≤ turns B d * B :=
  (turns_le pos ..).mp (Nat.le_refl _)

theorem climb {B u v w : Nat} (pos : 0 < B) (h : u ≤ v + w) :
    turns B u ≤ turns B v + turns B w := by
  apply (turns_le pos ..).mpr
  rw [Nat.add_mul]
  exact Nat.le_trans h (Nat.add_le_add (covered pos _) (covered pos _))

theorem descend {B d next : Nat} (pos : 0 < B) (nonzero : 0 < d) (step : next ≤ d - B) :
    turns B next + 1 ≤ turns B d := by
  have hi := covered pos d
  cases val : turns B d with
  | zero => simp [val] at hi; omega
  | succ k =>
    have h : next ≤ k * B := by rw [val, Nat.succ_mul] at hi; omega
    exact Nat.succ_le_succ ((turns_le pos ..).mpr h)

@[simp] theorem turns_zero {B : Nat} (pos : 0 < B) : turns B 0 = 0 :=
  Nat.eq_zero_of_le_zero ((turns_le pos ..).mpr (by simp))

def budget (B : Nat) : Nat → Nat
  | 0 => 0
  | r+1 => budget B r + turns B (r+1)

theorem budget_mono (B : Nat) {a b : Nat} (h : a ≤ b) : budget B a ≤ budget B b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right ..)

theorem paper_bound {B : Nat} (pos : 0 < B) (r : Nat) :
    budget B r ≤ r + Feedback.allowance r / B := by
  have total : budget B r * B ≤ Feedback.allowance r + r * B := by
    induction r with
    | zero => simp [budget, Feedback.allowance]
    | succ r ih =>
      have hi := Nat.div_mul_le_self (r+1+B-1) B
      change turns B (r+1) * B ≤ _ at hi
      simp only [budget, Feedback.allowance, Nat.add_mul, Nat.succ_mul]
      omega
  have h := (Nat.le_div_iff_mul_le pos).mpr total
  rw [Nat.add_mul_div_right _ _ pos] at h
  omega

@[simp] theorem budget_one (r : Nat) : budget 1 r = Feedback.allowance r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [budget, turns, Feedback.allowance, ih]

theorem budget_full {r B : Nat} (pos : 0 < B) (h : r ≤ B) : budget B r = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hi : turns B (r+1) ≤ 1 := (turns_le pos ..).mpr (by simpa)
    have lo := covered pos (r+1)
    have one : turns B (r+1) = 1 := by
      cases e : turns B (r+1) with
      | zero => simp [e] at lo
      | succ k => omega
    simp [budget, ih (by omega), one]

end SatWalk.FeedbackBatches
