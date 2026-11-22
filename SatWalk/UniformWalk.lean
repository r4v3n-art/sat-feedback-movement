import SatWalk.Model
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

noncomputable section
namespace SatWalk.UniformWalk
open Model FeedbackCube
open scoped ENNReal

/-- Average over list occurrences. The default is used only for an empty list. -/
def avg (xs : List α) (fallback : ℝ) (f : α → ℝ) : ℝ :=
  if xs = [] then fallback else (xs.map f).sum / xs.length

private theorem map_sum_le (xs : List α) {f g : α → ℝ} (h : ∀ i ∈ xs, f i ≤ g i) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (.head _)) (ih (fun i hi => h i (.tail _ hi)))

theorem avg_mono (xs : List α) {p q : ℝ} {f g : α → ℝ} (hp : p ≤ q)
    (h : ∀ a ∈ xs, f a ≤ g a) : avg xs p f ≤ avg xs q g := by
  unfold avg; split
  · exact hp
  · exact div_le_div_of_nonneg_right (map_sum_le xs h) (by positivity)

theorem avg_mul (xs : List α) (p k : ℝ) (f : α → ℝ) :
    avg xs (k*p) (fun i => k*f i) = k * avg xs p f := by
  have sum (l : List α) : (l.map (fun a => k*f a)).sum = k * (l.map f).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih, mul_add]
  simp only [avg, sum]; split <;> ring

theorem avg_affine (xs : List α) (p k c : ℝ) (f : α → ℝ) :
    avg xs (c+k*p) (fun i => c+k*f i) = c + k * avg xs p f := by
  have sum (l : List α) : (l.map (fun a => c+k*f a)).sum = l.length*c + k * (l.map f).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]; ring
  simp only [avg, sum]; split
  · rfl
  · rename_i h
    have hn : (xs.length : ℝ) ≠ 0 := by exact_mod_cast (List.length_pos_iff.mpr h).ne'
    field_simp

/-- Choose a uniformly random violated clause occurrence and then a uniformly
random position in it. A satisfying state is absorbing. -/
def advance (F : Formula n) (x : Point n) (v : Point n → ℝ) :=
  avg (violations F x) (v x) fun c => avg c (v x) fun l => v (toggle x l.var)

theorem advance_mono (F : Formula n) (x : Point n) {f g : Point n → ℝ} (h : ∀ y, f y ≤ g y) :
    advance F x f ≤ advance F x g := avg_mono _ (h _) (fun c _ => avg_mono _ (h _) (fun l _ => h _))

theorem advance_affine (F : Formula n) (x : Point n) (v : Point n → ℝ) (a b : ℝ) :
    advance F x (fun y => a+b*v y) = a+b*advance F x v := by
  simp only [advance, avg_affine]

/-- Truncated expected number of flips up to first acceptance. -/
def cost (F : Formula n) : Nat → Point n → ℝ
  | 0, _ => 0
  | t+1, x => if violations F x = [] then 0 else 1+advance F x (cost F t)

/-- Untruncated expectation, including infinite expected running times. -/
noncomputable def mean (F : Formula n) (x : Point n) : ℝ≥0∞ := ⨆ t, ENNReal.ofReal (cost F t x)

theorem upper (F : Formula n) (v : Point n → ℝ) (nonneg : ∀ x, 0 ≤ v x)
    (super : ∀ x, violations F x ≠ [] → 1+advance F x v ≤ v x) (x : Point n) :
    mean F x ≤ ENNReal.ofReal (v x) := by
  apply iSup_le; intro t; apply ENNReal.ofReal_le_ofReal
  induction t generalizing x with
  | zero => exact nonneg _
  | succ t ih =>
    simp only [cost]; split
    · exact nonneg _
    · exact (add_le_add_right (advance_mono F x ih) 1).trans (super x ‹_›)

/-- A bounded nonnegative subsolution yields a hitting-time lower bound.
This proof compares finite horizons directly. It also applies when the mean
is infinite or the walk can fail to terminate. -/
theorem lower (F : Formula n) (v : Point n → ℝ) (M : ℝ) (hM : 1 < M)
    (bound : ∀ x, v x ≤ M) (zero : ∀ x, violations F x = [] → v x = 0)
    (sub : ∀ x, violations F x ≠ [] → v x ≤ 1+advance F x v) (x : Point n) :
    ENNReal.ofReal (v x / 2) ≤ mean F x := by
  let a := 1 - 1/M
  have ha : 0 ≤ a := by dsimp [a]; rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have lt : a < 1 := by
    change 1 - 1/M < 1
    have h : 0 < 1/M := div_pos zero_lt_one (by linarith)
    linarith
  have comp (t : Nat) (x : Point n) : (1-a^t)*v x ≤ cost F t x := by
    induction t generalizing x with
    | zero => simp [cost]
    | succ t ih =>
      rw [cost]
      split
      · rw [zero _ ‹_›]; simp
      · have A : 0 ≤ a^t := pow_nonneg ha _
        have B : 0 ≤ 1-a^t := sub_nonneg.mpr (pow_le_one₀ ha lt.le)
        have h := advance_mono F x (ih)
        have E : advance F x (fun y => (1-a^t)*v y) = (1-a^t)*advance F x v := by
          simpa only [zero_add] using advance_affine F x v 0 (1-a^t)
        rw [E] at h
        have S := mul_le_mul_of_nonneg_left (sub x ‹_›) B
        have vM : (1-a)*v x ≤ 1 := by
          dsimp [a]; field_simp; linarith [bound x]
        have gap := mul_le_mul_of_nonneg_left vM A
        rw [pow_succ]
        nlinarith only [h,S,gap]
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ)<1/2) lt
  apply (le_iSup (fun t => ENNReal.ofReal (cost F t x)) t).trans'
  by_cases hv : 0 ≤ v x
  · apply ENNReal.ofReal_le_ofReal
    have e := mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ 1-a^t by linarith) hv
    linarith [comp t x]
  · rw [ENNReal.ofReal_of_nonpos (by linarith : v x / 2 ≤ 0)]; exact bot_le

end SatWalk.UniformWalk
