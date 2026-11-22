import SatWalk.PlantedWalk
import Mathlib.Tactic

noncomputable section
namespace SatWalk.SparseBarrier
open Model FeedbackCube UniformWalk PlantedWalk
open scoped ENNReal

/-- At either edge the potential is continued by a constant. Inside, its
consecutive differences are powers of rho. -/
def V (ρ : ℝ) (a b j : Nat) := (ρ^(b-a)-ρ^(min j b-a))/(ρ-1)

private theorem nonneg (hρ : 1 < ρ) (a b j : Nat) : 0 ≤ V ρ a b j := by
  apply div_nonneg _ (by linarith)
  exact sub_nonneg.mpr (pow_le_pow_right₀ hρ.le (by omega))

private theorem delta {ρ : ℝ} (hρ : 1 < ρ) {a b j : Nat} (hj : a ≤ j) (jb : j < b) :
    V ρ a b (j+1) = V ρ a b j - ρ^(j-a) := by
  simp only [V, Nat.min_eq_left (Nat.succ_le_of_lt jb), Nat.min_eq_left jb.le,
    show j+1-a = (j-a)+1 by omega, pow_succ]
  field_simp [show ρ-1 ≠ 0 by linarith]; ring

private theorem step_floor (ρ : ℝ) (hρ : 1 < ρ) (a b j : Nat) (hj : j ≤ a) (ab : a < b) :
    V ρ a b j - 1 ≤ V ρ a b (j+1) ∧ V ρ a b j - 1 ≤ V ρ a b (j-1) := by
  have hd : min (j-1) b - a = 0 := by omega
  have hz : min j b - a = 0 := by omega
  constructor
  · rcases hj.lt_or_eq with lt | rfl
    · simp [V,hz,show min (j+1) b - a = 0 by omega]
    · rw [delta hρ (le_refl _) ab]; simp
  · simp [V,hd,hz]

/-- Converts the drift ratio in the band into an exponential expected cost
from any state below its upper edge. No optional-stopping axiom is used. -/
theorem walk_lower (ts : List (Triple n)) (a b : Nat) (ab : a < b) (bn : b ≤ n)
    (ρ : ℝ) (hρ : 1 < ρ) (h2 : ρ < 2)
    (ratio : ∀ x : Point n, a < level x → level x < b →
      ρ*(3*((n : ℝ)-level x)+numBad ts x) ≤ 2*numBad ts x)
    (x : Point n) (start : level x < b) :
    ENNReal.ofReal (ρ^(b-a)/4) ≤ mean (formula ts) x := by
  let v := V ρ a b
  let M := ρ^(b-a)/(ρ-1)+2
  have den : 0 < ρ-1 := by linarith
  have pos : 0 < ρ := by linarith
  have bigM : 1 < M := by dsimp [M]; have h := div_nonneg (pow_nonneg pos.le (b-a)) den.le; linarith
  have cap (y : Point n) : v (level y) ≤ M := by
    dsimp [v,V,M]
    have h := div_nonneg (pow_nonneg pos.le (min (level y) b-a)) den.le
    rw [sub_div]; linarith
  have zero (y : Point n) (ok : violations (formula ts) y = []) : v (level y) = 0 := by
    rw [(complete_iff ..).1 ok]; simp [v,V,Nat.min_eq_right bn]
  have drift (y : Point n) (rej : violations (formula ts) y ≠ []) :
      v (level y) ≤ 1 + advance (formula ts) y (fun z => v (level z)) := by
    let j := level y
    let U : ℝ := n-j
    let T : ℝ := numBad ts y
    have capN : j ≤ n := by simpa [j,level] using (bits y).card_le_univ
    have J : j < n := Nat.lt_of_le_of_ne capN (fun eq => rej ((complete_iff ..).2 eq))
    have u : 0 < U := sub_pos.mpr (by exact_mod_cast J)
    have t : 0 ≤ T := by dsimp [T]; positivity
    have dt : 0 < U+T := by linarith
    rw [transition ts y v rej]
    change v j ≤ 1+(U*v (j+1)+T*((v (j+1)+2*v (j-1))/3))/(U+T)
    apply sub_le_iff_le_add'.mp
    apply (le_div_iff₀ dt).mpr
    by_cases jb : b ≤ j
    · have base : v j = 0 := by simp [v,V,Nat.min_eq_right jb]
      rw [base]
      have N1 := nonneg hρ a b (j+1)
      have N2 := nonneg hρ a b (j-1)
      change 0 ≤ v (j+1) at N1
      change 0 ≤ v (j-1) at N2
      nlinarith only [mul_nonneg u.le N1,mul_nonneg t N1,mul_nonneg t N2,u,t]
    · by_cases floor : j ≤ a
      · obtain ⟨up,down⟩ := step_floor ρ hρ a b j floor ab
        change v j - 1 ≤ _ at up down
        nlinarith only [mul_le_mul_of_nonneg_left up u.le, mul_le_mul_of_nonneg_left up t,
          mul_le_mul_of_nonneg_left down t]
      · have up := delta hρ (show a ≤ j by omega) (show j < b by omega)
        have prev := delta hρ (show a ≤ j-1 by omega) (show j-1 < b by omega)
        rw [show j-1+1=j by omega] at prev
        let z := ρ^(j-1-a)
        have shift : ρ^(j-a) = z*ρ := by rw [show j-a = (j-1-a)+1 by omega, pow_succ]
        have q := ratio y (by omega) (by omega)
        change ρ*(3*U+T) ≤ 2*T at q
        have z0 : 0 ≤ z := pow_nonneg pos.le _
        change v (j+1) = v j - _ at up
        change v j = v (j-1)-z at prev
        rw [up,shift,show v (j-1) = v j+z by linarith only [prev]]
        nlinarith only [mul_le_mul_of_nonneg_right q z0,u,t]
  have low := lower (formula ts) (fun y => v (level y)) M bigM cap zero drift x
  apply low.trans'; apply ENNReal.ofReal_le_ofReal
  have e : min (level x) b - a ≤ b-1-a := by omega
  have p := pow_le_pow_right₀ hρ.le e
  have last : ρ^(b-a) = ρ^(b-1-a)*ρ := by rw [show b-a = b-1-a+1 by omega, pow_succ]
  dsimp [v,V]
  have lb : ρ^(b-1-a) ≤ (ρ^(b-a)-ρ^(min (level x) b-a))/(ρ-1) := by
    apply (le_div_iff₀ den).mpr
    linarith only [p,last]
  nlinarith only [lb,last,mul_le_mul_of_nonneg_right h2.le (pow_nonneg pos.le (b-1-a))]

end SatWalk.SparseBarrier
