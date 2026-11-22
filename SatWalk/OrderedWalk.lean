import SatWalk.PlantedWalk

noncomputable section
namespace SatWalk.OrderedWalk
open FeedbackCube Model UniformWalk
open scoped ENNReal Topology

/-- Uniform single flips within the first violated clause of a fixed ordered CNF. -/
def cost (F : Formula n) : Nat → Point n → ℝ
  | 0,_ => 0
  | t+1,x =>
    match orderedReport F x with
    | none => 0
    | some c => 1+avg c (cost F t x) (fun l => cost F t (toggle x l.var))

def mean (F : Formula n) (x : Point n) : ℝ≥0∞ := ⨆ t, ENNReal.ofReal (cost F t x)

/-- Exact expectation from a bounded nonnegative solution of the first-step
equations. Finite horizons also handle possible nontermination. -/
theorem exact_mean (F : Formula n) (v : Point n → ℝ) (M : ℝ) (big : 1<M)
    (pos : ∀ y, 0 ≤ v y) (cap : ∀ y, v y ≤ M)
    (terminal : ∀ y, orderedReport F y = none → v y=0)
    (bellman : ∀ y c, orderedReport F y = some c →
      v y = 1+avg c (v y) (fun l => v (toggle y l.var))) (x) :
    mean F x = ENNReal.ofReal (v x) := by
  let a := 1-1/M
  have a0 : 0 ≤ a := by dsimp [a]; rw [sub_nonneg,div_le_one (by linarith)]; linarith
  have a1 : a < 1 := by dsimp [a]; have := div_pos zero_lt_one (show 0<M by linarith); linarith
  have bounds (t) (y) : (1-a^t)*v y ≤ cost F t y ∧ cost F t y ≤ v y := by
    induction t generalizing y with
    | zero => simp [cost,pos]
    | succ t ih =>
      rw [cost]
      cases r : orderedReport F y with
      | none => simp [terminal y r]
      | some c =>
        have U := avg_mono c (ih y).2 (fun l _ => (ih (toggle y l.var)).2)
        have L := avg_mono c (ih y).1 (fun l _ => (ih (toggle y l.var)).1)
        rw [avg_mul] at L
        have E := bellman y c r
        have A : 0 ≤ a^t := pow_nonneg a0 _
        have small : (1-a)*v y ≤ 1 := by dsimp [a]; field_simp; linarith [cap y]
        have extra := mul_le_mul_of_nonneg_left small A
        have EE := congrArg (fun z : ℝ => (1-a^t)*z) E
        rw [pow_succ]; exact ⟨by nlinarith only [L,EE,extra],by linarith only [U,E]⟩
  refine le_antisymm (iSup_le (fun t => ENNReal.ofReal_le_ofReal (bounds t x).2)) ?_
  have lim : Filter.Tendsto (fun t : Nat => (1-a^t)*v x) Filter.atTop (𝓝 (v x)) := by
    simpa using ((tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_pow_atTop_nhds_zero_of_lt_one a0 a1)).mul (tendsto_const_nhds (x := v x))
  apply le_of_tendsto' (ENNReal.continuous_ofReal.continuousAt.tendsto.comp lim)
  intro t
  exact (ENNReal.ofReal_le_ofReal (bounds t x).1).trans (le_iSup (fun t => ENNReal.ofReal (cost F t x)) t)

end SatWalk.OrderedWalk
