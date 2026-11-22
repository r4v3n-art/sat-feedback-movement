import SatWalk.PlantedWalk
import Mathlib.Tactic

noncomputable section
namespace SatWalk.DenseSeparation
open PlantedWalk FeedbackCube Model UniformWalk Finset
open scoped ENNReal

def triples (n : Nat) := (univ : Finset (Triple n)).toList

theorem violated_count (x : Point n) :
    numBad (triples n) x = (n-level x)*(level x).choose 2 := by
  classical
  let S := bits x
  let faulty := univ.filter (fun t : Triple n => bad t x)
  have repr : numBad (triples n) x = faulty.card := by
    let l := (triples n).filter (fun t => decide (bad t x))
    have eq : l.toFinset = faulty := by ext; simp [l, faulty, triples]
    have nd : l.Nodup := List.filter_sublist.nodup (Finset.nodup_toList _)
    rw [← eq, List.toFinset_card_of_nodup nd]; rfl
  rw [repr]
  have h : faulty.card = (Sᶜ ×ˢ S.powersetCard 2).card := by
    refine card_bij (fun t _ => (t.owner,t.tails)) ?_ ?_ ?_
    · intro t ht
      obtain ⟨ho,sub⟩ := (mem_filter.mp ht).2
      exact mem_product.mpr ⟨by simp [S,bits,ho], mem_powersetCard.mpr ⟨sub,t.two⟩⟩
    · rintro ⟨i,s,_,_⟩ _ ⟨j,t,_,_⟩ _ eq
      cases eq; rfl
    · rintro ⟨i,t⟩ hi
      obtain ⟨no, tt⟩ := mem_product.mp hi
      obtain ⟨sub, two⟩ := mem_powersetCard.mp tt
      have ni : i ∉ S := mem_compl.mp no
      let g : Triple n := ⟨i,t,two, fun h => ni (sub h)⟩
      refine ⟨g, mem_filter.mpr ⟨mem_univ _, ?_, sub⟩,rfl⟩
      simpa [S,bits] using ni
  simp [h, card_product, card_compl, S, level]

private def c (j : Nat) : ℝ := j.choose 2

/-- Consecutive differences of the dense birth-death chain's Bellman solution.
The all-wrong state moves up with probability one. -/
def delta : Nat → ℝ
  | 0 => 1
  | j+1 => (3*(1+c (j+1))+2*c (j+1)*delta j)/(3+c (j+1))

private theorem cpos (j : Nat) : 0 ≤ c j := by dsimp [c]; positivity
private theorem delta_ge (j : Nat) : 1 ≤ delta j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [delta, le_div_iff₀ (by have := cpos (j+1); linarith)]
    have := mul_nonneg (cpos (j+1)) (show 0 ≤ delta j by linarith)
    linarith [cpos (j+1)]

private theorem delta_hi (j : Nat) : delta j + 3 ≤ 4*2^j := by
  induction j with
  | zero => norm_num [delta]
  | succ j ih =>
    have C := cpos (j+1)
    have lower := delta_ge j
    have step : delta (j+1) ≤ 3+2*delta j := by
      rw [delta, div_le_iff₀ (by linarith : 0 < 3+c (j+1))]
      nlinarith
    rw [pow_succ]; linarith

private theorem c_exact (j : Nat) : 2*c (j+1) = ((j:ℝ)+1)*j := by
  have h := Nat.choose_succ_right_eq (j+1) 1
  simp at h
  unfold c
  exact_mod_cast (show 2*(j+1).choose 2 = (j+1)*j by omega)

/-- A rational telescoping factor avoids logarithms in the lower estimate.
For j ≥ 7 the factor j/(j-6) decreases from seven to one. -/
theorem delta_lo (j : Nat) (big : 7 ≤ j) :
    (2:ℝ)^j * j ≤ 896*delta j*(j-6) := by
  induction j, big using Nat.le_induction with
  | base => norm_num; linarith [delta_ge 7]
  | succ j hj ih =>
    have J : (7:ℝ) ≤ j := by exact_mod_cast hj
    have den : 0 < 3+c (j+1) := by linarith [cpos (j+1)]
    have fac := c_exact j
    have factor : ((j:ℝ)+1)*(3+c (j+1))*(j-6) ≤ (j:ℝ)*c (j+1)*(j-5) := by
      nlinarith only [fac,J]
    have step : 2*c (j+1)*delta j ≤ delta (j+1)*(3+c (j+1)) := by
      rw [delta, div_mul_cancel₀ _ den.ne']; linarith [cpos (j+1)]
    have h1 := mul_le_mul_of_nonneg_left factor (show 0 ≤ (2:ℝ)^j by positivity)
    have h2 := mul_le_mul_of_nonneg_right ih (show 0 ≤ c (j+1)*((j:ℝ)-5) from mul_nonneg (cpos _) (by linarith))
    have h3 := mul_le_mul_of_nonneg_right step (show 0 ≤ 896*((j:ℝ)-6)*((j:ℝ)-5) by exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
    rw [Nat.cast_succ, pow_succ]
    apply le_of_mul_le_mul_right (a := ((j:ℝ)-6)*(3+c (j+1))) _ (mul_pos (by linarith) den)
    nlinarith only [h1,h2,h3]

private def pref (n : Nat) := ∑ j ∈ range n, delta j
private def value (n j : Nat) := pref n - pref j

private theorem pref_mono : Monotone pref := monotone_nat_of_le_succ fun j => by
  simp [pref, sum_range_succ]; linarith [delta_ge j]

private theorem value_bounds (j n : Nat) (le : j ≤ n) :
    0 ≤ value n j ∧ value n j ≤ 4*2^n := by
  refine ⟨sub_nonneg.mpr (pref_mono le), ?_⟩
  have hp : 0 ≤ pref j := by simpa [pref] using pref_mono (Nat.zero_le j)
  have hi : pref n ≤ 4*((2:ℝ)^n-1) := by
    clear le
    induction n with
    | zero => simp [pref]
    | succ n ih => rw [pref, sum_range_succ, pow_succ]; change pref n + _ ≤ _; linarith [delta_hi n]
  simp only [value]; linarith

private theorem bellman (x : Point n) (bad : violations (formula (triples n)) x ≠ []) :
    value n (level x) = 1 + advance (formula (triples n)) x (fun y => value n (level y)) := by
  rw [transition _ _ _ bad, violated_count]
  have reject : level x ≠ n := fun eq => bad ((complete_iff ..).2 eq)
  have cap : level x ≤ n := by simpa [level] using (bits x).card_le_univ
  have u : 0 < (n:ℝ)-level x := sub_pos.mpr (by exact_mod_cast (show level x < n by omega))
  have cast : (↑(n-level x) : ℝ) = n-level x := Nat.cast_sub cap
  push_cast; rw [cast]
  cases h : level x with
  | zero =>
    have hn : (n:ℝ) ≠ 0 := by simpa [h] using u.ne'
    simp [value,pref,delta]; field_simp [hn]; ring
  | succ k =>
    have du : 0 < (n:ℝ)-((k:ℝ)+1) := by simpa [h] using u
    have C := cpos (k+1)
    have top : value n (k+1+1) = value n (k+1) - delta (k+1) := by simp [value,pref,sum_range_succ]; ring
    have bot : value n (k+1-1) = value n (k+1) + delta k := by simp [value,pref,sum_range_succ]; ring
    rw [top, bot]
    change value n (k+1) = 1 + (_ + _ * ((value n (k+1)-delta (k+1)+2*(value n (k+1)+delta k))/3)) / _
    let U : ℝ := n - (k+1 : Nat)
    have uPos : 0 < U := by simpa [U] using du
    have totalPos : 0 < U+U*c (k+1) := by nlinarith only [uPos, mul_nonneg uPos.le C]
    change _ = 1 + (U*_+U*c (k+1)*_)/(U+U*c (k+1))
    have recurrence : delta (k+1)*(3+c (k+1)) = 3*(1+c (k+1))+2*c (k+1)*delta k := by
      rw [delta,div_mul_cancel₀ _ (by linarith)]
    apply (sub_eq_iff_eq_add').mp
    apply (eq_div_iff totalPos.ne').mpr
    nlinarith only [congrArg (fun t => U*t) recurrence]


theorem walk_upper (x : Point n) : mean (formula (triples n)) x ≤ ENNReal.ofReal (4*(2:ℝ)^n) := by
  have cap (y : Point n) : level y ≤ n := by simpa [level] using (bits y).card_le_univ
  exact (upper _ (fun y => value n (level y)) (fun y => (value_bounds _ _ (cap y)).1)
    (fun y h => (bellman y h).symm.le) x).trans (ENNReal.ofReal_le_ofReal (value_bounds _ _ (cap x)).2)

theorem walk_lower (big : 8 ≤ n) (x : Point n) (unsolved : level x < n) :
    ENNReal.ofReal ((2:ℝ)^n / 3584) ≤ mean (formula (triples n)) x := by
  have cap (y : Point n) : level y ≤ n := by simpa [level] using (bits y).card_le_univ
  have low := lower (formula (triples n)) (fun y => value n (level y)) (4*2^n+2) (by
      have h : (0:ℝ) < 2^n := by positivity
      linarith)
    (fun y => (value_bounds _ _ (cap y)).2.trans (by linarith)) (fun y h => by
      rw [(complete_iff ..).1 h]; simp [value])
    (fun y h => (bellman y h).le) x
  apply low.trans'; apply ENNReal.ofReal_le_ofReal
  let j := n-1
  have add : j+1 = n := by dsimp [j]; omega
  have pos : (0:ℝ) < j := by exact_mod_cast (show 0 < j by dsimp [j]; omega)
  have dh := delta_lo j (by dsimp [j]; omega)
  have df := delta_ge j
  have hd : (2:ℝ)^j ≤ 896*delta j := by
    apply (le_of_mul_le_mul_right _ pos)
    nlinarith only [dh,df]
  have diff : delta j ≤ value n (level x) := by
    have cmp := pref_mono (show level x ≤ j by dsimp [j]; omega)
    change delta j ≤ pref n - pref (level x)
    have e : pref n = pref j + delta j := (congrArg pref add).symm.trans (sum_range_succ _ _)
    linarith only [cmp,e]
  have e : (2:ℝ)^n = 2^j*2 := (congrArg (fun i : Nat => (2:ℝ)^i) add).symm.trans (pow_succ _ _)
  linarith only [hd,diff,e]

theorem shared_start (big : 8 ≤ n) :
    ENNReal.ofReal ((2:ℝ)^n / 3584)/2 ≤ startMean (formula (triples n)) ∧
    startMean (formula (triples n)) ≤ ENNReal.ofReal (4*(2:ℝ)^n) := by
  refine ⟨paired_start_lower _ _ (fun x => ?_), start_upper _ _ walk_upper⟩
  by_cases h : level x < n
  · exact (walk_lower big x h).trans le_self_add
  · have h' : level (complement n x) < n := by rw [level_complement]; omega
    exact (walk_lower big _ h').trans le_add_self

end SatWalk.DenseSeparation
