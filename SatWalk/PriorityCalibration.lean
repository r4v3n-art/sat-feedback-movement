import SatWalk.OrderedWalk
import SatWalk.DenseSeparation

noncomputable section
namespace SatWalk.PriorityCalibration
open Model FeedbackCube PlantedWalk UniformWalk
open scoped ENNReal

def formula (n : Nat) : Formula n where
  clauses := (DenseSeparation.triples n).map clause ++ (List.finRange n).map pin
  width := by
    intro c mem
    exact (PlantedWalk.formula (DenseSeparation.triples n)).width c
      (List.mem_append.mpr (List.mem_append.mp mem).symm)

private def pot : Nat → ℝ
  | 0 => 0
  | j+1 => 2^(j+2) - 3*(j+1 : Nat)

private theorem diff (j : Nat) (pos : 0<j) :
    pot (j+1) = pot j + (2:ℝ)^(j+1)-3 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero pos.ne'
  simp only [pot,Nat.cast_succ,pow_succ]; ring

private theorem mono : Monotone pot := monotone_nat_of_le_succ (fun j => by
  cases j with
  | zero => norm_num [pot]
  | succ j =>
    rw [diff (j+1) (by omega)]
    have h : (2:ℝ)^2 ≤ 2^(j+1+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h; linarith)

private theorem report (x : Point n) :
    orderedReport (formula n) x =
      (((DenseSeparation.triples n).filter (fun t => decide (bad t x))).head?.map clause).or
        ((((List.finRange n).filter (fun i => !(x i))).head?).map pin) := by
  simp only [orderedReport,formula,List.find?_append,List.find?_map,List.head?_filter]
  congr 3
  · funext t; apply Bool.eq_iff_iff.mpr; simp [Function.comp_def]
  · funext i; simp [Function.comp_def,pin,isBroken,holds]

private theorem sameSolved (x : Point n) : orderedReport (formula n) x = none ↔ level x=n := by
  rw [←complete_iff (DenseSeparation.triples n) x, no_violations]
  simp only [orderedReport,List.find?_eq_none,Honest, Solved, isBroken_iff]
  simp [formula,PlantedWalk.formula, or_comm]

/-- With the deterministic triple-first order and uniform literal flips, the
exact expected time from one correct bit equals 2^(n+1)-3n-1. -/
theorem exact_mean (n : Nat) (big : 2 ≤ n) (x : Point n) (start : level x=1) :
    OrderedWalk.mean (formula n) x = ENNReal.ofReal ((2:ℝ)^(n+1)-3*n-1) := by
  let f := fun j => pot n - pot j
  have cap (y : Point n) : level y ≤ n := by simpa [level] using (bits y).card_le_univ
  have non (j : Nat) : 0 ≤ pot j := mono (Nat.zero_le j)
  have e := OrderedWalk.exact_mean (formula n) (fun y => f (level y)) (pot n + 2)
    (by linarith [non n]) (fun y => sub_nonneg.mpr (mono (cap y))) (fun y => by dsimp [f]; linarith [non (level y)])
    (fun y h => by rw [(sameSolved y).mp h]; simp [f])
  have step (y : Point n) (c) (r : orderedReport (formula n) y = some c) :
      f (level y) = 1+avg c (f (level y)) (fun l => f (level (toggle y l.var))) := by
    let ts := DenseSeparation.triples n
    let ls := ts.filter (fun t => decide (bad t y))
    have cnt : ls.length = (n-level y)*(level y).choose 2 := DenseSeparation.violated_count y
    rw [report] at r
    change (ls.head?.map clause).or _ = some c at r
    cases hl : ls.head? with
    | none =>
      have empty : ls = [] := List.head?_eq_none_iff.mp hl
      have zero : ls.length=0 := by rw [empty]; rfl
      have uns : level y ≠ n := by intro eq; have := (sameSolved y).mpr eq; rw [report,show ls.head? = none from hl] at this; grind
      have small : level y < 2 := by
        by_contra! hi
        have a := Nat.choose_pos hi
        have b : 0<n-level y := by have := cap y; omega
        have := Nat.mul_pos b a; omega
      cases hu : ((List.finRange n).filter (fun i => !(y i))).head? with
      | none => simp [hl,hu] at r
      | some i =>
        have mem := List.head?_eq_some_iff.mp hu
        obtain ⟨tail,eq⟩ := mem
        have hi : y i = false := by
          have hh : i ∈ (List.finRange n).filter (fun j => !(y j)) := eq ▸ List.Mem.head _
          simpa using (List.mem_filter.mp hh).2
        obtain rfl : pin i = c := by simpa [hl,hu] using r
        rw [unit_move f y i hi]
        interval_cases h : level y <;> norm_num [f,pot] <;> ring
    | some t =>
      obtain ⟨tail,eq⟩ := List.head?_eq_some_iff.mp hl
      have mem : t ∈ ls := eq ▸ List.Mem.head _
      have bad := of_decide_eq_true (List.mem_filter.mp mem).2
      have size : 0 < ls.length := List.length_pos_of_mem mem
      have two : 2 ≤ level y := by
        by_contra! low
        rw [Nat.choose_eq_zero_of_lt low,Nat.mul_zero] at cnt; omega
      obtain rfl : clause t = c := by simpa [hl] using r
      rw [triple_move f y t bad]
      let j := level y - 1
      have jpos : 0 < j := by dsimp [j]; omega
      have hj : j+1=level y := by dsimp [j]; omega
      rw [←hj]
      simp only [Nat.add_sub_cancel]
      simp only [f, diff (j+1) (by omega), diff j jpos, pow_succ]
      ring
  rw [e step x,start]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  congr 1; simp [f,pot] <;> ring

end SatWalk.PriorityCalibration
