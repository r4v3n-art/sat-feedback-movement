import SatWalk.UniformWalk
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

noncomputable section
namespace SatWalk.PlantedWalk
open Model FeedbackCube UniformWalk Finset
open scoped ENNReal

structure Triple (n : Nat) where
  owner : Fin n
  tails : Finset (Fin n)
  two : tails.card = 2
  disjoint : owner ∉ tails
deriving DecidableEq

def tripleEquiv (n : Nat) : Triple n ≃ {p : Fin n × Finset (Fin n) // p.2.card = 2 ∧ p.1 ∉ p.2} where
  toFun t := ⟨(t.owner,t.tails), t.two, t.disjoint⟩
  invFun := fun ⟨⟨i,S⟩,h,k⟩ => ⟨i,S,h,k⟩
  left_inv := by rintro ⟨a,b,c,d⟩; rfl
  right_inv := by rintro ⟨⟨a,b⟩,c,d⟩; rfl

instance : Fintype (Triple n) := Fintype.ofEquiv _ (tripleEquiv n).symm

def clause (t : Triple n) : Clause n :=
  ⟨t.owner,true⟩ :: t.tails.toList.map fun j => ⟨j,false⟩
def pin (i : Fin n) : Clause n := [⟨i,true⟩]
def formula (ts : List (Triple n)) : Formula n where
  clauses := (List.finRange n).map pin ++ ts.map clause
  width := by
    intro c hc
    rcases List.mem_append.mp hc with hp | ht
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp; simp [pin]
    · obtain ⟨t,_,rfl⟩ := List.mem_map.mp ht; simp [clause,t.two]

def bits (x : Point n) := univ.filter fun i => x i = true
def level (x : Point n) := (bits x).card

private theorem level_up {x : Point n} {i} (h : x i = false) : level (toggle x i) = level x + 1 := by
  have eq : bits (toggle x i) = insert i (bits x) := by ext j; by_cases e : j = i <;> simp [bits, toggle, e, h]
  rw [level, eq, card_insert_of_notMem (by simp [bits,h])]; rfl

private theorem level_down {x : Point n} {i} (h : x i = true) : level (toggle x i) = level x - 1 := by
  have eq : bits (toggle x i) = (bits x).erase i := by ext j; by_cases e : j = i <;> simp [bits, toggle, e, h]
  rw [level, eq, card_erase_of_mem (by simp [bits,h])]; rfl

def bad (t : Triple n) (x : Point n) := x t.owner = false ∧ t.tails ⊆ bits x
instance (t : Triple n) (x : Point n) : Decidable (bad t x) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem broken_clause (t : Triple n) (x : Point n) :
    Broken (clause t) x ↔ bad t x := by simp [Broken, clause, holds, bad, Finset.subset_iff, bits]

private theorem reports (ts : List (Triple n)) (x : Point n) :
    violations (formula ts) x =
      ((List.finRange n).filter (fun i => !(x i))).map pin ++
      (ts.filter (fun t => decide (bad t x))).map clause := by
  simp only [violations, formula, List.filter_append, List.filter_map]
  congr 2
  · congr 1; funext i; simp [pin, isBroken, holds]
  · congr 1; funext t; apply Bool.eq_iff_iff.mpr; simp

def numBad (ts : List (Triple n)) (x : Point n) := (ts.filter (fun t => decide (bad t x))).length

private theorem unit_count (x : Point n) :
    ((List.finRange n).filter (fun i => !(x i))).length = n-level x := by
  let us := (List.finRange n).filter (fun i => !(x i))
  have eq : us.toFinset = (bits x)ᶜ := by ext; simp [us,bits]
  have nd : us.Nodup := List.filter_sublist.nodup (List.nodup_finRange _)
  rw [← List.toFinset_card_of_nodup nd, eq, card_compl]; simp [level]

theorem report_count (ts : List (Triple n)) (x : Point n) :
    (violations (formula ts) x).length = n-level x + numBad ts x := by simp [reports,unit_count,numBad]

theorem complete_iff (ts : List (Triple n)) (x : Point n) :
    violations (formula ts) x = [] ↔ level x = n := by
  constructor
  · intro h
    have len := report_count ts x
    rw [h] at len
    have cap : level x ≤ n := by simpa [level] using (bits x).card_le_univ
    simp at len; omega
  · intro eq
    have all : bits x = univ := eq_univ_of_card _ (by simpa [level] using eq)
    have yes (i) : x i = true := (mem_filter.mp (show i ∈ bits x from all ▸ mem_univ _)).2
    simp [reports, bad, yes]

theorem promised (ts : List (Triple n)) : OddWitness (formula ts).clauses (fun _ => true) := by
  have none (ls : List (Fin n)) :
      parity (ls.map (fun i => (⟨i,false⟩ : Literal n))) (fun _ => true) = false := by
    induction ls with
    | nil => rfl
    | cons i ls ih => simp [parity, holds, ih]
  intro c mem
  rcases List.mem_append.mp mem with l | r
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp l; rfl
  · obtain ⟨t,_,rfl⟩ := List.mem_map.mp r; simp [clause, parity, none, holds]

theorem sum_const {f : α → ℝ} (xs : List α) (a : ℝ) (h : ∀ x ∈ xs, f x = a) :
    (xs.map f).sum = xs.length*a := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [h _ (.head _), ih (fun y hy => h y (.tail _ hy))]; ring

private theorem unit_move (f : Nat → ℝ) (x : Point n) (i : Fin n) (h : x i = false) :
    avg (pin i) (f (level x)) (fun l => f (level (toggle x l.var))) = f (level x+1) := by
  simp [avg, pin, level_up h]

private theorem triple_move (f : Nat → ℝ) (x : Point n) (t : Triple n) (h : bad t x) :
    avg (clause t) (f (level x)) (fun l => f (level (toggle x l.var))) =
      (f (level x+1) + 2*f (level x-1))/3 := by
  have hs := sum_const t.tails.toList (f (level x-1)) (f := fun i => f (level (toggle x i)))
    (fun i mem => congrArg f (level_down ((mem_filter.mp (h.2 (by simpa using mem))).2)))
  simp [avg, clause, level_up h.1, List.map_map, Function.comp_def, hs, t.two]

/-- The one-step conditional expectation is determined by the numbers of
violated pins and triples, for any function of the number of correct bits. -/
theorem transition (ts : List (Triple n)) (x : Point n) (f : Nat → ℝ)
    (reject : violations (formula ts) x ≠ []) :
    let j := level x
    let U : ℝ := n-j
    let T : ℝ := numBad ts x
    advance (formula ts) x (fun y => f (level y)) =
      (U*f (j+1) + T*((f (j+1)+2*f (j-1))/3))/(U+T) := by
  change _ = (((n : ℝ)-level x)*_+_)/_
  let g := fun c : Clause n => avg c (f (level x)) (fun l => f (level (toggle x l.var)))
  change avg (violations (formula ts) x) _ g = _
  rw [avg, if_neg reject, reports, List.map_append, List.sum_append]
  simp only [List.map_map, List.length_append, List.length_map]
  rw [sum_const _ (f (level x+1)) (f := g ∘ pin) (fun i mem => unit_move f x i (by simpa using (List.mem_filter.mp mem).2)),
      sum_const _ ((f (level x+1)+2*f (level x-1))/3) (f := g ∘ clause)
        (fun t mem => triple_move f x t (of_decide_eq_true (List.mem_filter.mp mem).2))]
  have cap : level x ≤ n := by simpa [level] using (bits x).card_le_univ
  simp [unit_count, numBad, Nat.cast_sub cap]

def complement (n : Nat) : Point n ≃ Point n where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem level_complement (x : Point n) : level (complement n x) = n-level x := by
  have e : bits (complement n x) = (bits x)ᶜ := by ext i; simp [bits,complement]
  simp [level, e, card_compl]

/-- Uniform average over starting assignments, independent of subsequent flips. -/
def startMean (F : Formula n) : ℝ≥0∞ := (∑ x : Point n, mean F x) / 2^n

theorem paired_start_lower (F : Formula n) (c : ℝ≥0∞)
    (h : ∀ x, c ≤ mean F x + mean F (complement n x)) : c/2 ≤ startMean F := by
  have card : Fintype.card (Point n) = 2^n := by simp [Point, Fintype.card_pi]
  have sum := Finset.sum_le_sum (s := (univ : Finset (Point n))) (fun x _ => h x)
  rw [Finset.sum_add_distrib, (complement n).sum_comp (mean F), ← two_mul] at sum
  simp only [Finset.sum_const, Finset.card_univ, card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at sum
  unfold startMean
  apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
  have h := mul_le_mul_left sum ((2:ℝ≥0∞)^n)⁻¹
  have cancel : (2:ℝ≥0∞)^n * (2^n)⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp) (by simp)
  calc
    c = ((2:ℝ≥0∞)^n * c) * (2^n)⁻¹ := by rw [mul_comm _ c,mul_assoc,cancel,mul_one]
    _ ≤ _ := h
    _ = _ := by simp only [div_eq_mul_inv]; ac_rfl

theorem start_upper (F : Formula n) (c : ℝ≥0∞) (h : ∀ x, mean F x ≤ c) : startMean F ≤ c := by
  have card : Fintype.card (Point n) = 2^n := by simp [Point,Fintype.card_pi]
  apply (ENNReal.div_le_iff (by simp) (by simp)).mpr
  simpa [card, mul_comm] using (Finset.sum_le_sum (s := (univ : Finset (Point n))) (fun x _ => h x))

end SatWalk.PlantedWalk
