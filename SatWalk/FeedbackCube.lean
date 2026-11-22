import SatWalk.Affine
import SatWalk.Literal

namespace SatWalk.FeedbackCube

abbrev Point (n : Nat) := Fin n → Bool
abbrev Clause (n : Nat) := List (Literal n)

def toggle (x : Point n) (i : Fin n) : Point n :=
  fun j => if j = i then !(x j) else x j

abbrev Eqn (n : Nat) := Affine.Row (toggle (n := n))

def holds (l : Literal n) (x : Point n) := x l.var == l.value

def parity : Clause n → Point n → Bool
  | [], _ => false
  | l :: ls, x => holds l x ^^ parity ls x

def coefficient : Clause n → Fin n → Bool
  | [], _ => false
  | l :: ls, i => (l.var == i) ^^ coefficient ls i

def clauseRow (c : Clause n) : Eqn n where
  value := parity c
  coeff := coefficient c
  toggle := by
    intro x i
    induction c with
    | nil => rfl
    | cons l ls ih =>
      simp only [parity, coefficient, ih]
      have h : holds l (toggle x i) = (holds l x ^^ (l.var == i)) := by
        by_cases eq : l.var = i
        · simp only [holds, toggle, eq, beq_self_eq_true, Bool.xor_true]
          cases x i <;> cases l.value <;> rfl
        · have be : (l.var == i) = false := beq_eq_false_iff_ne.mpr eq
          simp [holds, toggle, eq, be]
      rw [h]
      simp only [Bool.xor_assoc]
      rw [Bool.xor_left_comm (l.var == i) (parity ls x)]

theorem odd_has_literal {c : Clause n} {x : Point n} (h : parity c x = true) :
    ∃ l ∈ c, holds l x = true := by
  induction c with
  | nil => contradiction
  | cons l ls ih =>
    cases val : holds l x with
    | true => exact ⟨l, .head _, val⟩
    | false =>
      obtain ⟨v, hv, yes⟩ := ih (by simpa [parity, val] using h)
      exact ⟨v, .tail _ hv, yes⟩

def differences (x y : Point n) := (List.finRange n).filter fun i => x i != y i
def gap (x y : Point n) := (differences x y).length

@[simp] theorem mem_differences {i : Fin n} {x y : Point n} :
    i ∈ differences x y ↔ x i ≠ y i := by simp [differences, List.mem_finRange]

theorem differences_nodup (x y : Point n) : (differences x y).Nodup :=
  List.filter_sublist.nodup (List.nodup_finRange n)

@[simp] theorem gap_self (x : Point n) : gap x x = 0 := by simp [gap, differences]

theorem fold_untouched (p : List (Fin n)) (x : Point n) (i : Fin n) (hi : i ∉ p) :
    p.foldl toggle x i = x i := by
  induction p generalizing x with
  | nil => rfl
  | cons a p ih =>
    simp only [List.mem_cons, not_or] at hi
    simp [List.foldl, ih _ hi.2, toggle, hi.1]

private theorem fold_once (p : List (Fin n)) (x : Point n) (i : Fin n) (nd : p.Nodup)
    (hi : i ∈ p) : p.foldl toggle x i = !(x i) := by
  induction p generalizing x with
  | nil => contradiction
  | cons a p ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp hi with rfl | h
    · simp [List.foldl, fold_untouched _ _ _ absent, toggle]
    · have ne : i ≠ a := fun e => absent (e ▸ h)
      simp [List.foldl, ih _ tail h, toggle, ne]

theorem fold_plan {p : List (Fin n)} {x y : Point n} (plan : (differences x y).Perm p) :
    p.foldl toggle x = y := by
  funext i
  by_cases hi : i ∈ p
  · have ne := mem_differences.mp (plan.mem_iff.mpr hi)
    rw [fold_once _ _ _ (plan.nodup_iff.mp (differences_nodup ..)) hi]
    cases hx : x i <;> cases hy : y i <;> simp_all
  · have eq : x i = y i := by
      apply Classical.byContradiction
      intro h
      exact hi (plan.mem_iff.mp (mem_differences.mpr h))
    rw [fold_untouched _ _ _ hi, eq]

theorem gap_le_path (x : Point n) (p : List (Fin n)) : gap x (p.foldl toggle x) ≤ p.length := by
  apply (differences_nodup ..).length_le_of_subset
  intro i hi
  apply Classical.byContradiction
  intro absent
  exact (mem_differences.mp hi) (fold_untouched _ _ _ absent).symm

theorem guide_change (x h : Point n) (p : List (Fin n)) :
    gap x (p.foldl toggle h) ≤ gap x h + p.length := by
  have reach := fold_plan (x := x) (y := h) (List.Perm.refl _)
  simpa [List.foldl_append, reach, gap] using gap_le_path x (differences x h ++ p)

def batch (B : Nat) (x h : Point n) (i : Fin n) :=
  (i :: (differences x h).erase i).take B

/-- A physical batch has distinct coordinates, includes the forced literal and
consumes as much of the remaining Hamming distance as its budget permits. -/
theorem batch_spec {B : Nat} (hB : 0 < B) {x h : Point n} {i : Fin n} (ne : x i ≠ h i) :
    let p := batch B x h i
    p.Nodup ∧ i ∈ p ∧ p.length = min B (gap x h) ∧
      gap (p.foldl toggle x) h ≤ gap x h - B := by
  let route := i :: (differences x h).erase i
  have perm : (differences x h).Perm route := List.perm_cons_erase (mem_differences.mpr ne)
  have len : route.length = gap x h := perm.length_eq.symm
  have reach := fold_plan perm
  have rest := gap_le_path ((route.take B).foldl toggle x) (route.drop B)
  rw [← List.foldl_append, List.take_append_drop, reach, List.length_drop, len] at rest
  refine ⟨(List.take_sublist B route).nodup (perm.nodup_iff.mp (differences_nodup ..)), ?_, ?_, rest⟩
  · cases B with
    | zero => omega
    | succ k => simp [batch]
  · change (route.take B).length = _
    simp [len]

end SatWalk.FeedbackCube
