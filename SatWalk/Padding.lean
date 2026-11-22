import SatWalk.Occurrences

namespace SatWalk.Padding
open FeedbackCube Model CodeLowerBound Occurrences

def liftLit (a : Nat) (l : Literal n) : Literal (n+a) := ⟨l.var.castAdd a, l.value⟩
def units (n a : Nat) : List (Clause (n+a)) :=
  (List.finRange a).map fun j => [⟨j.natAdd n, false⟩]
def pad (D : Formula n) (a : Nat) : Formula (n+a) where
  clauses := D.clauses.map (List.map (liftLit a)) ++ units n a
  width := by
    intro c mem
    rcases List.mem_append.mp mem with h | h
    · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h; simpa using D.width q hq
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp h; simp

def project (x : Point (n+a)) : Point n := fun i => x (i.castAdd a)
def zeroExtend (x : Point n) (a : Nat) : Point (n+a) := Fin.addCases x (fun _ => false)

private theorem broken_map (x : Point (n+a)) (q : Clause n) :
    Broken (q.map (liftLit a)) x ↔ Broken q (project x) := by
  simp [Broken, liftLit, holds, project]

private theorem parity_map (x : Point (n+a)) (q : Clause n) :
    parity (q.map (liftLit a)) x = parity q (project x) := by
  induction q with
  | nil => rfl
  | cons l q ih => simp [parity, liftLit, holds, project, ih]

theorem solved (D : Formula n) (x : Point (n+a)) :
    Solved (pad D a).clauses x ↔ Solved D.clauses (project x) ∧ ∀ j : Fin a, x (j.natAdd n) = false := by
  unfold Solved
  simp only [pad, units, List.forall_mem_append, List.forall_mem_map, broken_map, List.mem_finRange, forall_const]
  simp [Broken, holds]

theorem odd (D : Formula n) (a) (x : Point n) (hx : OddWitness D.clauses x) :
    OddWitness (pad D a).clauses (zeroExtend x a) := by
  unfold OddWitness
  simp only [pad, units, List.forall_mem_append, List.forall_mem_map, parity_map, List.mem_finRange, forall_const]
  have eq : project (zeroExtend x a) = x := by funext i; simp [project, zeroExtend]
  exact ⟨by rw [eq]; exact hx, fun j => by simp [zeroExtend, parity, holds]⟩

theorem ordered_none (F : Formula n) (x : Point n) :
    orderedReport F x = none ↔ Solved F.clauses x := by
  simp [orderedReport, List.find?_eq_none, Solved]

theorem distance (D : Formula n) (a d) (sep : Separated D d) : Separated (pad D a) d := by
  intro x y hx hy ne
  have X := (solved D x).mp ((ordered_none ..).mp hx)
  have Y := (solved D y).mp ((ordered_none ..).mp hy)
  have diff : project x ≠ project y := by
    intro eq
    apply ne; funext i
    refine Fin.addCases (fun j => congrFun eq j) (fun j => (X.2 j).trans (Y.2 j).symm) i
  have lb := sep _ _ ((ordered_none ..).mpr X.1) ((ordered_none ..).mpr Y.1) diff
  apply lb.trans
  let xs := (differences (project x) (project y)).map (Fin.castAdd a)
  have nd : xs.Nodup := (differences_nodup ..).map (fun _ _ eq => Fin.castAdd_inj.mp eq)
  have sub : xs ⊆ differences x y := by
    intro i mem
    obtain ⟨j,h,rfl⟩ := List.mem_map.mp mem
    have hj := (mem_differences (x := project x) (y := project y)).mp h
    exact mem_differences.mpr hj
  simpa [gap, xs] using nd.length_le_of_subset sub

theorem size (D : Formula n) (a) : (pad D a).clauses.length = D.clauses.length+a := by
  simp [pad, units]

theorem occurrence (D : Formula n) (a) (H : ∀ i, count D.clauses i ≤ 12) (z : Fin (n+a)) :
    count (pad D a).clauses z ≤ 12 := by
  let vs := D.clauses.flatMap (fun c => c.map Literal.var)
  have head : (D.clauses.map (List.map (liftLit a))).flatMap (fun c => c.map Literal.var)
      = vs.map (Fin.castAdd a) := by
    simp [vs, liftLit, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
  have tail : (units n a).flatMap (fun c => c.map Literal.var) = (List.finRange a).map (Fin.natAdd n) := by
    unfold units
    generalize List.finRange a = js
    induction js with
    | nil => rfl
    | cons j js ih => simp [ih]
  have cross (i : Fin n) (j : Fin a) : i.castAdd a ≠ j.natAdd n := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = n+j.val at h
    omega
  change count (_ ++ units n a) z ≤ 12
  rw [count_append]; unfold count; rw [head, tail]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) z
  · rw [List.count_map_of_injective _ _ (fun _ _ eq => Fin.castAdd_inj.mp eq)]
    have h : i.castAdd a ∉ (List.finRange a).map (Fin.natAdd n) := by simp [fun j => Ne.symm (cross i j)]
    rw [List.count_eq_zero.mpr h, Nat.add_zero]; exact H i
  · have h : j.natAdd n ∉ vs.map (Fin.castAdd a) := by simp [fun i => cross i j]
    rw [List.count_eq_zero.mpr h, Nat.zero_add, List.count_map_of_injective _ _ (fun _ _ eq => (Fin.natAdd_inj _).mp eq)]
    rw [List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange _)]; decide

end SatWalk.Padding
