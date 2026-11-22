import Std

namespace SatWalk.Affine

universe u v

/-- An affine Boolean equation on a cube: toggling coordinate i always
toggles its truth value by the same coefficient, independent of the point. -/
structure Row {S : Type u} {I : Type v} (flip : S → I → S) where
  value : S → Bool
  coeff : I → Bool
  toggle : ∀ x i, value (flip x i) = (value x ^^ coeff i)

variable {S : Type u} {I : Type v} {flip : S → I → S}

/-- Eliminate the head row's pivot from another row. Truth means that an
equation holds, so the Boolean row operation combines *failure* bits. -/
def eliminate (head row : Row flip) (pivot : I) : Row flip :=
  if row.coeff pivot then
    { value := fun x => row.value x ^^ !(head.value x)
      coeff := fun i => row.coeff i ^^ head.coeff i
      toggle := by
        intro x i
        rw [row.toggle, head.toggle]
        cases row.value x <;> cases row.coeff i <;>
          cases head.value x <;> cases head.coeff i <;> decide }
  else row

private theorem eliminate_at_pivot (head row : Row flip) {i : I}
    (hi : head.coeff i = true) : (eliminate head row i).coeff i = false := by
  cases h : row.coeff i <;> simp [eliminate, h, hi]

private theorem eliminate_value (head row : Row flip) (x : S) (i : I)
    (hx : head.value x = true) : (eliminate head row i).value x = row.value x := by
  cases h : row.coeff i <;> simp [eliminate, h, hx]

private theorem constant_on_path (row : Row flip) (hc : ∀ i, row.coeff i = false)
    (x : S) (path : List I) : row.value (path.foldl flip x) = row.value x := by
  induction path generalizing x with
  | nil => rfl
  | cons i rest ih => simp [List.foldl, ih, row.toggle, hc]

/-- From any point, a feasible system of r affine Boolean equations on a
connected flip space has a solution within r moves. The proof is pivot
elimination. Rank reduction can be applied first to use only independent rows. -/
theorem sparse_repair (connected : ∀ x y : S, ∃ path : List I, path.foldl flip x = y)
    (rows : List (Row flip)) (w : S) (hw : ∀ row ∈ rows, row.value w = true)
    (x : S) : ∃ path : List I, path.length ≤ rows.length ∧
        ∀ row ∈ rows, row.value (path.foldl flip x) = true := by
  induction size : rows.length using Nat.strongRecOn generalizing rows x with
  | ind k ih =>
    cases rows with
    | nil => exact ⟨[], by simp, by simp⟩
    | cons head tail =>
      have short : tail.length < k := by simp at size; omega
      have hwhead := hw head (by simp)
      by_cases hp : ∃ i, head.coeff i = true
      · obtain ⟨i, hi⟩ := hp
        let reduced := tail.map (fun row => eliminate head row i)
        have len : reduced.length = tail.length := by simp [reduced]
        have feasible : ∀ row ∈ reduced, row.value w = true := by
          intro row hrow
          obtain ⟨original, mem, rfl⟩ := List.mem_map.mp hrow
          rw [eliminate_value head original w i hwhead]
          exact hw original (by simp [mem])
        obtain ⟨p, bound, sat⟩ := ih tail.length short reduced feasible x len
        let y := p.foldl flip x
        have tail_ok (original) (mem : original ∈ tail) :
            (eliminate head original i).value y = true :=
          sat _ (List.mem_map.mpr ⟨original, mem, rfl⟩)
        cases hy : head.value y with
        | true =>
          refine ⟨p, by simp at size ⊢; omega, ?_⟩
          intro row mem
          rcases List.mem_cons.mp mem with rfl | m
          · exact hy
          · simpa only [eliminate_value head row y i hy] using tail_ok row m
        | false =>
          have corrected : head.value (flip y i) = true := by rw [head.toggle, hy, hi]; rfl
          refine ⟨p ++ [i], by simp; omega, ?_⟩
          intro row mem
          change row.value ((p ++ [i]).foldl flip x) = true
          simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
          rcases List.mem_cons.mp mem with rfl | m
          · exact corrected
          · have same := (eliminate head row i).toggle y i
            rw [eliminate_at_pivot head row hi, Bool.xor_false,
                eliminate_value head row (flip y i) i corrected, tail_ok row m] at same
            exact same
      · have zero (i : I) : head.coeff i = false := by
          cases eq : head.coeff i
          · rfl
          · exact False.elim (hp ⟨i, eq⟩)
        obtain ⟨p, bound, sat⟩ := ih tail.length short tail
          (fun row mem => hw row (List.mem_cons_of_mem _ mem)) x rfl
        refine ⟨p, by omega, ?_⟩
        intro row mem
        rcases List.mem_cons.mp mem with rfl | m
        · obtain ⟨q,hq⟩ := connected (p.foldl flip x) w
          have same := constant_on_path _ zero (p.foldl flip x) q
          rw [hq, hwhead] at same
          exact same.symm
        · exact sat row m

end SatWalk.Affine
