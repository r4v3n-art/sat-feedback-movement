import SatWalk.LDPCCode
import SatWalk.InformationSet

namespace SatWalk.Occurrences
open FeedbackCube Model ParityGadget LDPCCode Finset

/-- Count literal positions, including repeated occurrences in one clause. -/
def count (cs : List (Clause n)) (i : Fin n) :=
  ((cs.flatMap (fun c => c.map Literal.var))).count i

@[simp] theorem count_append (cs ds : List (Clause n)) (i : Fin n) :
    count (cs ++ ds) i = count cs i + count ds i := by simp [count]

private def mark (z a : Fin n) : Nat := if a = z then 1 else 0

private theorem gate_count (a b c z : Fin n) :
    count (gate a b c) z = 4*(mark z a + mark z b + mark z c) := by
  simp [count, gate, List.count_cons, mark, beq_iff_eq]; ring

private def gates (ws : List (Wires n)) := (encode ws).clauses

private theorem gates_append (u v : List (Wires n)) :
    gates (u++v) = gates u ++ gates v := by simp [gates, encode]

private theorem block_count (A : SocketRows b m) (j : Fin m) (z : Coord b m) :
    count (gates (block A j)) z =
      4*((∑ h : Fin 6, mark z (input (A j h))) + 2*(mark z (u j)+mark z (v j)+mark z (w j))) := by
  change count (gate _ _ _ ++ (gate _ _ _ ++ (gate _ _ _ ++ (gate _ _ _ ++ [])))) z = _
  simp only [count_append, gate_count, Fin.sum_univ_succ, Finset.univ_eq_empty, sum_empty, add_zero]
  simp only [show count [] z = 0 from rfl, add_zero]
  norm_num [Fin.succ]; ring

private theorem counts (A : SocketRows b m) (z : Coord b m) :
    count (formula A).clauses z =
      ∑ j, 4*((∑ h : Fin 6, mark z (input (A j h))) + 2*(mark z (u j)+mark z (v j)+mark z (w j))) := by
  have split (js : List (Fin m)) :
      count (gates (js.flatMap (block A))) z = (js.map (fun j => count (gates (block A j)) z)).sum := by
    induction js with
    | nil => rfl
    | cons j js ih => simp [List.flatMap_cons, gates_append, count_append, ih]
  change count (gates ((List.finRange m).flatMap (block A))) z = _
  rw [split]
  simp only [block_count]
  rw [show List.finRange m = List.ofFn id from rfl, List.map_ofFn, List.sum_ofFn]
  rfl

private theorem cut {n m} (i : Fin n) (j : Fin m) : i.castAdd m ≠ j.natAdd n := by
  intro eq
  have h := congrArg Fin.val eq
  change i.val = n + j.val at h
  omega

private theorem cut_add (i : Fin m) (j : Fin m) : i.castAdd m ≠ j.addNat m := by
  intro eq
  have h := congrArg Fin.val eq
  change i.val = j.val + m at h
  omega

private theorem socket_count (p : Pairing m) (i : Variables m) :
    ∑ j, ∑ h, mark i (wires p j h) = 3 := by
  calc
    _ = ∑ t : Right m, mark i (p.symm t).1 := (Fintype.sum_prod_type _).symm
    _ = ∑ t : Left m, mark i t.1 := p.symm.sum_comp (fun t => mark i t.1)
    _ = _ := by rw [Fintype.sum_prod_type]; simp [mark, apply_ite Finset.card]

theorem bounded_occurrences (p : Pairing m) (z : Coord (2*m) m) :
    count (formula (wires p)).clauses z ≤ 12 := by
  rw [counts, ← Finset.mul_sum]
  refine Fin.addCases (fun a => ?_) (fun rem => ?_) z
  · simp only [input, u, v, w, mark, Fin.castAdd_inj, Ne.symm (cut _ _), ite_false, add_zero, mul_zero]
    change 4 * (∑ j, ∑ h, mark a (wires p j h)) ≤ 12
    rw [socket_count]
  · refine Fin.addCases (fun j => ?_) (fun last => ?_) rem
    · simp [input, u, v, w, mark, cut, Ne.symm (cut _ _), Fin.natAdd_inj, Fin.castAdd_inj]
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) last <;>
        simp [input, u, v, w, mark, cut, cut_add, Ne.symm (cut_add _ _), Fin.natAdd_inj, Fin.castAdd_inj]

theorem linear_size (A : SocketRows b m) : (formula A).clauses.length = 16*m := by
  have aux (js : List (Fin m)) : (gates (js.flatMap (block A))).length = 16*js.length := by
    induction js with
    | nil => rfl
    | cons j js ih =>
      simp only [List.flatMap_cons, gates_append, List.length_append, ih, List.length_cons]
      rw [show (gates (block A j)).length = 16 from rfl]; omega
  simpa [gates, formula] using aux (List.finRange m)

end SatWalk.Occurrences
