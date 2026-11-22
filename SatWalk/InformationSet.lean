import SatWalk.ParityGadget
import SatWalk.FeedbackBasis
import Mathlib.Tactic

namespace SatWalk.InformationSet
open FeedbackCube FeedbackBasis ParityGadget

/-- Row reduction on the public homogeneous checks exposes free coordinates.
This uses the same signed affine row semantics as the upper-bound learner. -/
theorem basis_for (rows : List (Eqn n)) (w : Point n) (wit : ∀ q ∈ rows, q.value w = true) :
    ∃ b : Basis n, Echelon b ∧ b.length ≤ rows.length ∧
      ∀ x, Fits b x ↔ ∀ q ∈ rows, q.value x = true := by
  induction rows with
  | nil => exact ⟨[], .empty, by simp, by simp [Fits]⟩
  | cons q rows ih =>
    obtain ⟨b, ech, size, spec⟩ := ih (fun r hr => wit r (.tail _ hr))
    let v := reduce b q
    have eq {x} (ok : Fits b x) : v.value x = q.value x := reduce_value ok _
    have vw : v.value w = true := (eq ((spec w).2 (fun r hr => wit r (.tail _ hr)))).trans (wit q (.head _))
    by_cases pivot : ∃ i, v.coeff i = true
    · obtain ⟨i,hi⟩ := pivot
      refine ⟨(i,v)::b, .add ech hi (reduce_zeros ech _), by simpa using size, ?_⟩
      intro x
      have split : Fits ((i,v)::b) x ↔ v.value x = true ∧ Fits b x := by simp [Fits]
      rw [split, List.forall_mem_cons]
      exact ⟨fun ⟨hv,hs⟩ => ⟨(eq hs).symm.trans hv, (spec x).1 hs⟩,
        fun ⟨hq,hs⟩ => ⟨(eq ((spec x).2 hs)).trans hq, (spec x).2 hs⟩⟩
    · refine ⟨b, ech, by simp; omega, ?_⟩
      intro x
      rw [List.forall_mem_cons, ← spec]
      refine ⟨fun ok => ⟨?_,ok⟩, And.right⟩
      cases h : q.value x with
      | true => rfl
      | false =>
        obtain ⟨i,_,hi⟩ := active_of_disagreement v ((eq ok).trans h) vw
        exact False.elim (pivot ⟨i,hi⟩)

private def checkRow (a : Fin 6 → Fin n) : Eqn n :=
  let cs : Clause n := [⟨a 0,false⟩, ⟨a 1,true⟩, ⟨a 2,true⟩, ⟨a 3,true⟩, ⟨a 4,true⟩, ⟨a 5,true⟩]
  clauseRow cs

private theorem row_ok (a : Fin 6 → Fin n) (x : Point n) :
    (checkRow a).value x = true ↔
      x (a 5) = ((((x (a 0) ^^ x (a 1)) ^^ x (a 2)) ^^ x (a 3)) ^^ x (a 4)) := by
  simp only [checkRow, clauseRow, parity, holds]
  generalize x (a 0) = v0, x (a 1) = v1, x (a 2) = v2, x (a 3) = v3,
    x (a 4) = v4, x (a 5) = v5
  decide +revert

/-- At least n-m distinct coordinates can be prescribed independently for
m homogeneous socket rows on n variables, including dependent rows. -/
theorem free_coordinates (A : SocketRows n m) :
    ∃ cs : List (Fin n), cs.Nodup ∧ n ≤ cs.length+m ∧
      ∀ guess : Point n, ∃ x, Valid A x ∧ ∀ i ∈ cs, x i = guess i := by
  let rows := (List.finRange m).map (fun j => checkRow (A j))
  have ok (x : Point n) : (∀ q ∈ rows, q.value x = true) ↔ Valid A x := by
    simp [rows, row_ok, Valid]
  obtain ⟨b, ech, size, spec⟩ := basis_for rows (fun _ => false) ((ok _).2 (fun _ => rfl))
  let ps := (pivots b).toFinset
  let cs := psᶜ.toList
  have len : cs.length + ps.card = n := by
    have cap : ps.card ≤ n := by simpa using ps.card_le_univ
    simp [cs, Finset.card_compl, Nat.sub_add_cancel cap]
  have lim : ps.card ≤ m := by
    calc
      _ ≤ (pivots b).length := List.toFinset_card_le _
      _ = b.length := by simp [pivots]
      _ ≤ m := by simpa [rows] using size
  refine ⟨cs, Finset.nodup_toList _, by omega, ?_⟩
  intro guess
  let x := (repairPath b guess).foldl toggle guess
  refine ⟨x, (ok x).mp ((spec x).mp (repair_fits ech _)), ?_⟩
  intro i mem
  apply fold_untouched
  have outside : i ∉ pivots b := by simpa [cs, ps] using mem
  exact fun hp => outside (repair_sub guess hp)

end SatWalk.InformationSet
