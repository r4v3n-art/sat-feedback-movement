import SatWalk.FeedbackCube

namespace SatWalk.FeedbackBasis
open FeedbackCube

/-- Eagerly tabulate a point or coefficient vector, so repeated lookup cannot
re-evaluate an elimination tree. -/
def tabulate (f : Fin n → Bool) : Fin n → Bool :=
  let a := Array.ofFn f
  fun i => a[i.val]'(by simp [a])

@[simp] theorem tabulate_eq (f : Fin n → Bool) : tabulate f = f := by
  funext i; simp [tabulate]

private def xorPath (f : Fin n → Bool) : List (Fin n) → Bool
  | [] => false
  | i :: p => f i ^^ xorPath f p

private theorem path_value (q : Eqn n) (p : List (Fin n)) (x : Point n) :
    q.value (p.foldl toggle x) = (q.value x ^^ xorPath q.coeff p) := by
  induction p generalizing x with
  | nil => simp [xorPath]
  | cons i p ih => simp [List.foldl, ih, q.toggle, xorPath]

/-- A row stored by its value at zero and its dense coefficient vector. -/
def compact (q : Eqn n) : Eqn n :=
  let zero : Point n := fun _ => false
  let intercept := q.value zero
  let coeff := tabulate q.coeff
  let eval := fun x => intercept ^^ xorPath coeff (differences zero x)
  have correct (x : Point n) : eval x = q.value x := by
    simpa [eval, intercept, coeff, fold_plan (List.Perm.refl _)] using
      (path_value q (differences zero x) zero).symm
  { value := eval, coeff := coeff
    toggle := fun x i => by rw [correct, correct, q.toggle]; simp [coeff] }

private theorem row_ext {a b : Eqn n} (v : a.value = b.value) (c : a.coeff = b.coeff) : a = b := by
  cases a; cases b; congr

@[simp] theorem compact_eq (q : Eqn n) : compact q = q := by
  have hv : (compact q).value = q.value := by
    funext x
    let zero : Point n := fun _ => false
    simpa [compact, zero, fold_plan (List.Perm.refl _)] using
      (path_value q (differences zero x) zero).symm
  have hc : (compact q).coeff = q.coeff := tabulate_eq _
  exact row_ext hv hc

/-- Newest row first. Every row vanishes on every older pivot. -/
abbrev Basis (n : Nat) := List (Fin n × Eqn n)
def pivots (b : Basis n) := b.map Prod.fst
def Fits (b : Basis n) (x : Point n) := ∀ e ∈ b, e.2.value x = true

inductive Echelon : Basis n → Prop where
  | empty : Echelon []
  | add {b : Basis n} {p : Fin n} {q : Eqn n} (old : Echelon b)
      (lead : q.coeff p = true) (zeros : ∀ i ∈ pivots b, q.coeff i = false) :
      Echelon ((p, q) :: b)

theorem rank_le {b : Basis n} (e : Echelon b) : b.length ≤ n := by
  have nd : (pivots b).Nodup := by
    induction e with
    | empty => simp [pivots]
    | add old lead zeros ih =>
      apply List.nodup_cons.mpr
      exact ⟨fun mem => by rw [zeros _ mem] at lead; contradiction, ih⟩
  simpa [pivots] using nd.length_le_of_subset (l₂ := List.finRange n) (fun i _ => List.mem_finRange i)

/-- Coordinate of the binary sum of a selection of coefficient rows. -/
def sumCoeff : Basis n → Fin n → Bool
  | [], _ => false
  | (_,q) :: rows, i => q.coeff i ^^ sumCoeff rows i

/-- Over the binary field every nonzero linear combination selects a nonempty
sublist. Its sum has a nonzero coefficient at one of the stored pivots. -/
theorem independent {b : Basis n} (h : Echelon b) {rows : Basis n}
    (sel : rows.Sublist b) (ne : rows ≠ []) : ∃ i ∈ pivots b, sumCoeff rows i = true := by
  induction h generalizing rows with
  | empty => cases sel; contradiction
  | @add b p q old lead zeros ih =>
    cases sel with
    | cons _ sub =>
      obtain ⟨i, mem, hit⟩ := ih sub ne
      exact ⟨i, .tail _ mem, hit⟩
    | cons_cons _ sub =>
      rename_i tail
      by_cases empty : tail = []
      · subst tail
        exact ⟨p, .head _, by simp [sumCoeff, lead]⟩
      · obtain ⟨i, mem, hit⟩ := ih sub empty
        exact ⟨i, .tail _ mem, by simp [sumCoeff, zeros i mem, hit]⟩

def reduce : Basis n → Eqn n → Eqn n
  | [], q => q
  | (p, r) :: rest, q => Affine.eliminate r (reduce rest q) p

theorem reduce_value {b : Basis n} {x : Point n} (ok : Fits b x) (q : Eqn n) :
    (reduce b q).value x = q.value x := by
  induction b with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨p, r⟩ := e
    have yes : r.value x = true := ok (p,r) (.head _)
    have tail := ih (fun e mem => ok e (.tail _ mem))
    simp only [reduce, Affine.eliminate]
    split <;> simp [yes, tail]

theorem reduce_zeros {b : Basis n} (e : Echelon b) (q : Eqn n) :
    ∀ i ∈ pivots b, (reduce b q).coeff i = false := by
  induction e with
  | empty => simp [pivots]
  | @add b p r old lead zeros ih =>
    intro i mem
    rcases List.mem_cons.mp mem with rfl | h
    · simp only [reduce, Affine.eliminate]
      split <;> simp_all
    · simp only [reduce, Affine.eliminate]
      split <;> simp [ih _ h, zeros _ h]

theorem active_of_disagreement (q : Eqn n) {h w : Point n}
    (bad : q.value h = false) (good : q.value w = true) :
    ∃ i ∈ List.finRange n, q.coeff i = true := by
  apply Classical.byContradiction
  intro none
  have zero (i : Fin n) : q.coeff i = false := by
    cases e : q.coeff i with
    | true => exact False.elim (none ⟨i, List.mem_finRange _, e⟩)
    | false => rfl
  have const (path : List (Fin n)) (x : Point n) : q.value (path.foldl toggle x) = q.value x := by
    induction path generalizing x with
    | nil => rfl
    | cons a rest ih => simp [List.foldl, ih, q.toggle, zero]
  have same := const (differences h w) h
  rw [fold_plan (List.Perm.refl _), good, bad] at same
  contradiction

/-- Correct the newest row, then sweep older pivots. Each pivot is used at most once. -/
def repairPath : Basis n → Point n → List (Fin n)
  | [], _ => []
  | (p, r) :: b, x =>
    if r.value x then repairPath b x else p :: repairPath b (toggle x p)

theorem repair_sub {b : Basis n} (x : Point n) : repairPath b x ⊆ pivots b := by
  induction b generalizing x with
  | nil => simp [repairPath]
  | cons e b ih =>
    obtain ⟨p, r⟩ := e
    simp only [repairPath]; split
    · exact fun i mem => .tail _ (ih x mem)
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact .head _
      · exact .tail _ (ih _ h)

theorem repair_length (b : Basis n) (x : Point n) : (repairPath b x).length ≤ b.length := by
  induction b generalizing x with
  | nil => simp [repairPath]
  | cons e b ih =>
    obtain ⟨p, r⟩ := e
    simp only [repairPath, List.length_cons]; split
    · exact Nat.le_succ_of_le (ih _)
    · exact Nat.succ_le_succ (ih _)

private theorem unchanged (q : Eqn n) (p : List (Fin n)) (x : Point n)
    (zero : ∀ i ∈ p, q.coeff i = false) : q.value (p.foldl toggle x) = q.value x := by
  induction p generalizing x with
  | nil => rfl
  | cons i p ih =>
    simp [List.foldl, ih _ (fun j hj => zero j (.tail _ hj)), q.toggle, zero i (.head _)]

theorem repair_fits {b : Basis n} (e : Echelon b) (x : Point n) :
    Fits b ((repairPath b x).foldl toggle x) := by
  induction e generalizing x with
  | empty => simp [Fits]
  | @add b p r old lead zeros ih =>
    have keep (y : Point n) := unchanged r (repairPath b y) y
      (fun j hj => zeros j (repair_sub y hj))
    intro entry mem
    rcases List.mem_cons.mp mem with rfl | mem
    · simp only [repairPath]
      split
      · simpa [keep] using ‹r.value x = true›
      · simp_all [List.foldl, r.toggle]
    · simp only [repairPath]; split
      · exact ih x entry mem
      · exact ih (toggle x p) entry mem

end SatWalk.FeedbackBasis
