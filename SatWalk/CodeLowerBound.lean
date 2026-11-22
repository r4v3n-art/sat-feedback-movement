import SatWalk.Model
import SatWalk.FeedbackBatches

namespace SatWalk.CodeLowerBound
open FeedbackCube FeedbackBatches Model

/-- Appending a single signed unit pin keeps every public check ahead of it. -/
def pin (F : Formula n) (i : Fin n) (b : Bool) : Formula n where
  clauses := F.clauses ++ [[⟨i, b⟩]]
  width := by
    intro c mem
    rcases List.mem_append.mp mem with old | new
    · exact F.width c old
    · simp at new; subst c; simp

theorem report_pin (F : Formula n) (i : Fin n) (b : Bool) (x : Point n) :
    orderedReport (pin F i b) x = (orderedReport F x).or
      (if x i = b then none else some [⟨i,b⟩]) := by
  by_cases h : x i = b <;>
    simp [pin, orderedReport, List.find?_append, isBroken, holds, h]

def restriction (D F : Formula n) : Prop := ∃ suffix, F.clauses = D.clauses ++ suffix

theorem under_pin {D F : Formula n} (sub : restriction D F) (i : Fin n) (b : Bool) :
    restriction D (pin F i b) := by
  obtain ⟨cs, eq⟩ := sub
  exact ⟨cs ++ [[⟨i,b⟩]], by simp [pin, eq, List.append_assoc]⟩

theorem agree_report {D F : Formula n} (sub : restriction D F) {x : Point n} {c}
    (h : orderedReport D x = some c) : orderedReport F x = some c := by
  obtain ⟨cs, eq⟩ := sub
  simp only [orderedReport, eq, List.find?_append]
  change (orderedReport D x).or _ = _
  rw [h]; rfl

theorem public_solved {D F : Formula n} (sub : restriction D F) {x : Point n}
    (h : orderedReport F x = none) : orderedReport D x = none := by
  cases e : orderedReport D x with
  | none => rfl
  | some c => rw [agree_report sub e] at h; contradiction

abbrev Config (n : Nat) (σ : Type) := σ × Point n

/-- This stronger search game allows any batch of length at most B. Refusal,
oversize batches and success leave the configuration fixed. A legal solver
therefore follows exactly its physical trajectory until its first success. -/
def step (B : Nat) (alg : Solver n σ) (r : Option (Clause n)) (s : Config n σ) : Config n σ :=
  match r with
  | none => s
  | some c =>
    match alg.respond s.1 s.2 c with
    | none => s
    | some (t, p) => if p.length ≤ B then (t, p.foldl toggle s.2) else s

def trajectory (B : Nat) (alg : Solver n σ) (F : Formula n) (start : Point n) : Nat → Config n σ
  | 0 => (alg.initial start, start)
  | t+1 =>
    let s := trajectory B alg F start t
    step B alg (orderedReport F s.2) s

theorem step_gap (x : Point n) (alg : Solver n σ) (r) (s : Config n σ) (B) :
    gap x (step B alg r s).2 ≤ gap x s.2 + B := by
  unfold step
  split
  · omega
  · split
    · omega
    · split
      · exact Nat.le_trans (guide_change ..) (Nat.add_le_add_left ‹_ ≤ B› _)
      · omega

theorem interval_gap (B : Nat) (alg : Solver n σ) (F : Formula n) (x : Point n) (t l : Nat) :
    gap (trajectory B alg F x t).2 (trajectory B alg F x (t+l)).2 ≤ l*B := by
  induction l with
  | zero => simp
  | succ l ih =>
    have h := step_gap (trajectory B alg F x t).2 alg
      (orderedReport F (trajectory B alg F x (t+l)).2) (trajectory B alg F x (t+l)) B
    exact Nat.le_trans h (by rw [Nat.succ_mul]; omega)

def Hit (B : Nat) (alg : Solver n σ) (F : Formula n) (x : Point n) (t : Nat) :=
  orderedReport F (trajectory B alg F x t).2 = none

private theorem least {P : Nat → Prop} (existsHit : ∃ t, P t) :
    ∃ t, P t ∧ ∀ j, P j → t ≤ j := by
  classical
  obtain ⟨t, ht⟩ := existsHit
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases smaller : ∃ j, j < t ∧ P j
    · obtain ⟨j, hj, yes⟩ := smaller
      exact ih j hj yes
    · exact ⟨t, ht, fun j yes => by
        by_cases le : t ≤ j
        · exact le
        · exact False.elim (smaller ⟨j, by omega, yes⟩)⟩

/-- On a terminating trajectory this is its first acceptance time. -/
noncomputable def first (B : Nat) (alg : Solver n σ) (F : Formula n) (x : Point n) : Nat := by
  classical
  exact if h : ∃ t, Hit B alg F x t then Classical.choose (least h) else 0

theorem first_spec {B} {alg : Solver n σ} {F : Formula n} {x} (h : ∃ t, Hit B alg F x t) :
    Hit B alg F x (first B alg F x) ∧ ∀ t, Hit B alg F x t → first B alg F x ≤ t := by
  simpa [first, h] using Classical.choose_spec (least h)

/-- Before a public-prefix formula accepts, its reports and the solver's
entire remembered state are identical on every extension of that prefix. -/
theorem prefix_coupling {B} {alg : Solver n σ} {D F : Formula n} {x t}
    (sub : restriction D F) (before : ∀ j < t, ¬ Hit B alg D x j) :
    trajectory B alg D x t = trajectory B alg F x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have earlier := ih (fun j hj => before j (by omega))
    cases e : orderedReport D (trajectory B alg D x t).2 with
    | none => exact False.elim (before t (by omega) e)
    | some c =>
      simp only [trajectory, ← earlier, e, agree_report sub e]

theorem prefix_first {B} {alg : Solver n σ} {D F : Formula n} {x}
    (sub : restriction D F) (finish : ∃ t, Hit B alg F x t) :
    (∃ t, Hit B alg D x t) ∧ first B alg D x ≤ first B alg F x ∧
      trajectory B alg D x (first B alg D x) = trajectory B alg F x (first B alg D x) := by
  classical
  let t := first B alg F x
  have early : ∃ j, j ≤ t ∧ Hit B alg D x j := by
    apply Classical.byContradiction
    intro no
    have same := prefix_coupling (B := B) (alg := alg) (x := x) sub
      (t := t) (fun j hj hit => no ⟨j, by omega, hit⟩)
    have hit := (first_spec finish).1
    unfold Hit at hit
    change orderedReport F (trajectory B alg F x t).2 = none at hit
    rw [← same] at hit
    exact no ⟨t, Nat.le_refl _, public_solved sub hit⟩
  obtain ⟨j, le, hj⟩ := early
  have spec := first_spec (Exists.intro j hj)
  exact ⟨⟨j,hj⟩, Nat.le_trans (spec.2 j hj) le,
    prefix_coupling sub (fun a lt yes => Nat.not_le_of_lt lt (spec.2 a yes))⟩

/-- The satisfying assignments of the public code formula are d-separated.
No assumption of linearity is needed for the movement charge. -/
def Separated (D : Formula n) (d : Nat) : Prop :=
  ∀ x y, orderedReport D x = none → orderedReport D y = none → x ≠ y → d ≤ gap x y

theorem wrong_child {B d : Nat} (pos : 0 < B) {alg : Solver n σ} {x : Point n}
    {D F : Formula n} (sub : restriction D F) (dist : Separated D d) (i : Fin n)
    (finish : ∀ b, ∃ t, Hit B alg (pin F i b) x t) :
    let t := first B alg F x
    let y := (trajectory B alg F x t).2
    ∀ b, y i ≠ b → t + turns B d ≤ first B alg (pin F i b) x := by
  let t := first B alg F x
  let y := (trajectory B alg F x t).2
  have related (b : Bool) : restriction F (pin F i b) := ⟨_,rfl⟩
  have h (b : Bool) := prefix_first (related b) (finish b)
  change ∀ b, y i ≠ b → t + turns B d ≤ first B alg (pin F i b) x
  intro b miss
  let child := pin F i b
  let u := first B alg child x
  let z := (trajectory B alg child x u).2
  have atY : orderedReport F y = none := (first_spec (h b).1).1
  have atZ : orderedReport child z = none := (first_spec (finish b)).1
  have val : z i = b := by
    by_cases ok : z i = b
    · exact ok
    · change orderedReport (pin F i b) z = none at atZ
      rw [report_pin, ite_eq_right ok] at atZ
      cases e : orderedReport F z <;> simp [e] at atZ
  have ne : y ≠ z := fun eq => miss (eq ▸ val)
  have far := dist y z (public_solved sub atY) (public_solved (under_pin sub i b) atZ) ne
  obtain ⟨l, eq⟩ := Nat.le.dest (h b).2.1
  have reach := interval_gap B alg child x t l
  change t + l = u at eq
  rw [eq] at reach
  have sync := congrArg Prod.snd (h b).2.2
  change y = (trajectory B alg child x t).2 at sync
  rw [← sync] at reach
  have charge := (turns_le pos d l).mpr (Nat.le_trans far reach)
  change t + turns B d ≤ u
  omega

private theorem siblings {B d : Nat} (pos : 0 < B) {alg : Solver n σ} {x : Point n}
    {D F : Formula n} (sub : restriction D F) (dist : Separated D d) (i : Fin n)
    (finish : ∀ b, ∃ t, Hit B alg (pin F i b) x t) :
    2 * first B alg F x + turns B d ≤
      first B alg (pin F i false) x + first B alg (pin F i true) x := by
  let t := first B alg F x
  let y := (trajectory B alg F x t).2
  have related (b : Bool) : restriction F (pin F i b) := ⟨_,rfl⟩
  have h (b : Bool) := prefix_first (related b) (finish b)
  have wrong : ∀ b, y i ≠ b → t + turns B d ≤ first B alg (pin F i b) x := wrong_child pos sub dist i finish
  have loF := (h false).2.1
  have loT := (h true).2.1
  change 2*t + _ ≤ _
  change t ≤ _ at loF loT
  cases hy : y i with
  | false => have := wrong true (by simp [hy]); omega
  | true => have := wrong false (by simp [hy]); omega

/-- Sum a statistic over every bit string on the ordered list of message pins.
Each leaf has multiplicity one, including when costs happen to coincide. -/
def leafSum [Add R] (f : Formula n → R) (F : Formula n) : List (Fin n) → R
  | [] => f F
  | i :: rest => leafSum f (pin F i false) rest + leafSum f (pin F i true) rest

def allLeaves (P : Formula n → Prop) (F : Formula n) : List (Fin n) → Prop
  | [] => P F
  | i :: rest => ∀ b, allLeaves P (pin F i b) rest

theorem prefix_terminates {B} {alg : Solver n σ} {x : Point n} {coords : List (Fin n)}
    {F : Formula n} (finish : allLeaves (fun G => ∃ t, Hit B alg G x t) F coords) :
    ∃ t, Hit B alg F x t := by
  induction coords generalizing F with
  | nil => exact finish
  | cons i rest ih => exact (prefix_first (D := F) ⟨_,rfl⟩ (ih (finish false))).1

/-- Uniform-secret information and movement charge, with doubled numerator
so that the exact half-integer mean is preserved. At each prefix, the first
publicly accepted word is common to both children. One child must travel at
least one code distance. This accounts for disjoint intervals along each path. -/
theorem code_charge {B d : Nat} (pos : 0 < B) (alg : Solver n σ) (x : Point n)
    (D : Formula n) (dist : Separated D d) (coords : List (Fin n))
    (finish : allLeaves (fun G => ∃ t, Hit B alg G x t) D coords) :
    coords.length * turns B d * 2^coords.length ≤
      2 * leafSum (fun G => first B alg G x) D coords := by
  have aux (F : Formula n) (sub : restriction D F) (cs : List (Fin n))
      (fin : allLeaves (fun G => ∃ t, Hit B alg G x t) F cs) :
      (2 * first B alg F x + cs.length * turns B d) * 2^cs.length ≤
        2 * leafSum (fun G => first B alg G x) F cs := by
    induction cs generalizing F with
    | nil => simp [leafSum]
    | cons i rest ih =>
      have left := ih _ (under_pin sub i false) (fin false)
      have right := ih _ (under_pin sub i true) (fin true)
      have both := siblings pos sub dist i (fun b => prefix_terminates (fin b))
      have scaled := Nat.mul_le_mul_right (2^rest.length) both
      simp only [List.length_cons, Nat.pow_succ, Nat.mul_two, Nat.succ_mul, leafSum, Nat.add_mul,
        Nat.mul_add, Nat.mul_assoc] at *
      omega
  have total := aux D ⟨[], by simp⟩ coords finish
  rw [Nat.add_mul] at total
  omega

end SatWalk.CodeLowerBound
