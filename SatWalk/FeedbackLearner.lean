import SatWalk.Model
import SatWalk.FeedbackBasis
import SatWalk.FeedbackBatches

namespace SatWalk.FeedbackLearner
open FeedbackCube FeedbackBasis FeedbackBatches

structure State (n : Nat) where
  point : Point n
  guide : Point n
  basis : Basis n

def initial (x : Point n) : State n := ⟨x, x, []⟩

export Model (Broken Solved OddWitness)

/-- Neither the hidden formula nor the promise witness is an algorithm input. -/
def prepare (s : State n) (c : Clause n) : Option (Basis n × List (Fin n)) :=
  if parity c s.guide then some (s.basis, [])
  else
    let q := compact (reduce s.basis (clauseRow c))
    ((List.finRange n).find? q.coeff).map fun p =>
      let b := (p, q) :: s.basis
      (b, repairPath b s.guide)

def advance (B : Nat) (s : State n) (c : Clause n) : Option (State n × List (Fin n)) := do
  let (b, corrections) ← prepare s c
  let h := tabulate (corrections.foldl toggle s.guide)
  let l ← c.find? (fun lit => holds lit h)
  let moves := batch B s.point h l.var
  return (⟨tabulate (moves.foldl toggle s.point), h, b⟩, moves)

structure Invariant (w : Point n) (s : State n) : Prop where
  echelon : Echelon s.basis
  guide : Fits s.basis s.guide
  witness : Fits s.basis w

private theorem prepare_spec {w : Point n} {s : State n} {c : Clause n}
    (inv : Invariant w s) (promise : parity c w = true) :
    ∃ b path, prepare s c = some (b, path) ∧
      Echelon b ∧ Fits b (path.foldl toggle s.guide) ∧ Fits b w ∧
      parity c (path.foldl toggle s.guide) = true ∧
      ((b = s.basis ∧ path = []) ∨
       (b.length = s.basis.length + 1 ∧ path.length ≤ b.length)) := by
  cases h : parity c s.guide with
  | true => exact ⟨s.basis, [], by simp [prepare, h], inv.echelon, inv.guide,
                    inv.witness, h, .inl ⟨rfl, rfl⟩⟩
  | false =>
    let q := reduce s.basis (clauseRow c)
    have qbad : q.value s.guide = false := (reduce_value inv.guide _).trans h
    have qgood : q.value w = true := (reduce_value inv.witness _).trans promise
    obtain ⟨p, hp⟩ : ∃ p, (List.finRange n).find? q.coeff = some p := by
      cases found : (List.finRange n).find? q.coeff with
      | some p => exact ⟨p, rfl⟩
      | none =>
        obtain ⟨i, mem, active⟩ := active_of_disagreement q qbad qgood
        exact False.elim (List.find?_eq_none.mp found i mem active)
    let b := (p, q) :: s.basis
    have eb : Echelon b := .add inv.echelon (List.find?_some hp) (reduce_zeros inv.echelon _)
    have gh := repair_fits eb s.guide
    have tail : Fits s.basis ((repairPath b s.guide).foldl toggle s.guide) :=
      fun e mem => gh e (.tail _ mem)
    have prepared : prepare s c = some (b, repairPath b s.guide) := by
      unfold prepare
      simp only [compact_eq]
      rw [ite_eq_right (by simp [h])]
      change (List.find? q.coeff (List.finRange n)).map _ = _
      rw [hp]
      rfl
    refine ⟨b, repairPath b s.guide, prepared, eb, gh, ?_, ?_,
            .inr ⟨rfl, repair_length ..⟩⟩
    · intro e mem
      rcases List.mem_cons.mp mem with rfl | he
      · exact qgood
      · exact inv.witness _ he
    · exact (reduce_value tail (clauseRow c)).symm.trans (gh (p,q) (.head _))

structure Legal (B : Nat) (s t : State n) (c : Clause n) (p : List (Fin n)) : Prop where
  distinct : p.Nodup
  withinBudget : p.length ≤ B
  includesReported : ∃ l ∈ c, l.var ∈ p
  resultingPoint : t.point = p.foldl toggle s.point

/-- On any genuine broken-clause report the deterministic update succeeds,
is a legal physical move, and satisfies the one-round amortized inequality. -/
theorem advance_charges {B : Nat} (pos : 0 < B) {w : Point n} {s : State n} {c : Clause n}
    (inv : Invariant w s) (promise : parity c w = true) (bad : Broken c s.point) :
    ∃ t p, advance B s c = some (t, p) ∧ Invariant w t ∧ Legal B s t c p ∧
      1 + turns B (gap t.point t.guide) + budget B s.basis.length ≤
        turns B (gap s.point s.guide) + budget B t.basis.length ∧
      p.length + gap t.point t.guide + Feedback.allowance s.basis.length ≤
        gap s.point s.guide + Feedback.allowance t.basis.length := by
  obtain ⟨b, path, prep, echelon, guide, wit, odd, growth⟩ := prepare_spec inv promise
  let h := path.foldl toggle s.guide
  obtain ⟨l, found⟩ : ∃ l, c.find? (fun v => holds v h) = some l := by
    cases choice : c.find? (fun v => holds v h) with
    | some l => exact ⟨l, rfl⟩
    | none =>
      obtain ⟨l, mem, yes⟩ := odd_has_literal odd
      exact False.elim (List.find?_eq_none.mp choice l mem yes)
  have mem := List.mem_of_find?_eq_some found
  have yes : holds l h = true := List.find?_some (p := fun v => holds v h) found
  have ne : s.point l.var ≠ h l.var := by
    intro eq
    have no := bad l mem
    unfold holds at no yes
    rw [eq, yes] at no
    contradiction
  let p := batch B s.point h l.var
  let t : State n := ⟨p.foldl toggle s.point, h, b⟩
  obtain ⟨nd, hit, len, residual⟩ := batch_spec pos ne
  have positive : 0 < gap s.point h :=
    List.length_pos_of_mem (mem_differences.mpr ne)
  have down := descend pos positive residual
  refine ⟨t, p, by simp [advance, prep, found, h, p, t], ⟨echelon, guide, wit⟩,
          ⟨nd, by rw [show p.length = _ from len]; exact Nat.min_le_left .., ⟨l, mem, hit⟩, rfl⟩, ?_⟩
  constructor
  · change 1 + turns B (gap (p.foldl toggle s.point) h) + _ ≤ _ + budget B b.length
    change turns B (gap (p.foldl toggle s.point) h) + 1 ≤ turns B (gap s.point h) at down
    rcases growth with ⟨rfl, rfl⟩ | ⟨rank, cost⟩
    · change turns B (gap (p.foldl toggle s.point) h) + 1 ≤ turns B (gap s.point s.guide) at down
      omega
    · have distance : gap s.point h ≤ gap s.point s.guide + (s.basis.length+1) :=
        Nat.le_trans (guide_change s.point s.guide path) (Nat.add_le_add_left (rank ▸ cost) _)
      have up := climb pos distance
      rw [rank, budget]
      omega
  · change p.length + gap (p.foldl toggle s.point) h + Feedback.allowance s.basis.length ≤
      gap s.point s.guide + Feedback.allowance b.length
    have walk : p.length + gap (p.foldl toggle s.point) h ≤ gap s.point h := by
      change p.length = min B (gap s.point h) at len
      change gap (p.foldl toggle s.point) h ≤ gap s.point h-B at residual
      omega
    rcases growth with ⟨rfl,rfl⟩ | ⟨rank,cost⟩
    · exact Nat.add_le_add_right walk _
    · have dist := guide_change s.point s.guide path
      change gap s.point h ≤ _ at dist
      rw [rank,Feedback.allowance]; omega

theorem advance_spec {B : Nat} (pos : 0 < B) {w : Point n} {s : State n} {c : Clause n}
    (inv : Invariant w s) (promise : parity c w = true) (bad : Broken c s.point) :
    ∃ t p, advance B s c = some (t, p) ∧ Invariant w t ∧ Legal B s t c p ∧
      1 + turns B (gap t.point t.guide) + budget B s.basis.length ≤
        turns B (gap s.point s.guide) + budget B t.basis.length := by
  obtain ⟨t,p,a,i,l,steps,_⟩ := advance_charges pos inv promise bad
  exact ⟨t,p,a,i,l,steps⟩

/-- Any legal adaptive reporting history, starting from the given assignment. -/
inductive Run (B : Nat) (cs : List (Clause n)) (x : Point n) : Nat → State n → Prop where
  | start : Run B cs x 0 (initial x)
  | step {m s t p c} (prior : Run B cs x m s) (report : c ∈ cs)
      (broken : Broken c s.point) (update : advance B s c = some (t, p)) :
      Run B cs x (m+1) t

theorem run_bound {B : Nat} (pos : 0 < B) {cs : List (Clause n)} {w x : Point n}
    (promise : OddWitness cs w) {m s} (run : Run B cs x m s) :
    Invariant w s ∧ m + turns B (gap s.point s.guide) ≤ budget B s.basis.length := by
  induction run with
  | start =>
    exact ⟨⟨.empty, by simp [initial, Fits], by simp [initial, Fits]⟩,
      by simp [initial, budget, turns_zero pos]⟩
  | step prior report broken update ih =>
    obtain ⟨t, p, eq, inv, _, charge⟩ := advance_spec pos ih.1 (promise _ report) broken
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (eq.symm.trans update))
    exact ⟨inv, by have := ih.2; omega⟩

theorem moves_at_most {B : Nat} (pos : 0 < B) {cs : List (Clause n)} {w x : Point n}
    (promise : OddWitness cs w) {m s} (run : Run B cs x m s) : m ≤ budget B n := by
  obtain ⟨inv, amortized⟩ := run_bound pos promise run
  exact Nat.le_trans (Nat.le_add_right ..) (Nat.le_trans amortized (budget_mono B (rank_le inv.echelon)))

/-- On reaching the global budget, the assignment already satisfies every clause.
Together with advance_spec, this excludes both an infinite run and early failure. -/
theorem solved_at_budget {B : Nat} (pos : 0 < B) {cs : List (Clause n)} {w x : Point n}
    (promise : OddWitness cs w) {s} (run : Run B cs x (budget B n) s) : Solved cs s.point := by
  intro c mem broken
  have inv := (run_bound pos promise run).1
  obtain ⟨t, p, eq, _⟩ := advance_spec pos inv (promise c mem) broken
  have tooLong := moves_at_most pos promise (.step run mem broken eq)
  omega

/-- A bounded driver. The oracle reports success with none or supplies a clause.
The separate Run theorem also covers history-dependent clause selection. -/
def play (B : Nat) (report : Nat → Point n → Option (Clause n)) : Nat → Nat → State n → State n
  | 0, _, s => s
  | fuel+1, m, s =>
    match report m s.point with
    | none => s
    | some c =>
      match advance B s c with
      | none => s
      | some (t, _) => play B report fuel (m+1) t

/-- The implemented learner actually returns a SAT assignment within the stated
fuel on every promised formula, from any start and for every honest reporter. -/
theorem play_solves {B : Nat} (pos : 0 < B) (cs : List (Clause n)) (x w : Point n)
    (promise : OddWitness cs w) (report : Nat → Point n → Option (Clause n))
    (accept : ∀ m y, report m y = none → Solved cs y)
    (reject : ∀ m y c, report m y = some c → c ∈ cs ∧ Broken c y) :
    Solved cs (play B report (budget B n) 0 (initial x)).point := by
  have aux (fuel m : Nat) (s : State n) (run : Run B cs x m s) (cap : m+fuel = budget B n) :
      Solved cs (play B report fuel m s).point := by
    induction fuel generalizing m s with
    | zero => exact solved_at_budget pos promise (by simpa [play, ← cap] using run)
    | succ k ih =>
      cases hr : report m s.point with
      | none => simpa [play, hr] using accept m _ hr
      | some c =>
        obtain ⟨mem, bad⟩ := reject _ _ _ hr
        obtain ⟨t, p, ht, _⟩ := advance_spec pos (run_bound pos promise run).1 (promise _ mem) bad
        simpa [play, hr, ht] using ih (m+1) t (.step run mem bad ht) (by omega)
  exact aux _ 0 _ .start (by simp)

end SatWalk.FeedbackLearner
