import SatWalk.FeedbackCube

namespace SatWalk.Model
open FeedbackCube

/-- Signed clause positions are counted with multiplicity. The oracle discloses
the reported clause, including its signs and indices. -/
structure Formula (n : Nat) where
  clauses : List (Clause n)
  width : ∀ c ∈ clauses, c.length ≤ 3

def Broken (c : Clause n) (x : Point n) := ∀ l ∈ c, holds l x = false
def Solved (cs : List (Clause n)) (x : Point n) := ∀ c ∈ cs, ¬ Broken c x
def OddWitness (cs : List (Clause n)) (w : Point n) := ∀ c ∈ cs, parity c w = true

def isBroken (c : Clause n) (x : Point n) := !(c.any fun l => holds l x)
@[simp] theorem isBroken_iff (c : Clause n) (x : Point n) :
    isBroken c x = true ↔ Broken c x := by simp [isBroken, Broken]

/-- An honest oracle may choose adaptively among the currently violated clauses.
Success is reported exactly when no violated clause remains. -/
def Honest (F : Formula n) (x : Point n) : Option (Clause n) → Prop
  | none => Solved F.clauses x
  | some c => c ∈ F.clauses ∧ Broken c x

def orderedReport (F : Formula n) (x : Point n) :=
  F.clauses.find? fun c => isBroken c x

theorem ordered_honest (F : Formula n) (x : Point n) : Honest F x (orderedReport F x) := by
  unfold orderedReport
  cases e : F.clauses.find? (fun c => isBroken c x) with
  | none =>
    exact fun c mem bad => List.find?_eq_none.mp e c mem ((isBroken_iff ..).mpr bad)
  | some c =>
    exact ⟨List.mem_of_find?_eq_some e, (isBroken_iff ..).mp
      (List.find?_some (p := fun v => isBroken v x) e)⟩

/-- Each clause occurrence contributes one ticket. Sampling a uniform index
from this list implements uniform violated-clause feedback. -/
def violations (F : Formula n) (x : Point n) := F.clauses.filter fun c => isBroken c x

theorem mem_violations {F : Formula n} {x : Point n} {c : Clause n} :
    c ∈ violations F x ↔ Honest F x (some c) := by simp [violations, Honest]

theorem no_violations {F : Formula n} {x : Point n} :
    violations F x = [] ↔ Honest F x none := by
  constructor
  · intro empty c mem bad
    have contra := (mem_violations (F := F) (x := x) (c := c)).mpr ⟨mem, bad⟩
    simp [empty] at contra
  · intro solved
    cases e : violations F x with
    | nil => rfl
    | cons v vs =>
      have mem : v ∈ violations F x := e ▸ List.Mem.head _
      exact False.elim ((solved v (mem_violations.mp mem).1) (mem_violations.mp mem).2)

/-- A ticket is an index into the violated occurrences. A uniform draw from
this finite index type gives the uniform violated-clause reporter. -/
def ticketReport (F : Formula n) (x : Point n)
    (draw : (k : Nat) → 0 < k → Fin k) : Option (Clause n) :=
  let cs := violations F x
  if h : 0 < cs.length then some cs[draw cs.length h] else none

theorem ticket_honest (F : Formula n) (x : Point n) (draw) :
    Honest F x (ticketReport F x draw) := by
  unfold ticketReport
  dsimp only
  split
  · exact mem_violations.mp (List.getElem_mem ..)
  · exact no_violations.mp (List.length_eq_zero_iff.mp (by omega))

/-- The list specifies distinct simultaneous flips. The new assignment is
literally their application. There is no transition for a restart or final jump. -/
structure LegalMove (B : Nat) (c : Clause n) (p : List (Fin n)) : Prop where
  distinct : p.Nodup
  withinBudget : p.length ≤ B
  includesReported : ∃ l ∈ c, l.var ∈ p

/-- State can contain arbitrary history. None represents failure to produce a
move. An upper bound must separately exclude that possibility on reachable states. -/
structure Solver (n : Nat) (σ : Type) where
  initial : Point n → σ
  respond : σ → Point n → Clause n → Option (σ × List (Fin n))

/-- The complete random tape is fixed independently of the hidden instance.
For a fixed tape the machine is deterministic, including any remembered choices.
The tape law is an argument to probabilistic claims, not to a solver step. -/
abbrev RandomizedSolver (n : Nat) (σ Tape : Type) := Tape → Solver n σ

/-- Every finite history permitted by the oracle model. The first point is given
for free; subsequent points are obtained only by the reported physical moves. -/
inductive Run (B : Nat) (F : Formula n) (alg : Solver n σ) (start : Point n) :
    Nat → σ → Point n → Prop where
  | init : Run B F alg start 0 (alg.initial start) start
  | step {m s x c t p} (prior : Run B F alg start m s x)
      (report : Honest F x (some c)) (response : alg.respond s x c = some (t, p))
      (legal : LegalMove B c p) :
      Run B F alg start (m+1) t (p.foldl toggle x)

end SatWalk.Model
