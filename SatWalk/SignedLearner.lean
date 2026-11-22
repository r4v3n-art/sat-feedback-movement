import SatWalk.UpperBound
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace SatWalk.SignedLearner
open FeedbackCube Model

/-- A uniformly sampled internal coordinate order and independent bit mask. -/
abbrev Frame (n : Nat) := Equiv.Perm (Fin n) × Point n

def point (g : Frame n) (x : Point n) : Point n := fun i => x (g.1.symm i) ^^ g.2 i
def lit (g : Frame n) (l : Literal n) : Literal n := ⟨g.1 l.var, l.value ^^ g.2 (g.1 l.var)⟩
def compose (g h : Frame n) : Frame n := (g.1.trans h.1, point h g.2)

private def key (l : Literal n) := 2*l.var.val + l.value.toNat
private theorem key_inj : Function.Injective (key (n := n)) := by
  rintro ⟨a,u⟩ ⟨b,v⟩ eq
  cases u <;> cases v <;> simp [key] at eq <;> first | omega | (congr 1; exact Fin.ext eq)
private local instance : LinearOrder (Literal n) := LinearOrder.lift' key key_inj

/-- Sorting inside the private frame makes the learner insensitive to the
presentation order of the reported literals, including repeated positions. -/
def clause (g : Frame n) (c : Clause n) : Clause n := ((c.map (lit g) : List _) : Multiset _).sort
theorem clause_perm (g : Frame n) (c : Clause n) : (clause g c).Perm (c.map (lit g)) :=
  Quotient.exact (Multiset.sort_eq ..)
theorem clause_congr (g : Frame n) {c d : Clause n} (h : c.Perm d) : clause g c = clause g d :=
  congrArg (fun s : Multiset (Literal n) => s.sort (· ≤ ·)) (Quotient.sound (h.map (lit g)))

def formula (g : Frame n) (F : Formula n) : Formula n where
  clauses := F.clauses.map (clause g)
  width := by
    rintro _ h
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp h
    simpa [(clause_perm g c).length_eq] using F.width c hc

private theorem same_truth (g : Frame n) (l : Literal n) (x : Point n) :
    holds (lit g l) (point g x) = holds l x := by
  simp only [lit,point,holds,Equiv.symm_apply_apply]
  cases x l.var <;> cases l.value <;> cases g.2 (g.1 l.var) <;> rfl

private theorem perm_parity {c d : Clause n} (eq : c.Perm d) (x : Point n) : parity c x = parity d x := by
  induction eq with
  | nil => rfl
  | cons l _ ih => simp [parity,ih]
  | swap a b c => simp [parity,Bool.xor_left_comm]
  | trans _ _ a b => exact a.trans b

theorem promise {F : Formula n} {w : Point n} (g : Frame n) (hw : OddWitness F.clauses w) :
    OddWitness (formula g F).clauses (point g w) := by
  rintro _ h; obtain ⟨c,mem,rfl⟩ := List.mem_map.mp h
  rw [perm_parity (clause_perm g c)]
  have e (ls : Clause n) : parity (ls.map (lit g)) (point g w) = parity ls w := by
    induction ls with
    | nil => rfl
    | cons l ls ih => simp [parity,same_truth,ih]
  exact (e c).trans (hw c mem)

theorem report_iff (g : Frame n) (F : Formula n) (x : Point n) (c : Clause n)
    (_mem : c ∈ F.clauses) : Broken (clause g c) (point g x) ↔ Broken c x := by
  simp only [Broken, (clause_perm g c).mem_iff, List.forall_mem_map, same_truth]

private theorem toggle_map (g : Frame n) (x : Point n) (i : Fin n) :
    point g (toggle x i) = toggle (point g x) (g.1 i) := by
  funext j
  by_cases h : j=g.1 i
  · subst j; simp [toggle,point]
  · have h' : g.1.symm j ≠ i := fun e => h ((g.1.symm_apply_eq).mp e)
    simp [toggle,point,h,h']
private theorem fold_map (g : Frame n) (x : Point n) (p : List (Fin n)) :
    point g (p.foldl toggle x) = (p.map g.1).foldl toggle (point g x) := by
  induction p generalizing x with
  | nil => rfl
  | cons i p ih => simp [ih,toggle_map]

def back (g : Frame n) (o : Option (σ × List (Fin n))) := o.map (fun (s,p) => (s,p.map g.1.symm))
def solver (g : Frame n) (B : Nat) : Solver n (FeedbackLearner.State n) where
  initial x := (paritySolver n B).initial (point g x)
  respond s x c := back g ((paritySolver n B).respond s (point g x) (clause g c))

private theorem response (g : Frame n) (B : Nat) (s x c t p)
    (h : (solver g B).respond s x c = some (t,p)) :
    (paritySolver n B).respond s (point g x) (clause g c) = some (t,p.map g.1) := by
  change back g _ = _ at h
  cases eq : (paritySolver n B).respond s (point g x) (clause g c) with
  | none => simp [back,eq] at h
  | some z =>
    rcases z with ⟨s',q⟩
    simp [back,eq] at h
    obtain ⟨rfl,rfl⟩ := h
    simp

theorem transport (g : Frame n) {F : Formula n} {start : Point n} {B m s x}
    (run : Run B F (solver g B) start m s x) :
    Run B (formula g F) (paritySolver n B) (point g start) m s (point g x) := by
  induction run with
  | init => exact .init
  | @step m s x c t p prior rep resp legal ih =>
    rw [fold_map]
    apply Run.step ih (c := clause g c)
    · exact ⟨List.mem_map.mpr ⟨c,rep.1,rfl⟩,(report_iff g F x c rep.1).mpr rep.2⟩
    · exact response g B s x c t p resp
    · obtain ⟨l,mem,hit⟩ := legal.includesReported
      exact ⟨legal.distinct.map g.1.injective, by simpa using legal.withinBudget,
        lit g l,(clause_perm ..).mem_iff.mpr (List.mem_map.mpr ⟨l,mem,rfl⟩),
        List.mem_map.mpr ⟨l.var,hit,rfl⟩⟩

theorem pathwise (g : Frame n) {F : Formula n} {start w : Point n} {m s x}
    (hw : OddWitness F.clauses w) (run : Run 1 F (solver g 1) start m s x) :
    m ≤ n*(n+1)/2 := by
  obtain ⟨hr,_,_,hm⟩ := theorem_upper_bound (by decide : 0 < 1) (promise g hw) (transport g run)
  exact (hm rfl).trans (Nat.div_le_div_right (Nat.mul_le_mul hr (by omega)))

theorem progress (g : Frame n) {F : Formula n} {start w : Point n} {m s x c}
    (hw : OddWitness F.clauses w) (run : Run 1 F (solver g 1) start m s x)
    (rep : Honest F x (some c)) :
    ∃ t p, (solver g 1).respond s x c = some (t,p) ∧ LegalMove 1 c p := by
  have R : Honest (formula g F) (point g x) (some (clause g c)) :=
    ⟨List.mem_map.mpr ⟨c,rep.1,rfl⟩,(report_iff g F x c rep.1).mpr rep.2⟩
  obtain ⟨t,q,res,leg⟩ := paritySolver_progress (by decide : 0<1) (promise g hw) (transport g run) R
  obtain ⟨l,lc,hv⟩ := leg.includesReported
  obtain ⟨l',mem,rfl⟩ := List.mem_map.mp ((clause_perm ..).mem_iff.mp lc)
  refine ⟨t,q.map g.1.symm,by simp [solver,back,res],leg.distinct.map g.1.symm.injective,
    by simpa using leg.withinBudget,l',mem,?_⟩
  exact List.mem_map.mpr ⟨g.1 l'.var,hv,g.1.symm_apply_apply _⟩

theorem at_budget (g : Frame n) {F : Formula n} {start w : Point n} {s x}
    (hw : OddWitness F.clauses w) (run : Run 1 F (solver g 1) start (n*(n+1)/2) s x) :
    Solved F.clauses x := by
  intro c mem bad
  obtain ⟨t,p,resp,leg⟩ := progress g hw run (c := c) ⟨mem,bad⟩
  have bound := pathwise g hw (run.step ⟨mem,bad⟩ resp leg)
  omega

/-- The bijection of frame tapes for an outside change of coordinates. -/
def reindex (g : Frame n) : Frame n ≃ Frame n where
  toFun h := compose g h
  invFun h := (g.1.symm.trans h.1, fun i => h.2 i ^^ g.2 (g.1 (h.1.symm i)))
  left_inv h := by
    apply Prod.ext
    · ext i; simp [compose]
    · funext i; simp [compose,point]; cases h.2 i <;> simp
  right_inv h := by
    apply Prod.ext
    · ext i; simp [compose]
    · funext i; simp [compose,point]; cases h.2 i <;> simp

theorem point_comp (g h : Frame n) (x : Point n) : point h (point g x) = point (compose g h) x := by
  funext i; simp [point,compose]
theorem clause_comp (g h : Frame n) (c : Clause n) :
    clause h (c.map (lit g)) = clause (compose g h) c := by
  have eq : lit h ∘ lit g = lit (compose g h) := by
    funext l; cases l; simp [lit,compose,point]
  simp [clause,List.map_map,eq]

/-- Same initial memory and transported response on paired tapes, for every
state and input. The pairing is a permutation of the entire uniform tape space,
so it couples complete adaptive histories, not just one-step marginals. -/
theorem equivariant (g : Frame n) :
    ∃ e : Frame n ≃ Frame n, ∀ h B,
      (∀ x, (solver h B).initial (point g x) = (solver (e h) B).initial x) ∧
      ∀ s x c, (solver (e h) B).respond s x c =
        back g ((solver h B).respond s (point g x) (c.map (lit g))) := by
  refine ⟨reindex g,fun h B => ⟨fun x => by simp [solver,reindex,point_comp], fun s x c => ?_⟩⟩
  simp only [solver,reindex,Equiv.coe_fn_mk,point_comp,clause_comp]
  cases (paritySolver n B).respond s (point (compose g h) x) (clause (compose g h) c) with
  | none => rfl
  | some z => rcases z with ⟨s',q⟩; simp [back,compose,List.map_map,Function.comp_def]

end SatWalk.SignedLearner
