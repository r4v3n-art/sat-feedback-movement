import SatWalk.UpperBound
import Mathlib.Tactic

namespace SatWalk.DenseMachine
open FeedbackCube FeedbackBasis FeedbackLearner

/-- A dense bit row contains only its intercept and its n coefficients. The
pivot is stored separately. No oracle for evaluating an affine row is needed. -/
structure Row (n : Nat) where
  bias : Bool
  bits : Point n

def encode (q : Eqn n) : Row n := ⟨q.value (fun _ => false), q.coeff⟩

def inner (a x : Point n) : List (Fin n) → Bool
  | [] => false
  | i :: is => (a i && x i) ^^ inner a x is

def eval (r : Row n) (x : Point n) := r.bias ^^ inner r.bits x (List.finRange n)

private theorem inner_toggle (a x : Point n) (l : List (Fin n)) (nd : l.Nodup) (j : Fin n) :
    inner a (toggle x j) l = (inner a x l ^^ (decide (j ∈ l) && a j)) := by
  induction l with
  | nil => simp [inner]
  | cons i l ih =>
    obtain ⟨no,tail⟩ := List.nodup_cons.mp nd
    by_cases eq : i = j
    · subst i; simp [inner,ih tail,no,toggle]
      cases a j <;> cases x j <;> cases inner a x l <;> rfl
    · have e : j ≠ i := Ne.symm eq
      simp [inner,ih tail,toggle,eq,e]

def decode (r : Row n) : Eqn n where
  value := eval r
  coeff := r.bits
  toggle := fun x i => by
    simp [eval,inner_toggle _ _ _ (List.nodup_finRange _) _]

private theorem extRow {a b : Eqn n} (v : a.value = b.value) (c : a.coeff = b.coeff) : a = b := by
  cases a; cases b; congr

theorem decode_encode (q : Eqn n) : decode (encode q) = q := by
  refine extRow (a := decode (encode q)) (b := q) ?_ rfl
  funext x
  let z : Point n := fun _ => false
  have inn (l : List (Fin n)) : inner q.coeff z l = false := by induction l <;> simp_all [inner,z]
  have base : (decode (encode q)).value z = q.value z := by simp [decode,encode,eval,inn,z]
  have path (p : List (Fin n)) (y : Point n) (ok : (decode (encode q)).value y = q.value y) :
      (decode (encode q)).value (p.foldl toggle y) = q.value (p.foldl toggle y) := by
    induction p generalizing y with
    | nil => exact ok
    | cons i p ih =>
      apply ih
      rw [(decode (encode q)).toggle,q.toggle,ok]; rfl
  exact (fold_plan (x := z) (y := x) (List.Perm.refl _)) ▸ path (differences z x) z base

theorem encode_decode (r : Row n) : encode (decode r) = r := by
  have zero (l : List (Fin n)) : inner r.bits (fun _ => false) l = false := by
    induction l <;> simp_all [inner]
  cases r
  simp_all [encode,decode,eval]

abbrev Rows (n : Nat) := List (Fin n × Row n)
def basis (rs : Rows n) : Basis n := rs.map (fun (p,r) => (p,decode r))

def eliminate (p : Fin n) (s q : Row n) : Row n :=
  if q.bits p then ⟨q.bias ^^ !s.bias, tabulate (fun i => q.bits i ^^ s.bits i)⟩ else q

theorem eliminate_eq (p : Fin n) (s q : Row n) :
    decode (eliminate p s q) = Affine.eliminate (decode s) (decode q) p := by
  rw [←decode_encode (Affine.eliminate ..)]
  congr 1
  have B (r : Row n) : eval r (fun _ => false) = r.bias := congrArg Row.bias (encode_decode r)
  cases h : q.bits p <;> simp [eliminate,Affine.eliminate,encode,h,decode,B]

def reduce (rs : Rows n) (q : Row n) : Row n :=
  match rs with
  | [] => q
  | (p,r)::rest => eliminate p r (reduce rest q)

theorem reduce_eq (rs : Rows n) (q : Row n) :
    decode (reduce rs q) = FeedbackBasis.reduce (basis rs) (decode q) := by
  induction rs with
  | nil => rfl
  | cons e rs ih => cases e; simp [reduce,basis,FeedbackBasis.reduce,eliminate_eq,ih,basis] at *

/-- Sweep the pivot rows with an explicit dense guide buffer. -/
def repair (rs : Rows n) (h : Point n) : Point n :=
  match rs with
  | [] => h
  | (p,r)::rest => repair rest (if eval r h then h else tabulate (toggle h p))

theorem repair_eq (rs : Rows n) (h : Point n) :
    repair rs h = (repairPath (basis rs) h).foldl toggle h := by
  induction rs generalizing h with
  | nil => rfl
  | cons e rs ih =>
    rcases e with ⟨p,r⟩
    cases e : eval r h <;> simp [repair,basis,repairPath,decode,e,ih,basis]

structure Data (n : Nat) where
  point : Point n
  guide : Point n
  rows : Rows n

def view (s : Data n) : State n := ⟨s.point,s.guide,basis s.rows⟩
def init (x : Point n) : Data n := ⟨x,x,[]⟩

def setup (s : Data n) (c : Clause n) : Option (Rows n × Point n) :=
  if parity c s.guide then some (s.rows,s.guide)
  else
    let q := reduce s.rows (encode (clauseRow c))
    ((List.finRange n).find? q.bits).map fun p =>
      let rs := (p,q)::s.rows
      (rs,repair rs s.guide)

theorem setup_eq (s : Data n) (c : Clause n) :
    (setup s c).map (fun (rs,h) => (basis rs,h)) =
    (prepare (view s) c).map (fun (rs,p) => (rs,p.foldl toggle s.guide)) := by
  have eq := reduce_eq s.rows (encode (clauseRow c))
  rw [decode_encode] at eq
  have bits := congrArg Affine.Row.coeff eq
  change (reduce s.rows (encode (clauseRow c))).bits = _ at bits
  simp only [setup,prepare,view,compact_eq]
  split
  · rfl
  · rw [bits]
    cases (List.finRange n).find? (FeedbackBasis.reduce (basis s.rows) (clauseRow c)).coeff with
    | none => rfl
    | some p =>
      simp [repair_eq,basis,eq] at *

def update (B : Nat) (s : Data n) (c : Clause n) : Option (Data n × List (Fin n)) := do
  let (rs,h) ← setup s c
  let l ← c.find? (fun l => holds l h)
  let p := batch B s.point h l.var
  return (⟨tabulate (p.foldl toggle s.point),h,rs⟩,p)

/-- The concrete dense-row machine refines the movement theorem's solver
including its choice of pivot, physical flips, next point and stored rows. -/
theorem update_eq (B : Nat) (s : Data n) (c : Clause n) :
    (update B s c).map (fun (t,p) => (view t,p)) = advance B (view s) c := by
  have h := setup_eq s c
  cases a : setup s c with
  | none =>
    cases b : prepare (view s) c <;> simp_all [update,advance]
  | some v =>
    rcases v with ⟨rs,h'⟩
    cases b : prepare (view s) c with
    | none => simp_all
    | some w =>
      rcases w with ⟨rows,p⟩
      obtain ⟨rfl,rfl⟩ : basis rs = rows ∧ h' = p.foldl toggle s.guide := by simpa [a,b] using h
      unfold update advance
      rw [a,b]
      simp [view,tabulate_eq,bind,Option.bind, pure]
      cases c.find? (fun l => holds l (p.foldl toggle s.guide)) <;> rfl

end SatWalk.DenseMachine
