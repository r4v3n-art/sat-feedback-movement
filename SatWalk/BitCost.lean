import SatWalk.DenseMachine
import Mathlib.Tactic

namespace SatWalk.BitCost
open FeedbackCube DenseMachine

/-- The bit-operation model charges reads, writes and Boolean gates.
A vector operation scans its ports in order. A variable address is supplied
as a one-hot word. Indices stored in lists likewise occupy at most n+1 bits.
The clock counts the elementary operations in the chosen implementation,
independently of Lean's native runtime and of the reporter's work. -/
structure Timed (α : Type) where
  val : α
  ticks : Nat

def seq (a : Timed α) (k : α → Timed β) : Timed β :=
  let b := k a.val
  ⟨b.val,a.ticks+b.ticks⟩

def map (a : Timed α) (f : α → β) : Timed β := ⟨f a.val,a.ticks⟩

/-- A fixed wiring diagram for one output line. Input ports are bits already
available in registers. The last unit charged by a gate is its output write. -/
inductive Gate where
  | port : Bool → Gate
  | xor : Gate → Gate → Gate
  | both : Gate → Gate → Gate
  | neg : Gate → Gate

def Gate.run : Gate → Bool
  | .port b => b
  | .xor a b => a.run ^^ b.run
  | .both a b => a.run && b.run
  | .neg a => !a.run
def Gate.work : Gate → Nat
  | .port _ => 1
  | .xor a b | .both a b => a.work+b.work+2
  | .neg a => a.work+2

/-- Materialize a fresh dense output word. Fixed coordinate wiring is free.
Each output bit is written once, even when it merely copies an input port. -/
def word (f : Fin n → Gate) : Timed (Point n) :=
  ⟨FeedbackBasis.tabulate (fun i => (f i).run), (List.finRange n |>.map (fun i => (f i).work+1)).sum⟩

theorem word_work (f : Fin n → Gate) (k : Nat) (h : ∀ i, (f i).work+1 ≤ k) :
    (word f).ticks ≤ n*k := by
  have aux (l : List (Fin n)) : (l.map (fun i => (f i).work+1)).sum ≤ l.length*k := by
    induction l with
    | nil => simp
    | cons i l ih => have := h i; simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]; omega
  simpa [word] using aux (List.finRange n)

def xorWord (a b : Point n) := word (fun i => .xor (.port (a i)) (.port (b i)))
def unit (p : Fin n) : Point n := fun j => decide (j=p)

/-- A horizontal XOR of pairwise ANDs. It implements both the affine dot
product and a multiplexer addressed by a one-hot word. -/
def accum (a b : Point n) : List (Fin n) → Timed Bool
  | [] => ⟨false,1⟩
  | i::is => seq (accum a b is) fun tail =>
      let g := Gate.xor (.both (.port (a i)) (.port (b i))) (.port tail)
      ⟨g.run,g.work+1⟩

@[simp] theorem accum_val (a b : Point n) (l) : (accum a b l).val = DenseMachine.inner a b l := by
  induction l <;> simp_all [accum,seq,DenseMachine.inner,Gate.run]

@[simp] theorem accum_ticks (a b : Point n) (l) : (accum a b l).ticks = 8*l.length+1 := by
  induction l <;> simp_all [accum,seq,Gate.work] <;> omega

def read (a : Point n) (p : Fin n) := accum a (unit p) (List.finRange n)

@[simp] theorem read_val (a : Point n) (p : Fin n) : (read a p).val = a p := by
  have E (l : List (Fin n)) (nd : l.Nodup) :
      DenseMachine.inner a (unit p) l = (if p ∈ l then a p else false) := by
    induction l with
    | nil => simp [DenseMachine.inner]
    | cons i l ih =>
      obtain ⟨no,tail⟩ := List.nodup_cons.mp nd
      by_cases h : i=p
      · subst i; simp [DenseMachine.inner,unit,ih tail,no]
      · simp [DenseMachine.inner,unit,ih tail,h,Ne.symm h]
  simp [read,E _ (List.nodup_finRange _)]

def testRow (r : Row n) (h : Point n) :=
  seq (accum r.bits h (List.finRange n)) fun b =>
    let g := Gate.xor (.port r.bias) (.port b)
    ⟨g.run,g.work⟩

def merged (p : Fin n) (s q : Row n) : Timed (Row n) :=
  seq (read q.bits p) fun hit =>
    if hit then
      let v := xorWord q.bits s.bits
      let g := Gate.xor (.port q.bias) (.neg (.port s.bias))
      ⟨⟨g.run,v.val⟩,1+g.work+v.ticks⟩
    else ⟨q,1⟩

theorem merged_spec (p : Fin n) (s q : Row n) :
    (merged p s q).val = eliminate p s q ∧ (merged p s q).ticks ≤ 20*(n+1) := by
  have bnd := word_work (fun i => Gate.xor (.port (q.bits i)) (.port (s.bits i))) 5 (by intros; exact Nat.le_refl 5)
  have rd : (read q.bits p).ticks = 8*n+1 := by simp [read]
  have V : (xorWord q.bits s.bits).val = fun i => q.bits i ^^ s.bits i := by simp [xorWord,word,Gate.run]
  change (xorWord q.bits s.bits).ticks ≤ _ at bnd
  cases h : q.bits p <;> simp [merged,seq,read_val,h,eliminate,Gate.run,Gate.work,rd,V] <;> omega

def reducing (rs : Rows n) (q : Row n) : Timed (Row n) :=
  match rs with
  | [] => ⟨q,1⟩
  | (p,r)::tail => seq (reducing tail q) (merged p r)

theorem reducing_spec (rs : Rows n) (q : Row n) :
    (reducing rs q).val = reduce rs q ∧ (reducing rs q).ticks ≤ 1+rs.length*(20*(n+1)) := by
  induction rs with
  | nil => simp [reducing,reduce]
  | cons e rs ih =>
    rcases e with ⟨p,r⟩
    have H := merged_spec p r (reducing rs q).val
    simp only [reducing,seq,reduce,List.length_cons,Nat.succ_mul rs.length]; exact ⟨H.1.trans (ih.1 ▸ rfl),by have := ih.2; have := H.2; omega⟩

def repairing (rs : Rows n) (h : Point n) : Timed (Point n) :=
  match rs with
  | [] => ⟨h,1⟩
  | (p,r)::tail =>
    seq (testRow r h) fun yes =>
      let w := if yes then (⟨h,1⟩ : Timed _) else xorWord h (unit p)
      seq w (repairing tail)

theorem repairing_spec (rs : Rows n) (h : Point n) :
    (repairing rs h).val = repair rs h ∧ (repairing rs h).ticks ≤ 1+rs.length*(20*(n+1)) := by
  induction rs generalizing h with
  | nil => simp [repairing,repair]
  | cons e rs ih =>
    rcases e with ⟨p,r⟩
    have yes : (testRow r h).val = eval r h := by simp [testRow,seq,eval,Gate.run]
    have cost : (testRow r h).ticks = 8*n+5 := by simp [testRow,seq,Gate.work]
    have eq : (xorWord h (unit p)).val = toggle h p := by
      funext i; by_cases e : i=p <;> simp [xorWord,word,Gate.run,unit,toggle,e]
    have small := word_work (fun i => Gate.xor (.port (h i)) (.port (unit p i))) 5 (by intros; exact Nat.le_refl 5)
    change (xorWord h (unit p)).ticks ≤ _ at small
    cases val : eval r h <;> simp only [repairing,repair,seq,yes,cost,val,Bool.false_eq_true,ite_false,ite_true,FeedbackBasis.tabulate_eq,eq,List.length_cons,Nat.succ_mul rs.length]
    · exact ⟨(ih _).1,by have := (ih (toggle h p)).2; omega⟩
    · exact ⟨(ih _).1,by have := (ih h).2; omega⟩

end SatWalk.BitCost
