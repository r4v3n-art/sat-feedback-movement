import SatWalk.LDPCCode
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
namespace SatWalk.SimplexCode
open FeedbackCube Model ParityGadget Finset

/-- The usual binary simplex recursion. Retain the old forms, insert the new
message bit, then append the XOR of each old form with that bit. -/
def length : Nat → Nat
  | 0 => 0
  | k+1 => length k + (length k+1)

theorem length_eq (k : Nat) : length k+1=2^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [length,pow_succ,←ih]; omega

def left (j : Fin (length k)) : Fin (length (k+1)) := Fin.castAdd _ j
def mid (k : Nat) : Fin (length (k+1)) := Fin.natAdd (length k) (0 : Fin (length k+1))
def right (j : Fin (length k)) : Fin (length (k+1)) := Fin.natAdd (length k) j.succ
def join (a : Point (length k)) (b : Bool) : Point (length (k+1)) :=
  Fin.addCases a (Fin.cases b (fun j => a j ^^ b))

@[simp] theorem at_left (a : Point (length k)) b j : join a b (left j) = a j := by simp [join,left]
@[simp] theorem at_mid (a : Point (length k)) b : join a b (mid k) = b := by simp [join,mid]
@[simp] theorem at_right (a : Point (length k)) b j : join a b (right j) = (a j ^^ b) := by simp [join,right]

def word : (k : Nat) → Point k → Point (length k)
  | 0,_ => Fin.elim0
  | k+1,u => join (word k (Fin.tail u)) (u 0)

def key : (k : Nat) → Fin k → Fin (length k)
  | 0 => Fin.elim0
  | k+1 => Fin.cases (mid k) (fun i => left (key k i))

@[simp] theorem systematic (u : Point k) (i : Fin k) : word k u (key k i) = u i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [word,key]
    · simp [word,key,ih,Fin.tail]

theorem key_injective (k : Nat) : Function.Injective (key k) := by
  intro i j eq
  have h := congrArg (word k (fun a => decide (a=i))) eq
  exact (by simpa using h.symm : j=i).symm

def gates : (k : Nat) → List (Wires (length k))
  | 0 => []
  | k+1 => (gates k).map (fun (a,b,c) => (left a,left b,left c)) ++
      (List.finRange (length k)).map (fun j => (left j,mid k,right j))

theorem checks (k : Nat) (x : Point (length k)) :
    Checks (gates k) x ↔ x = word k (x ∘ key k) := by
  induction k with
  | zero => exact ⟨fun _ => funext (fun i => Fin.elim0 i),fun _ _ h => by cases h⟩
  | succ k ih =>
    let u := x ∘ left (k := k)
    have char : Checks (gates (k+1)) x ↔ Checks (gates k) u ∧ ∀ j, x (right j) = (u j ^^ x (mid k)) := by
      simp only [Checks,gates,List.forall_mem_append,List.forall_mem_map,List.mem_finRange,forall_true_left]
      constructor
      · rintro ⟨h,j⟩; exact ⟨fun ⟨a,b,c⟩ m => h _ m,j⟩
      · rintro ⟨h,j⟩; exact ⟨fun ⟨a,b,c⟩ m => h _ m,j⟩
    rw [char,ih]
    have tail : Fin.tail (x ∘ key (k+1)) = u ∘ key k := by funext j; rfl
    simp only [word,tail]
    constructor
    · rintro ⟨eq,h⟩
      funext i
      refine Fin.addCases (fun a => ?_) (fun v => ?_) i
      · exact (congrFun eq a).trans (at_left ..).symm
      · refine Fin.cases ?_ (fun j => ?_) v
        · exact (at_mid ..).symm
        · exact (h j).trans ((congrArg (fun z => z ^^ x (mid k)) (congrFun eq j)).trans (at_right ..).symm)
    · intro eq
      have L (i : Fin (length k)) := congrFun eq (left i)
      have R (i : Fin (length k)) := congrFun eq (right i)
      refine ⟨funext (fun i => (L i).trans (at_left ..)),fun j => ?_⟩
      rw [show u j = _ from (L j).trans (at_left ..)]
      exact (R j).trans (at_right ..)

def formula (k : Nat) := ParityGadget.encode (gates k)

theorem recognized (u : Point k) : OddWitness (formula k).clauses (word k u) := by
  apply (encode_spec ..).2.mpr
  apply (checks ..).mpr
  congr 1; funext i; simp

theorem solved_iff (x : Point (length k)) : Solved (formula k).clauses x ↔ x=word k (x ∘ key k) :=
  (encode_spec ..).1.trans (checks ..)

/-- The distance between halves of the recursive simplex words is doubled
when the new bit agrees. When it differs, each pair of corresponding
coordinates contributes exactly one difference. -/
theorem join_gap (a c : Point (length k)) (b d : Bool) :
    hammingDist (join a b) (join c d) =
      if b=d then 2*hammingDist a c else length k+1 := by
  rw [hammingDist,card_filter]
  change (∑ i : Fin (length k + (length k+1)), if join a b i ≠ join c d i then 1 else 0) = _
  rw [Fin.sum_univ_add]
  simp only [show ∀ i, join a b (Fin.castAdd (length k+1) i) = a i from at_left a b,
    show ∀ i, join c d (Fin.castAdd (length k+1) i) = c i from at_left c d]
  rw [Fin.sum_univ_succ]
  change (∑ i, if a i ≠ c i then 1 else 0) + ((if join a b (mid k) ≠ join c d (mid k) then 1 else 0) +
    ∑ i, if join a b (right i) ≠ join c d (right i) then 1 else 0) = _
  simp only [at_mid,at_right,hammingDist,card_filter]
  by_cases e : b=d
  · subst d; simp [two_mul]
  · rw [if_neg e]
    have pair (i : Fin (length k)) : (if a i ≠ c i then 1 else 0) + (if (a i ^^ b) ≠ (c i ^^ d) then 1 else 0) = 1 := by
      cases a i <;> cases c i <;> cases b <;> cases d <;> simp_all
    have sum := Finset.sum_congr (s₁ := (univ : Finset (Fin (length k)))) rfl (fun i _ => pair i)
    rw [Finset.sum_add_distrib] at sum
    simp at sum
    simp [e]; omega

theorem distance {u v : Point k} (ne : u ≠ v) :
    FeedbackCube.gap (word k u) (word k v) = 2^(k-1) := by
  rw [←LDPCCode.hamming_eq_gap]
  induction k with
  | zero => exact False.elim (ne (funext (fun i => Fin.elim0 i)))
  | succ k ih =>
    rw [word,word,join_gap]
    by_cases b : u 0=v 0
    · have tail : Fin.tail u ≠ Fin.tail v := by
        intro eq; apply ne; exact funext (Fin.cases b (fun i => congrFun eq i))
      rw [if_pos b,ih tail]
      have kp : 0<k := by
        by_contra! h
        obtain rfl : k=0 := by omega
        exact tail (funext (fun i => Fin.elim0 i))
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero kp.ne'
      simp [pow_succ,Nat.mul_comm]
    · simp [b,length_eq]

end SatWalk.SimplexCode
