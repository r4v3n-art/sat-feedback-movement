import SatWalk.BitCost

namespace SatWalk.TimedSearch
open FeedbackCube DenseMachine BitCost

/-- Report input is a list of at most three signed one-hot addresses. For each
literal, XOR its indicator into the coefficient word and its value at zero into
the intercept. This counts repeated variables correctly. -/
def clauseBits : Clause n → Timed (Row n)
  | [] => ⟨⟨false,fun _ => false⟩,n+1⟩
  | l::ls => seq (clauseBits ls) fun r =>
    let v := xorWord (unit l.var) r.bits
    let g := Gate.xor (.neg (.port l.value)) (.port r.bias)
    ⟨⟨g.run,v.val⟩,1+g.work+v.ticks⟩

theorem clause_spec (c : Clause n) :
    (clauseBits c).val = encode (clauseRow c) ∧ (clauseBits c).ticks ≤ (c.length+1)*(10*(n+1)) := by
  induction c with
  | nil => exact ⟨rfl,by simp [clauseBits]⟩
  | cons l c ih =>
    have bnd := word_work (fun i => Gate.xor (.port (unit l.var i)) (.port ((clauseBits c).val.bits i))) 5 (by intros; exact Nat.le_refl _)
    change (xorWord (unit l.var) (clauseBits c).val.bits).ticks ≤ _ at bnd
    constructor
    · simp only [clauseBits,seq,ih.1,encode,clauseRow,parity,coefficient,xorWord,word,Gate.run,FeedbackBasis.tabulate_eq,holds]
      congr 1
      · cases l.value <;> rfl
      · funext i; by_cases eq : i=l.var
        · simp [unit,eq]
        · simp [unit,eq,beq_eq_false_iff_ne.mpr (Ne.symm eq)]
    · simp only [clauseBits,seq,Gate.work,List.length_cons,Nat.succ_mul (c.length+1)]
      have := ih.2; omega

/-- Sequentially test candidate addresses. Copying an address and the control
bit costs at most w+2 bit operations. -/
def find (w : Nat) (f : α → Timed Bool) : List α → Timed (Option α)
  | [] => ⟨none,1⟩
  | a::ls => seq (f a) fun hit =>
    if hit then ⟨some a,w+2⟩ else
      let t := find w f ls
      ⟨t.val,t.ticks+1⟩

theorem find_spec (w : Nat) (f : α → Timed Bool) (l : List α) (k : Nat) (h : ∀ i, (f i).ticks ≤ k) :
    (find w f l).val = l.find? (fun i => (f i).val) ∧
    (find w f l).ticks ≤ 1+l.length*(k+w+2) := by
  induction l with
  | nil => simp [find]
  | cons i l ih =>
    have hi := h i; have := ih.2
    cases eq : (f i).val <;> simp [find,seq,eq,ih.1,Nat.succ_mul l.length]; all_goals omega

def selectPivot (r : Row n) := find (n+1) (fun i => (⟨r.bits i,1⟩ : Timed Bool)) (List.finRange n)

def setup (s : Data n) (c : Clause n) : Timed (Option (Rows n × Point n)) :=
  seq (clauseBits c) fun q => seq (testRow q s.guide) fun yes =>
    if yes then ⟨some (s.rows,s.guide),1⟩ else
      seq (reducing s.rows q) fun v => seq (selectPivot v) fun p =>
        match p with
        | none => ⟨none,1⟩
        | some j =>
          let bs := (j,v)::s.rows
          let t := repairing bs s.guide
          ⟨some (bs,t.val),t.ticks+2*n+4⟩

theorem setup_spec (s : Data n) (c : Clause n) (width : c.length ≤ 3) (rank : s.rows.length ≤ n) :
    (setup s c).val = DenseMachine.setup s c ∧ (setup s c).ticks ≤ 150*(n+1)^2 := by
  let q := (clauseBits c).val
  let v := (reducing s.rows q).val
  have C := clause_spec c
  have R := reducing_spec s.rows q
  have P := find_spec (n+1) (fun i => (⟨v.bits i,1⟩ : Timed Bool)) (List.finRange n) 1 (by simp)
  change (selectPivot v).val = _ ∧ (selectPivot v).ticks ≤ _ at P
  change (selectPivot v).val = (List.finRange n).find? v.bits ∧ _ at P
  rw [List.length_finRange] at P
  have Y : (testRow q s.guide).val = parity c s.guide := by
    have eq := congrArg (fun r : Eqn n => r.value s.guide) (decode_encode (clauseRow c))
    change eval (encode (clauseRow c)) s.guide = parity c s.guide at eq
    simpa [testRow,seq,Gate.run,eval,q,C.1] using eq
  have Ycost : (testRow q s.guide).ticks = 8*n+5 := by simp [testRow,seq,Gate.work]
  have Q : q = encode (clauseRow c) := C.1
  have V : v = reduce s.rows (encode (clauseRow c)) := R.1.trans (congrArg _ Q)
  have cv := C.2; have cr := R.2; have cp := P.2
  have cb := Nat.mul_le_mul_right (10*(n+1)) (show c.length+1 ≤ 4 by omega)
  have rb := Nat.mul_le_mul_right (20*(n+1)) rank
  cases e : parity c s.guide with
  | true =>
    simp [setup,seq,DenseMachine.setup,show (clauseBits c).val = q from rfl,Y,e,Ycost]
    nlinarith
  | false =>
    cases hp : (selectPivot v).val with
    | none =>
      have eq := P.1.symm.trans hp
      simp only [setup,seq,DenseMachine.setup,show (clauseBits c).val=q from rfl,Y,e,Bool.false_eq_true,ite_false,
        show (reducing s.rows q).val=v from rfl,hp,Ycost,←V,eq,Option.map_none,true_and]
      nlinarith
    | some j =>
      have eq := P.1.symm.trans hp
      have H := repairing_spec ((j,v)::s.rows) s.guide
      have bound := H.2
      rw [List.length_cons,Nat.succ_mul s.rows.length] at bound
      simp only [setup,seq,DenseMachine.setup,show (clauseBits c).val=q from rfl,Y,e,Bool.false_eq_true,ite_false,
        show (reducing s.rows q).val=v from rfl,hp,Ycost,←V,eq,Option.map_some,H.1]
      exact ⟨True.intro,by nlinarith⟩

/-- Scan the public order once. A selected index is written as a one-hot word.
The erase pass compares one-hot addresses by testing one intersection; take
copies at most w-bit entries and advances its unary counter. -/
def diffScan (x h : Point n) : List (Fin n) → Timed (List (Fin n))
  | [] => ⟨[],1⟩
  | i::is =>
    let r := diffScan x h is
    let gate := Gate.xor (.port (x i)) (.port (h i))
    ⟨if gate.run then i::r.val else r.val,r.ticks+gate.work+n+2⟩

def erase (i : Fin n) : List (Fin n) → Timed (List (Fin n))
  | [] => ⟨[],1⟩
  | j::ls =>
    let same := read (unit i) j
    if same.val then ⟨ls,same.ticks+1⟩ else
      let r := erase i ls
      ⟨j::r.val,same.ticks+n+2+r.ticks⟩

def take (w : Nat) : Nat → List α → Timed (List α)
  | 0, _ | _+1, [] => ⟨[],1⟩
  | k+1, i::ls =>
    let r := take w k ls
    ⟨i::r.val,r.ticks+2*w+2⟩

theorem diff_spec (x h : Point n) (l : List (Fin n)) :
    (diffScan x h l).val = l.filter (fun i => x i != h i) ∧
    (diffScan x h l).ticks ≤ 1+l.length*(n+6) := by
  induction l with
  | nil => simp [diffScan]
  | cons j l ih =>
    have := ih.2
    cases a : x j <;> cases b : h j <;> simp [diffScan,Gate.run,Gate.work,a,b,ih.1,Nat.succ_mul l.length] <;> omega

theorem erase_spec (i : Fin n) (l : List (Fin n)) :
    (erase i l).val = l.erase i ∧ (erase i l).ticks ≤ 1+l.length*(10*(n+1)) := by
  induction l with
  | nil => simp [erase]
  | cons j l ih =>
    have := ih.2
    have rd : (read (unit i) j).ticks = 8*n+1 := by simp [BitCost.read]
    by_cases e : j=i <;> simp [erase,unit,read_val,rd,e,Ne.symm,ih.1,Nat.succ_mul l.length] at * <;> omega

theorem take_spec (w k : Nat) (l : List α) : (take w k l).val = l.take k ∧ (take w k l).ticks ≤ 1+l.length*(2*w+2) := by
  induction k generalizing l with
  | zero => simp [take]
  | succ k ih =>
    cases l with
    | nil => simp [take]
    | cons a l => have := (ih l).2; simp [take,(ih l).1,Nat.succ_mul l.length]; omega

def moves (B : Nat) (x h : Point n) (i : Fin n) :=
  seq (diffScan x h (List.finRange n)) fun ds => seq (erase i ds) fun tail => take (n+1) B (i::tail)

theorem moves_spec (B : Nat) (x h : Point n) (i : Fin n) : (moves B x h i).val = batch B x h i ∧
    (moves B x h i).ticks ≤ 25*(n+1)^2 := by
  let ds := (diffScan x h (List.finRange n)).val
  have D := diff_spec x h (List.finRange n)
  have E := erase_spec i ds
  have T := take_spec (n+1) B (i::(erase i ds).val)
  have len : ds.length ≤ n := by simpa [ds,D.1] using (List.length_filter_le (fun j => x j != h j) (List.finRange n))
  have le : (erase i ds).val.length ≤ n := E.1 ▸ (List.Sublist.length_le (List.erase_sublist ..)).trans len
  have dl := D.2; rw [List.length_finRange] at dl
  have tl := T.2; rw [List.length_cons] at tl
  have el := E.2
  have ca := Nat.mul_le_mul_right (10*(n+1)) len
  have cb := Nat.mul_le_mul_right (2*(n+1)+2) (Nat.succ_le_succ le)
  exact ⟨T.1.trans (by rw [E.1]; simp [ds,D.1,batch,differences]),by change _+(_+_) ≤ _; nlinarith⟩

end SatWalk.TimedSearch
