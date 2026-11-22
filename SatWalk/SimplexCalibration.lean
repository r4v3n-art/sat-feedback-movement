import SatWalk.SimplexCode
import SatWalk.RandomizedCharge

noncomputable section
namespace SatWalk.SimplexCalibration
open FeedbackCube FeedbackBatches Model CodeLowerBound SimplexCode

private theorem clear_iff (F : Formula n) (x : Point n) :
    orderedReport F x = none ↔ Solved F.clauses x := by
  simp [orderedReport,List.find?_eq_none,Solved]

def pins (u : Point k) (i : Fin k) : Clause (length k) := [⟨key k i,u i⟩]
def instanceFor (u : Point k) : Formula (length k) where
  clauses := (formula k).clauses ++ (List.finRange k).map (pins u)
  width := by
    intro c h
    rcases List.mem_append.mp h with a|b
    · exact (formula k).width c a
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp b; simp [pins]

private theorem recognized_solved (u : Point k) : Solved (formula k).clauses (word k u) :=
  (solved_iff ..).mpr (by congr 1; funext i; simp)

private theorem code_clear (u : Point k) : orderedReport (formula k) (word k u) = none :=
  (clear_iff ..).mpr (recognized_solved u)

theorem accepted (u : Point k) : orderedReport (instanceFor u) (word k u) = none := by
  apply (clear_iff ..).mpr
  intro c h
  rcases List.mem_append.mp h with a|b
  · exact recognized_solved u c a
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp b; simp [Broken,pins,holds]

private theorem pin_report (u a : Point k) (ne : a ≠ u) :
    ∃ j : Fin k, a j ≠ u j ∧ orderedReport (instanceFor u) (word k a) = some (pins u j) := by
  have ex : ∃ j, a j ≠ u j := Function.ne_iff.mp ne
  have uns (ok : orderedReport (instanceFor u) (word k a)=none) := (clear_iff ..).mp ok
  have no : orderedReport (instanceFor u) (word k a) ≠ none := by
    intro ok
    obtain ⟨j,hj⟩ := ex
    apply uns ok (pins u j) (List.mem_append_right _ (List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩))
    simp [pins,Broken,holds,hj]
  cases e : orderedReport (instanceFor u) (word k a) with
  | none => contradiction
  | some c =>
    have rep := ordered_honest (instanceFor u) (word k a)
    rw [e] at rep
    obtain ⟨mem,broken⟩ := rep
    rcases List.mem_append.mp mem with pub|pin
    · exact False.elim (recognized_solved a c pub broken)
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp pin
      exact ⟨j,by simpa [pins,Broken,holds] using broken,rfl⟩

/-- The state is the current target word. On-code the public checker has
accepted and the report is a message pin. Off-code keep the target and use
the reported clause to make a forced legal step toward it. -/
def destination (s x : Point (length k)) (c : Clause (length k)) :=
  if orderedReport (formula k) x = none then
    match c with
    | [] => s
    | l::_ => word k (fun i => if key k i = l.var then l.value else x (key k i))
  else s

def solver (k B : Nat) : Solver (length k) (Point (length k)) where
  initial := id
  respond s x c :=
    let h := destination s x c
    (c.find? (fun l => holds l h)).map (fun l => (h,batch B x h l.var))

/-- Every step uses the actual deterministic reporter and the public solver.
Its endpoint is the result of the reported physical flips. -/
inductive Path (B : Nat) (F : Formula n) (A : Solver n σ) : Config n σ → Nat → Config n σ → Prop where
  | nil (s) : Path B F A s 0 s
  | cons {s c t p m z} (rep : orderedReport F s.2=some c)
      (resp : A.respond s.1 s.2 c=some (t,p)) (leg : LegalMove B c p)
      (tail : Path B F A (t,p.foldl toggle s.2) m z) : Path B F A s (m+1) z

private theorem append {F : Formula n} {A : Solver n σ} {x y z a b}
    (p : Path B F A x a y) (q : Path B F A y b z) : Path B F A x (a+b) z := by
  induction p with
  | nil => simpa using q
  | @cons x c s p a y r o l tail ih => simpa [Nat.succ_add] using Path.cons r o l (ih q)

private theorem motion {u : Point k} {s x h : Point (length k)} {c} {B}
    (pos : 0<B) (r : orderedReport (instanceFor u) x=some c) (target : destination s x c = h)
    (good : ¬Broken c h) :
    ∃ y, Path B (instanceFor u) (solver k B) (s,x) 1 (h,y) ∧
      turns B (gap y h)+1 ≤ turns B (gap x h) := by
  have honest := ordered_honest (instanceFor u) x
  rw [r] at honest
  have found : ∃ l, c.find? (fun l => holds l h) = some l := by
    cases e : c.find? (fun l => holds l h) with
    | some l => exact ⟨_,rfl⟩
    | none =>
      apply False.elim; apply good
      simpa [List.find?_eq_none,Broken] using e
  obtain ⟨l,hl⟩ := found
  have mem := List.mem_of_find?_eq_some hl
  have no := honest.2 l mem
  have yes := List.find?_some (p := fun l => holds l h) hl
  have ne : x l.var ≠ h l.var := by intro eq; simp only [holds,eq] at no yes; rw [yes] at no; cases no
  obtain ⟨nd,inc,len,dist⟩ := batch_spec pos ne
  let p := batch B x h l.var
  have leg : LegalMove B c p := ⟨nd,len.trans_le (Nat.min_le_left ..),l,mem,inc⟩
  refine ⟨p.foldl toggle x,.cons r (by simp [solver,target,hl,p]) leg (.nil _),?_⟩
  exact descend pos (List.length_pos_of_mem (mem_differences.mpr ne)) dist

/-- Below one code distance from a target codeword, all intermediate
non-target reports come from the public code. -/
private theorem coast (u a : Point k) {B} (pos : 0<B) (x : Point (length k))
    (small : gap x (word k a) < 2^(k-1)) :
    ∃ m ≤ turns B (gap x (word k a)),
      Path B (instanceFor u) (solver k B) (word k a,x) m (word k a,word k a) := by
  generalize z : turns B (gap x (word k a)) = t
  induction t using Nat.strong_induction_on generalizing x with
  | ind t ih =>
    by_cases eq : x=word k a
    · subst x; exact ⟨0,Nat.zero_le _,.nil _⟩
    have off : orderedReport (formula k) x ≠ none := by
      intro yes
      have X := (solved_iff ..).mp ((clear_iff ..).mp yes)
      have ne : x ∘ key k ≠ a := fun h => eq (X.trans (congrArg _ h))
      have d := distance ne
      rw [←X] at d; omega
    cases e : orderedReport (formula k) x with
    | none => contradiction
    | some c =>
      have r := agree_report (D := formula k) (F := instanceFor u) ⟨_,rfl⟩ e
      have honest := ordered_honest (formula k) x; rw [e] at honest
      obtain ⟨y,step,less⟩ := motion (s := word k a) pos r (by simp [destination,off]) (recognized_solved a c honest.1)
      have smaller : gap y (word k a) < gap x (word k a) := by
        by_contra! le
        have monotone : turns B (gap x (word k a)) ≤ turns B (gap y (word k a)) :=
          Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right le B) 1)
        omega
      obtain ⟨m,cap,tail⟩ := ih _ (by omega) y (lt_trans smaller small) rfl
      exact ⟨1+m,by omega,append step tail⟩

/-- Starting at a public codeword, correcting a first reported wrong message
bit costs at most one code distance in batches. No other message bit changes. -/
theorem correction (u a : Point k) {B} (pos : 0<B) (ne : a ≠ u) :
    ∃ j : Fin k, a j ≠ u j ∧ ∃ m ≤ turns B (2^(k-1)),
      Path B (instanceFor u) (solver k B) (word k a,word k a) m (word k (toggle a j),word k (toggle a j)) := by
  obtain ⟨j,miss,r⟩ := pin_report u a ne
  let b := toggle a j
  have flip : u j = !(a j) := by cases v : a j <;> cases w : u j <;> simp_all
  have dest : destination (word k a) (word k a) (pins u j) = word k b := by
    simp only [destination,code_clear,ite_true,pins]
    congr 1; funext i
    by_cases eq : i=j
    · subst i; simp [b,toggle,flip]
    · simp [b,toggle,eq,(key_injective k).ne eq]
  have ok : ¬ Broken (pins u j) (word k b) := by simp [pins,Broken,holds,b,toggle,flip]
  have neq : a ≠ b := by intro h; have e := congrFun h j; simp [b,toggle] at e
  have d := distance neq
  obtain ⟨y,step,less⟩ := motion pos r dest ok
  rw [d] at less
  have small : gap y (word k b) < 2^(k-1) := by
    by_contra! le
    have mono : turns B (2^(k-1)) ≤ turns B (gap y (word k b)) :=
      Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right le B) 1)
    omega
  obtain ⟨m,cap,tail⟩ := coast u b pos y small
  exact ⟨j,miss,1+m,by omega,append step tail⟩

private theorem distance_le {F : Formula n} {A : Solver n σ} {x y m} (p : Path B F A x m y) :
    gap x.2 y.2 ≤ m*B := by
  induction p with
  | nil => simp
  | @cons s c t p m z rep resp legal tail ih =>
    let y := p.foldl toggle s.2
    have tri := hammingDist_triangle s.2 y z.2
    simp only [LDPCCode.hamming_eq_gap] at tri
    have one := (gap_le_path s.2 p).trans legal.withinBudget
    change gap y z.2 ≤ _ at ih
    change gap s.2 y ≤ _ at one
    rw [Nat.succ_mul]; omega

private theorem decrement {u a : Point k} {j} (miss : a j ≠ u j) :
    gap (toggle a j) u + 1 = gap a u := by
  simp only [←LDPCCode.hamming_eq_gap,hammingDist]
  let S := Finset.univ.filter (fun i => a i ≠ u i)
  have mem : j ∈ S := by simp [S,miss]
  have eq : Finset.univ.filter (fun i => toggle a j i ≠ u i) = S.erase j := by
    ext i; by_cases h : i=j
    · subst i; cases p : a j <;> cases q : u j <;> simp_all [toggle]
    · constructor
      · intro m; exact Finset.mem_erase.mpr ⟨h,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [toggle,h] using (Finset.mem_filter.mp m).2⟩⟩
      · intro m; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [toggle,h] using (Finset.mem_filter.mp (Finset.mem_erase.mp m).2).2⟩
  rw [eq]; exact Finset.card_erase_add_one mem

theorem exact_path (u a : Point k) {B} (pos : 0<B) :
    Path B (instanceFor u) (solver k B) (word k a,word k a)
      (gap a u * turns B (2^(k-1))) (word k u,word k u) := by
  generalize E : gap a u = z
  induction z using Nat.strong_induction_on generalizing a with
  | ind z ih =>
    by_cases eq : a=u
    · subst a; simp at E; subst z; simpa using Path.nil (B := B) (F := instanceFor u) (A := solver k B) (word k u,word k u)
    obtain ⟨j,miss,m,cap,p⟩ := correction u a pos eq
    have ne : a ≠ toggle a j := by intro h; have e := congrFun h j; simp [toggle] at e
    have g := distance_le p
    change gap (word k a) (word k (toggle a j)) ≤ _ at g
    rw [distance ne] at g
    have lower := (turns_le pos _ _).mpr g
    have D := decrement miss
    have tail := ih _ (by omega) (toggle a j) rfl
    have len : m + gap (toggle a j) u * turns B (2^(k-1)) = z * turns B (2^(k-1)) := by
      rw [←E,←D,Nat.succ_mul]; omega
    exact len ▸ append p tail

private theorem follow {F : Formula n} {A : Solver n σ} {s z m} (p : Path B F A s m z)
    (x : Point n) (t : Nat) (atStart : trajectory B A F x t = s) :
    trajectory B A F x (t+m) = z ∧ ∀ i<m, ¬Hit B A F x (t+i) := by
  induction p generalizing t with
  | nil => exact ⟨by simpa using atStart,by simp⟩
  | @cons s c u q m z rep resp legal tail ih =>
    have next : trajectory B A F x (t+1) = (u,q.foldl toggle s.2) := by
      simp [trajectory,atStart,rep,step,resp,legal.withinBudget]
    obtain ⟨arrive,prior⟩ := ih (t+1) next
    refine ⟨by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using arrive,?_⟩
    intro i hi
    cases i with
    | zero => simp [Hit,atStart,rep]
    | succ i => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using prior i (by omega)

theorem exact_moves (u a : Point k) {B} (pos : 0<B) :
    first B (solver k B) (instanceFor u) (word k a) = gap a u * turns B (2^(k-1)) := by
  have H := follow (exact_path u a pos) (word k a) 0 rfl
  simp only [Nat.zero_add] at H
  let m := gap a u * turns B (2^(k-1))
  have hit : Hit B (solver k B) (instanceFor u) (word k a) m := by
    unfold Hit; rw [show trajectory _ _ _ _ m = _ from H.1]; exact accepted u
  have S := first_spec (Exists.intro m hit)
  exact le_antisymm (S.2 m hit) (Nat.le_of_not_gt (fun lt => H.2 _ lt S.1))

/-- Exact mean for k independent fair message bits, without rounding the
half-integer or restricting the batch size to divisors of the distance. -/
theorem exact_average (a : Point k) {B} (pos : 0<B) :
    2*(∑ u : Point k, first B (solver k B) (instanceFor u) (word k a)) =
      2^k*k*turns B (2^(k-1)) := by
  let flip : Point k ≃ Point k := ⟨fun u i => !(u i),fun u i => !(u i),
    fun u => by funext i; simp,fun u => by funext i; simp⟩
  have pair (u : Point k) : gap a u + gap a (flip u) = k := by
    simp only [←LDPCCode.hamming_eq_gap,hammingDist]
    let S := Finset.univ.filter (fun i => a i ≠ u i)
    have eq : Finset.univ.filter (fun i => a i ≠ flip u i) = Sᶜ := by
      ext i; cases h : a i <;> cases g : u i <;> simp [flip,S,h,g]
    rw [eq, Finset.card_compl]
    simp only [Fintype.card_fin]; change S.card+(k-S.card)=k
    have c : S.card ≤ k := by simpa using S.card_le_univ
    omega
  have count := Finset.sum_congr (s₁ := (Finset.univ : Finset (Point k))) rfl (fun u _ => pair u)
  rw [Finset.sum_add_distrib,flip.sum_comp (gap a), ←two_mul] at count
  simp [Point,Fintype.card_pi] at count
  simp only [exact_moves _ _ pos,←Finset.sum_mul,←Nat.mul_assoc,count]

/-- Equally weighted leaves of the ordered pin tree are the equally weighted
binary messages, including when two runs happen to have the same length. -/
private def appendPins (F : Formula n) (is : Fin k → Fin n) (u : Point k) : Formula n where
  clauses := F.clauses ++ List.ofFn (fun j => ([⟨is j,u j⟩] : Clause n))
  width := by intro c h; rcases List.mem_append.mp h with a|b
              · exact F.width c a
              · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp b; simp

private theorem append_cons (F : Formula n) (is : Fin (k+1) → Fin n) (b : Bool) (u : Point k) :
    appendPins F is (Fin.cons b u) = appendPins (pin F (is 0) b) (fun j => is j.succ) u := by
  unfold appendPins pin
  congr 1
  simp [List.ofFn_succ]

private def messages (k : Nat) : Bool × Point k ≃ Point (k+1) where
  toFun p := Fin.cons p.1 p.2
  invFun u := (u 0,Fin.tail u)
  left_inv := by rintro ⟨b,u⟩; simp [Fin.tail]
  right_inv := Fin.cons_self_tail

private theorem enumerate (f : Formula n → Nat) (F : Formula n) (is : Fin k → Fin n) :
    leafSum f F (List.ofFn is) = ∑ u : Point k, f (appendPins F is u) := by
  induction k generalizing F with
  | zero =>
    have eq (u : Point 0) : appendPins F is u = F := by cases F; simp [appendPins]
    simp [leafSum,eq,Point,Fintype.card_pi]
  | succ k ih =>
    rw [←(messages k).sum_comp (fun u => f (appendPins F is u)),Fintype.sum_prod_type,Fintype.sum_bool,
      List.ofFn_succ,leafSum,ih,ih]
    simp [messages,append_cons,Nat.add_comm]

private theorem leaves_all (F : Formula n) (is : Fin k → Fin n) (P : Formula n → Prop)
    (c : ∀ u, P (appendPins F is u)) : allLeaves P F (List.ofFn is) := by
  induction k generalizing F with
  | zero => simpa [appendPins,allLeaves] using c (fun _ => false)
  | succ k ih =>
    rw [List.ofFn_succ,allLeaves]
    intro b; apply ih
    intro u; simpa only [append_cons] using c (Fin.cons b u)

private theorem instance_eq (u : Point k) : appendPins (formula k) (key k) u = instanceFor u := by
  congr 1
  simp [appendPins,instanceFor,pins,List.finRange,List.map_ofFn]; rfl

theorem optimal (a : Point k) {B} (pos : 0<B) (A : Solver (length k) σ)
    (fin : ∀ u, ∃ t, Hit B A (instanceFor u) (word k a) t) :
    (∑ u : Point k, first B (solver k B) (instanceFor u) (word k a)) ≤
      ∑ u : Point k, first B A (instanceFor u) (word k a) := by
  have sep : Separated (formula k) (2^(k-1)) := by
    intro x y cx cy ne
    have X := (solved_iff ..).mp ((clear_iff ..).mp cx)
    have Y := (solved_iff ..).mp ((clear_iff ..).mp cy)
    have diff : x ∘ key k ≠ y ∘ key k := fun e => ne (X.trans ((congrArg _ e).trans Y.symm))
    exact ((X ▸ Y ▸ distance diff) : gap x y = 2^(k-1)).ge
  have ch := code_charge pos A (word k a) (formula k) sep (List.ofFn (key k))
    (leaves_all _ _ _ (fun u => by simpa [instance_eq] using fin u))
  simp only [List.length_ofFn,enumerate,instance_eq] at ch
  have exactCost := exact_average a pos
  rw [show 2^k*k*turns B (2^(k-1)) = k*turns B (2^(k-1))*2^k by ring] at exactCost
  omega

end SatWalk.SimplexCalibration
