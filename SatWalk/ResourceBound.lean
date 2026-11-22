import SatWalk.TimedSearch

namespace SatWalk.ResourceBound
open FeedbackCube DenseMachine BitCost

def flipAll (x : Point n) : List (Fin n) → Timed (Point n)
  | [] => ⟨x,1⟩
  | p::ls => seq (xorWord x (unit p)) fun y => flipAll y ls

theorem flip_spec (x : Point n) (l : List (Fin n)) :
    (flipAll x l).val = l.foldl toggle x ∧ (flipAll x l).ticks ≤ 1+l.length*(5*n) := by
  induction l generalizing x with
  | nil => simp [flipAll]
  | cons j l ih =>
    have V : (xorWord x (unit j)).val = toggle x j := by
      funext i; by_cases eq : i=j <;> simp [xorWord,word,Gate.run,unit,toggle,eq]
    have W := word_work (fun i => Gate.xor (.port (x i)) (.port (unit j i))) 5 (by intros; exact Nat.le_refl _)
    change (xorWord x (unit j)).ticks ≤ _ at W
    obtain ⟨val,cost⟩ := ih (toggle x j)
    simp [flipAll,seq,V,val,Nat.succ_mul l.length]; omega

def testLit (x : Point n) (l : Literal n) : Timed Bool :=
  seq (BitCost.read x l.var) fun v =>
    let g := Gate.neg (.xor (.port v) (.port l.value))
    ⟨g.run,g.work⟩

theorem lit_spec (x : Point n) (l : Literal n) :
    (testLit x l).val = holds l x ∧ (testLit x l).ticks ≤ 10*(n+1) := by
  have rd : (BitCost.read x l.var).ticks = 8*n+1 := by simp [BitCost.read]
  constructor
  · simp [testLit,seq,Gate.run,holds]; cases x l.var <;> cases l.value <;> rfl
  · simp [testLit,seq,Gate.work,rd]; omega

def finish (B : Nat) (s : Data n) (c : Clause n) (rs : Rows n) (h : Point n) : Timed (Option (Data n × List (Fin n))) :=
  seq (TimedSearch.find (n+1) (testLit h) c) fun found =>
    match found with
    | none => ⟨none,1⟩
    | some l =>
      seq (TimedSearch.moves B s.point h l.var) fun p =>
      let t := flipAll s.point p
      ⟨some (⟨t.val,h,rs⟩,p),t.ticks+1⟩

def update (B : Nat) (s : Data n) (c : Clause n) :=
  seq (TimedSearch.setup s c) fun prep =>
    match prep with
    | none => ⟨none,1⟩
    | some (rs,h) => finish B s c rs h

private theorem finish_spec (B : Nat) (s : Data n) (c : Clause n) (rs : Rows n) (h : Point n)
    (width : c.length ≤ 3) (budget : B ≤ n) :
    (finish B s c rs h).val = (c.find? (fun l => holds l h)).map (fun l =>
      let p := batch B s.point h l.var
      ((⟨p.foldl toggle s.point,h,rs⟩ : Data n),p)) ∧
    (finish B s c rs h).ticks ≤ 80*(n+1)^2 := by
  let f := TimedSearch.find (n+1) (testLit h) c
  have F := TimedSearch.find_spec (n+1) (testLit h) c (10*(n+1)) (fun l => (lit_spec h l).2)
  have fv : f.val = c.find? (fun l => holds l h) := by simpa [(lit_spec ..).1] using F.1
  have fc := F.2
  have cut := Nat.mul_le_mul_right (10*(n+1)+(n+1)+2) width
  cases e : f.val with
  | none =>
    simp only [finish,seq,show TimedSearch.find (n+1) (testLit h) c=f from rfl,e,←fv,Option.map_none,true_and]
    nlinarith
  | some l =>
    let p := (TimedSearch.moves B s.point h l.var).val
    have M := TimedSearch.moves_spec B s.point h l.var
    have P := flip_spec s.point p
    have len : p.length ≤ n := by
      change (TimedSearch.moves B s.point h l.var).val.length ≤ n
      rw [M.1,batch,List.length_take]; omega
    have bound := Nat.mul_le_mul_right (5*n) len
    have pc := P.2; have mc := M.2
    simp only [finish,seq,show TimedSearch.find (n+1) (testLit h) c=f from rfl,e,←fv,
      show (TimedSearch.moves B s.point h l.var).val=p from rfl,Option.map_some,P.1,←M.1]
    exact ⟨True.intro,by nlinarith⟩

theorem update_spec (B : Nat) (s : Data n) (c : Clause n) (width : c.length ≤ 3) (budget : B ≤ n)
    (rank : s.rows.length ≤ n) :
    (update B s c).val = DenseMachine.update B s c ∧ (update B s c).ticks ≤ 240*(n+1)^2 := by
  have H := TimedSearch.setup_spec s c width rank
  have hc := H.2
  cases a : (TimedSearch.setup s c).val with
  | none => simp [update,seq,DenseMachine.update,←H.1,a]; nlinarith
  | some v =>
    rcases v with ⟨rs,h⟩
    have K := finish_spec B s c rs h width budget
    have kc := K.2
    simp only [update,seq,DenseMachine.update,←H.1,a,K.1]
    constructor
    · cases f : c.find? (fun l => holds l h) <;> simp [bind, Option.bind,pure,FeedbackBasis.tabulate_eq,f]
    · nlinarith

/-- Space is in bits. Each retained row has an intercept, n coefficients, a
one-hot pivot and a presence flag. The two point words are stored explicitly. -/
def stored (s : Data n) := 2*n+2 + s.rows.length*(2*n+2)

/-- The maximum live-bit bound even permits every temporary bit written during
a transition to coexist until that transition returns. The old state and the
incoming signed one-hot report are included. -/
def workspace (s : Data n) (c : Clause n) (ticks : Nat) :=
  stored s + (n+2)*c.length + ticks + (n+1)

inductive History (B : Nat) (F : Model.Formula n) (start : Point n) :
    Nat → Data n → Nat → Nat → Prop where
  | init : History B F start 0 (DenseMachine.init start) (2*n+2) (2*n+2)
  | step {m s clocks peak c t p} (prev : History B F start m s clocks peak)
      (rep : Model.Honest F s.point (some c)) (out : (update B s c).val = some (t,p))
      (legal : Model.LegalMove B c p) :
      History B F start (m+1) t (clocks+(update B s c).ticks)
        (max peak (workspace s c (update B s c).ticks))

private theorem denseResponse (B : Nat) (s : Data n) (c : Clause n) {t p}
    (hc : c.length ≤ 3) (budget : B ≤ n) (rank : s.rows.length ≤ n)
    (out : (update B s c).val = some (t,p)) :
    (paritySolver n B).respond (view s) s.point c = some (view t,p) ∧ t.point = p.foldl toggle s.point := by
  have val := (update_spec B s c hc budget rank).1.symm.trans out
  have eq := DenseMachine.update_eq B s c
  rw [val] at eq
  refine ⟨eq.symm,?_⟩
  unfold DenseMachine.update at val
  cases a : DenseMachine.setup s c with
  | none => simp [a] at val
  | some v =>
    rcases v with ⟨rs,h⟩
    cases b : c.find? (fun l => holds l h) with
    | none => simp [a,b] at val
    | some l =>
      simp [a,b] at val
      obtain ⟨rfl,rfl⟩ := val
      simp

/-- Simultaneous simulation and resource accounting for all honest adaptive
histories of the dense bit machine. Costs include initialization. -/
theorem history_bound {B : Nat} (pos : 0<B) (budget : B ≤ n) {F : Model.Formula n} {w start}
    (promise : Model.OddWitness F.clauses w) {m s clocks peak} (hist : History B F start m s clocks peak) :
    Model.Run B F (paritySolver n B) start m (view s) s.point ∧
      clocks ≤ 2*n+2+m*(240*(n+1)^2) ∧ peak ≤ 260*(n+1)^2 := by
  induction hist with
  | init => exact ⟨.init,by simp,by nlinarith⟩
  | @step m s clock peak c t p prev rep out legal ih =>
    have rank : s.rows.length ≤ n := by simpa [view,basis] using (theorem_upper_bound pos promise ih.1).1
    have width := F.width c rep.1
    obtain ⟨resp,point⟩ := denseResponse B s c width budget rank out
    have cost := (update_spec B s c width budget rank).2
    have mem := Nat.mul_le_mul_right (2*n+2) rank
    have inp := Nat.mul_le_mul_left (n+2) width
    refine ⟨point ▸ ih.1.step rep resp legal,?_,max_le ih.2.2 ?_⟩
    · rw [Nat.succ_mul m]; have := ih.2.1; omega
    · unfold workspace stored; nlinarith

/-- Every reachable rejection of the bit machine produces a legal move. -/
theorem progress {B : Nat} (pos : 0<B) (budget : B ≤ n) {F : Model.Formula n} {w start}
    (promise : Model.OddWitness F.clauses w) {m s clocks peak} (hist : History B F start m s clocks peak)
    {c : Clause n} (rep : Model.Honest F s.point (some c)) :
    ∃ t p, (update B s c).val = some (t,p) ∧ Model.LegalMove B c p := by
  have sim := (history_bound pos budget promise hist).1
  have rank : s.rows.length ≤ n := by simpa [view,basis] using (theorem_upper_bound pos promise sim).1
  obtain ⟨u,p,U,leg⟩ := paritySolver_progress pos promise sim rep
  have eq := DenseMachine.update_eq B s c
  rw [← (update_spec B s c (F.width c rep.1) budget rank).1] at eq
  change FeedbackLearner.advance B (view s) c = _ at U
  rw [U] at eq
  cases a : (update B s c).val with
  | none => simp [a] at eq
  | some v =>
    rcases v with ⟨t,q⟩
    obtain ⟨_,rfl⟩ : view t = u ∧ q = p := by simpa [a] using eq
    exact ⟨t,_,rfl,leg⟩

end SatWalk.ResourceBound

namespace SatWalk

/-- Quartic bit work and quadratic workspace for the concrete dense
implementation, with the same rank-sensitive pathwise movement theorem.
The constant words cover the terminal reporter flag and returned point. -/
theorem theorem_bit_complexity {B n : Nat} (pos : 0<B) (budget : B ≤ n) {F : Model.Formula n} {w start}
    (promise : Model.OddWitness F.clauses w) {m s clocks peak} (hist : ResourceBound.History B F start m s clocks peak) :
    clocks+(n+1) ≤ 500*(n+1)^4 ∧ peak+(n+1) ≤ 270*(n+1)^2 ∧
    m ≤ s.rows.length + s.rows.length*(s.rows.length+1)/(2*B) := by
  obtain ⟨sim,time,space⟩ := ResourceBound.history_bound pos budget promise hist
  obtain ⟨rank,_,moves,_⟩ := theorem_upper_bound pos promise sim
  simp only [DenseMachine.view,DenseMachine.basis,List.length_map] at rank moves
  have cap := Nat.div_le_self (s.rows.length*(s.rows.length+1)) (2*B)
  have prod := Nat.mul_le_mul rank (Nat.succ_le_succ rank)
  have steps : m ≤ (n+1)^2 := by nlinarith
  have total := Nat.mul_le_mul_right (240*(n+1)^2) steps
  exact ⟨by nlinarith,by nlinarith,moves⟩

end SatWalk
