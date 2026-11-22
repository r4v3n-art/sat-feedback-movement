import SatWalk.UpperBound

namespace SatWalk
open FeedbackCube FeedbackLearner

/-- Projecting away the flip count gives a learner history. This version
records every bit of a batch separately even when a guide revision interrupts. -/
inductive FlipHistory (B : Nat) (F : Model.Formula n) (start : Point n) :
    Nat → Nat → State n → Prop where
  | init : FlipHistory B F start 0 0 (initial start)
  | step {m flips s c t p} (prev : FlipHistory B F start m flips s)
      (report : Model.Honest F s.point (some c)) (response : advance B s c = some (t,p)) :
      FlipHistory B F start (m+1) (flips+p.length) t

theorem total_flips {B : Nat} (pos : 0<B) {F : Model.Formula n} {start w}
    (hw : Model.OddWitness F.clauses w) {m flips s} (hist : FlipHistory B F start m flips s) :
    FeedbackLearner.Run B F.clauses start m s ∧
    flips + gap s.point s.guide ≤ Feedback.allowance s.basis.length := by
  induction hist with
  | init => exact ⟨.start,by simp [initial,Feedback.allowance]⟩
  | @step m flips s c t p prev rep resp ih =>
    have inv := (run_bound pos hw ih.1).1
    obtain ⟨t',p',out,_,_,_,charge⟩ := advance_charges pos inv (hw c rep.1) rep.2
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (out.symm.trans resp))
    exact ⟨.step ih.1 rep.1 rep.2 resp,by have := ih.2; omega⟩

end SatWalk
