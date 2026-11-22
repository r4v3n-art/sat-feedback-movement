import Std

namespace SatWalk.Feedback

/-- The ith independent equation costs at most i units of target movement. -/
def allowance : Nat → Nat
  | 0 => 0
  | r+1 => allowance r + (r+1)

theorem allowance_closed (r : Nat) : 2 * allowance r = r*(r+1) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [allowance, Nat.mul_add, Nat.succ_mul, Nat.mul_succ] at *
    omega

/-- 'gap' is the Hamming distance to the current guide. The trace records one
legal flip per step. Adding an equation of new rank r+1 can move the target
by at most r+1 before that flip; otherwise the gap strictly decreases. -/
inductive Trace : Nat → Nat → Nat → Prop where
  | start : Trace 0 0 0
  | follow {r gap moves next} : Trace r gap moves → next+1 ≤ gap →
      Trace r next (moves+1)
  | learn {r gap moves next} : Trace r gap moves → next+1 ≤ gap+(r+1) →
      Trace (r+1) next (moves+1)

theorem movement_bound {r gap moves : Nat} (h : Trace r gap moves) :
    moves + gap ≤ allowance r := by
  induction h with
  | start => decide
  | follow _ _ ih => omega
  | learn _ _ ih => simp only [allowance]; omega

/-- At each depth a predictor may use the complete earlier secret prefix.
The two subtrees can choose different future predictions. -/
inductive Predictor : Nat → Type where
  | done : Predictor 0
  | guess {k} : Bool → (Bool → Predictor k) → Predictor (k+1)

/-- Sum of all first-examination mistakes over the equally weighted secrets. -/
def totalMistakes : {k : Nat} → Predictor k → Nat
  | _, .done => 0
  | k+1, .guess b child =>
    (if b = false then 0 else 2^k) + totalMistakes (child false) +
    (if b = true then 0 else 2^k) + totalMistakes (child true)

theorem fair_secret_cost {k : Nat} (p : Predictor k) :
    2 * totalMistakes p = k * 2^k := by
  induction p with
  | done => rfl
  | @guess k b child ih =>
    have hl := ih false
    have hr := ih true
    cases b <;> simp only [totalMistakes, Bool.false_eq_true, Bool.true_eq_false,
      ite_false, ite_true, Nat.pow_succ, Nat.succ_mul, ← Nat.mul_assoc] <;> omega

/-- Exact first differences of the reflecting 1/3-up, 2/3-down walk.
If Δ₁=1 and Δⱼ₊₁=3+2Δⱼ, then Δⱼ + 3 = 2^(j+1). -/
theorem walk_difference (delta : Nat → Nat) (base : delta 1 = 1)
    (step : ∀ i, delta (i+2) = 3+2*delta (i+1)) (i : Nat) :
    delta (i+1) + 3 = 2^(i+2) := by
  induction i with
  | zero => simpa using base
  | succ i ih =>
    rw [show i+1+1 = i+2 by omega, step, Nat.pow_succ]
    omega

/-- Sum of the first n-1 differences. Index m = n-1. -/
def walkCost : Nat → Nat
  | 0 => 0
  | m+1 => walkCost m + (2^(m+2)-3)

theorem walk_cost_closed (m : Nat) : walkCost m + 3*m+4 = 2^(m+2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [walkCost]
    change walkCost m + (2^(m+2)-3) + 3*(m+1)+4 = 2^((m+2)+1)
    rw [Nat.pow_succ 2 (m+2)]
    omega

/-- A renaming of variables together with independent complements. Applied to
both the assignment and the literal signs, it preserves truth values. -/
def recode {I : Type} (rename : I → I) (mask x : I → Bool) : I → Bool :=
  fun i => x (rename i) ^^ mask i

/-- If a kernel only sees the assignment and the unordered support of a broken
clause (its signs are thereby determined), equivariance forces equal weights.
The output scale could be any type; only equality matters here. -/
theorem equal_weights {I W : Type} [DecidableEq I]
    (policy : (I → Bool) → (I → Bool) → I → W)
    (equivariant : ∀ (p : I → I) (mask x support : I → Bool),
      (∀ i, p (p i) = i) → ∀ i,
      policy (recode p mask x) (support ∘ p) i = policy x support (p i))
    (x support : I → Bool) {a b : I} (same : support a = support b) :
    policy x support a = policy x support b := by
  classical
  let p := fun i => if i = a then b else if i = b then a else i
  have inv : ∀ i, p (p i) = i := by
    intro i
    by_cases eq : a = b <;> by_cases ha : i = a <;> by_cases hb : i = b <;>
      simp_all [p]
  let mask := fun i => x (p i) ^^ x i
  have restored : recode p mask x = x := by
    funext i
    simp only [recode, mask]
    cases x (p i) <;> cases x i <;> decide
  have unchanged : support ∘ p = support := by
    funext i
    by_cases ha : i = a <;> by_cases hb : i = b <;> simp_all [p, Function.comp_def]
  have h := equivariant p mask x support inv a
  simpa only [restored, unchanged, p, ite_true, eq_self] using h

end SatWalk.Feedback
