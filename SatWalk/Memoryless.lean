import SatWalk.PlantedWalk
import SatWalk.Feedback

noncomputable section
namespace SatWalk.Memoryless
open Model FeedbackCube UniformWalk PlantedWalk
open scoped ENNReal

def support (is : List (Fin n)) : Point n := fun i => decide (i ∈ is)

/-- On a broken clause its unordered support and the current assignment determine
every sign. The kernel assigns a probability to each legal (in-support) flip.
Renamings and independent coordinate complements act simultaneously on the input. -/
structure Policy (n : Nat) where
  weight : Point n → Point n → Fin n → ℝ
  nonneg : ∀ x s i, s i = true → 0 ≤ weight x s i
  unitMass : ∀ x (is : List (Fin n)), is.Nodup → is ≠ [] →
    (is.map (weight x (support is))).sum = 1
  equivariant : ∀ (p : Equiv.Perm (Fin n)) mask x s i,
    weight (Feedback.recode p mask x) (s ∘ p) i = weight x s (p i)

/-- The usual uniformly random legal flip is itself a member of the class. -/
def uniform (n : Nat) : Policy n where
  weight _ s _ := 1 / ((Finset.univ.filter fun j => s j = true).card : ℝ)
  nonneg := by intros; positivity
  unitMass := by
    intro x is nd ne
    have same : Finset.univ.filter (fun j => support is j = true) = is.toFinset := by ext; simp [support]
    rw [same,List.toFinset_card_of_nodup nd,sum_const is _ (fun _ _ => rfl)]
    have pos : (is.length : ℝ) ≠ 0 := by exact_mod_cast (List.length_pos_iff.mpr ne).ne'
    field_simp
  equivariant := by
    intro p mask x s i
    have eq : (Finset.univ.filter (fun j => (s ∘ p) j = true)).map p.toEmbedding = Finset.univ.filter (fun j => s j = true) := by
      ext j; simp
    rw [←eq,Finset.card_map]

theorem equal_on (P : Policy n) (x : Point n) (is : List (Fin n))
    (ha : a ∈ is) (hb : b ∈ is) :
    P.weight x (support is) a = P.weight x (support is) b := by
  apply Feedback.equal_weights P.weight _ x (support is) (by simp [support,ha,hb])
  intro p mask y s inv i
  exact P.equivariant ⟨p,p,inv,inv⟩ mask y s i

def clauseStep (P : Policy n) (x : Point n) (c : Clause n) (v : Point n → ℝ) : ℝ :=
  let is := c.map Literal.var
  (is.map (fun i => P.weight x (support is) i * v (toggle x i))).sum

theorem simple_step (P : Policy n) (x : Point n) (c : Clause n) (v : Point n → ℝ)
    (nd : (c.map Literal.var).Nodup) (ne : c ≠ []) :
    clauseStep P x c v = avg c (v x) (fun l => v (toggle x l.var)) := by
  let is := c.map Literal.var
  have nonempty : is ≠ [] := by simpa [is] using ne
  obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil is nonempty
  let w := P.weight x (support is) i
  have eq (j) (hj : j ∈ is) : P.weight x (support is) j = w := equal_on P x is hj hi
  have mass := P.unitMass x is nd nonempty
  rw [sum_const is w eq] at mass
  have sum (ls : List (Fin n)) (h : ∀ j ∈ ls, j ∈ is) :
      (ls.map (fun j => P.weight x (support is) j * v (toggle x j))).sum =
      w*(ls.map (fun j => v (toggle x j))).sum := by
    induction ls with
    | nil => simp
    | cons j ls ih => simp [eq _ (h _ (.head _)), ih (fun k hk => h k (.tail _ hk)), mul_add]
  change (is.map _).sum = _
  rw [sum is (by simp),avg,ite_eq_right (fun h => (ne h).elim)]
  have len : (c.length : ℝ) ≠ 0 := by exact_mod_cast (List.length_pos_iff.mpr ne).ne'
  simpa [is, List.map_map, Function.comp_def] using
    (show w * (is.map (fun j => v (toggle x j))).sum =
      (is.map (fun j => v (toggle x j))).sum / c.length from
      (eq_div_iff len).mpr (by
        have m : (c.length : ℝ)*w=1 := by simpa [is] using mass
        calc _ = ((c.length:ℝ)*w)*(is.map (fun j => v (toggle x j))).sum := by ring
             _ = _ := by rw [m,one_mul]))

def cost (P : Policy n) (F : Formula n) : Nat → Point n → ℝ
  | 0, _ => 0
  | t+1, x => if violations F x = [] then 0 else
      1 + avg (violations F x) (cost P F t x) (fun c => clauseStep P x c (cost P F t))

def mean (P : Policy n) (F : Formula n) (x : Point n) : ℝ≥0∞ :=
  ⨆ t, ENNReal.ofReal (cost P F t x)
def startMean (P : Policy n) (F : Formula n) : ℝ≥0∞ := (∑ x, mean P F x)/2^n

def Simple (F : Formula n) := ∀ c ∈ F.clauses, (c.map Literal.var).Nodup ∧ c ≠ []
theorem planted_simple (ts : List (Triple n)) : Simple (formula ts) := by
  intro c hc
  rcases List.mem_append.mp hc with a|b
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp a; simp [pin]
  · obtain ⟨t,_,rfl⟩ := List.mem_map.mp b
    simp [clause,List.map_map,Function.comp_def,t.disjoint, Finset.nodup_toList]

theorem cost_eq (P : Policy n) (F : Formula n) (ok : Simple F) (t : Nat) :
    cost P F t = UniformWalk.cost F t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x; simp only [cost,UniformWalk.cost,ih]; split
    · rfl
    · congr 1
      unfold advance avg
      split
      · rfl
      · congr 2
        apply List.map_congr_left
        intro c h
        exact simple_step P x c _ (ok c (mem_violations.mp h).1).1 (ok c (mem_violations.mp h).1).2

theorem mean_eq (P : Policy n) (F : Formula n) (ok : Simple F) (x : Point n) :
    mean P F x = UniformWalk.mean F x := by simp [mean,UniformWalk.mean,cost_eq P F ok]

theorem start_eq (P : Policy n) (F : Formula n) (ok : Simple F) :
    startMean P F = PlantedWalk.startMean F := by simp [startMean,PlantedWalk.startMean,mean_eq P F ok]

end SatWalk.Memoryless
