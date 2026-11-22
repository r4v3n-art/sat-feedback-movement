import SatWalk.CodeLowerBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

namespace SatWalk.CodeLowerBound
open MeasureTheory FeedbackCube FeedbackBatches Model
open scoped ENNReal

/-- One entry per secret, in the same order as the branching sum. -/
def instances (D : Formula n) : List (Fin n) → List (Formula n)
  | [] => [D]
  | i :: cs => instances (pin D i false) cs ++ instances (pin D i true) cs

theorem allLeaves_iff {P : Formula n → Prop} {cs : List (Fin n)} {D : Formula n} :
    allLeaves P D cs ↔ ∀ F ∈ instances D cs, P F := by
  induction cs generalizing D with
  | nil => simp [allLeaves, instances]
  | cons i cs ih =>
    simp only [allLeaves, instances, List.forall_mem_append, ← ih, Bool.forall_bool]

private theorem leafSum_natCast (f : Formula n → Nat) (D : Formula n) (cs) :
    ((leafSum f D cs : Nat) : ℝ≥0∞) = leafSum (fun G => (f G : ℝ≥0∞)) D cs := by
  induction cs generalizing D with
  | nil => rfl
  | cons i cs ih => simp [leafSum, ih]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

private theorem leaf_integral (f : Formula n → Ω → ℝ≥0∞) (D : Formula n) (cs)
    (hm : ∀ G ∈ instances D cs, AEMeasurable (f G) μ) :
    AEMeasurable (fun ω => leafSum (fun G => f G ω) D cs) μ ∧
    (∫⁻ ω, leafSum (fun G => f G ω) D cs ∂μ) = leafSum (fun G => ∫⁻ ω, f G ω ∂μ) D cs := by
  induction cs generalizing D with
  | nil => exact ⟨hm _ (by simp [instances]), rfl⟩
  | cons i cs ih =>
    have hf := ih (pin D i false) (fun G mem => hm G (List.mem_append_left _ mem))
    have ht := ih (pin D i true) (fun G mem => hm G (List.mem_append_right _ mem))
    exact ⟨hf.1.add ht.1, (lintegral_add_left' hf.1 _).trans (congrArg₂ (· + ·) hf.2 ht.2)⟩

private theorem maximum_leaf (f : Formula n → ℝ≥0∞) (D : Formula n) (cs) :
    ∃ G ∈ instances D cs, leafSum f D cs ≤ f G * 2^cs.length := by
  induction cs generalizing D with
  | nil => exact ⟨D, by simp [instances], by simp [leafSum]⟩
  | cons i cs ih =>
    obtain ⟨L, hl, lb⟩ := ih (pin D i false)
    obtain ⟨R, hr, rb⟩ := ih (pin D i true)
    rcases le_total (f L) (f R) with le | le
    · refine ⟨R, List.mem_append_right _ hr, ?_⟩
      simpa [leafSum, pow_succ, mul_two, mul_add] using add_le_add (lb.trans (mul_le_mul_left le _)) rb
    · refine ⟨L, List.mem_append_left _ hl, ?_⟩
      simpa [leafSum, pow_succ, mul_two, mul_add] using add_le_add lb (rb.trans (mul_le_mul_left le _))

/-- Unnormalized uniform-secret mean, integrating over any independent solver tape. -/
theorem uniform_expected_charge [IsProbabilityMeasure μ] {B d : Nat} (pos : 0 < B)
    (alg : Ω → Solver n σ) (x : Point n) (D : Formula n) (dist : Separated D d)
    (cs : List (Fin n))
    (fin : ∀ G ∈ instances D cs, ∀ᵐ ω ∂μ, ∃ t, Hit B (alg ω) G x t)
    (meas : ∀ G ∈ instances D cs, AEMeasurable (fun ω => (first B (alg ω) G x : ℝ≥0∞)) μ) :
    (cs.length * turns B d : Nat) * (2 : ℝ≥0∞)^cs.length ≤
      2 * leafSum (fun G => ∫⁻ ω, (first B (alg ω) G x : ℝ≥0∞) ∂μ) D cs := by
  let f := fun G ω => (first B (alg ω) G x : ℝ≥0∞)
  let c : ℝ≥0∞ := (cs.length * turns B d : Nat)
  let w : ℝ≥0∞ := 2^cs.length
  have finiteAll (ls : List (Formula n)) (h : ∀ G ∈ ls, ∀ᵐ ω ∂μ, ∃ t, Hit B (alg ω) G x t) :
      ∀ᵐ ω ∂μ, ∀ G ∈ ls, ∃ t, Hit B (alg ω) G x t := by
    induction ls with
    | nil => simp
    | cons a as ih =>
      filter_upwards [h a (by simp), ih (fun G mem => h G (by simp [mem]))] with ω ha tail
      simpa using And.intro ha tail
  have bound : ∀ᵐ ω ∂μ, c * w ≤ 2 * leafSum (fun G => f G ω) D cs := by
    filter_upwards [finiteAll _ fin] with ω ok
    have orig := code_charge pos (alg ω) x D dist cs (allLeaves_iff.mpr ok)
    have cast := Nat.cast_le (α := ℝ≥0∞) |>.mpr orig
    simpa [c, w, f, leafSum_natCast] using cast
  have integ := leaf_integral f D cs meas
  have avg := lintegral_mono_ae bound
  rw [lintegral_const, measure_univ, mul_one, lintegral_const_mul'' _ integ.1, integ.2] at avg
  exact avg

/-- For an arbitrary probability law on a secret-independent solver tape,
some fixed pin string costs at least k ceil(d/B)/2 in expectation. Hitting
times on null sets may be completed arbitrarily. -/
theorem randomized_code_charge [IsProbabilityMeasure μ] {B d : Nat} (pos : 0 < B)
    (alg : Ω → Solver n σ) (x : Point n) (D : Formula n) (dist : Separated D d)
    (cs : List (Fin n))
    (fin : ∀ G ∈ instances D cs, ∀ᵐ ω ∂μ, ∃ t, Hit B (alg ω) G x t)
    (meas : ∀ G ∈ instances D cs, AEMeasurable (fun ω => (first B (alg ω) G x : ℝ≥0∞)) μ) :
    ∃ G ∈ instances D cs, (cs.length * turns B d : Nat) ≤
      2 * (∫⁻ ω, (first B (alg ω) G x : ℝ≥0∞) ∂μ) := by
  let f := fun G ω => (first B (alg ω) G x : ℝ≥0∞)
  let c : ℝ≥0∞ := (cs.length * turns B d : Nat)
  let w : ℝ≥0∞ := 2^cs.length
  have avg := uniform_expected_charge pos alg x D dist cs fin meas
  obtain ⟨G, mem, mx⟩ := maximum_leaf (fun G => ∫⁻ ω, f G ω ∂μ) D cs
  refine ⟨G, mem, ?_⟩
  have scaled := avg.trans (mul_le_mul_right mx 2)
  rw [← mul_assoc] at scaled
  have cancel : w * w⁻¹ = 1 := ENNReal.mul_inv_cancel (by simp [w]) (by simp [w])
  have final := mul_le_mul_left scaled w⁻¹
  change c * w * w⁻¹ ≤ (2 * _) * w * w⁻¹ at final
  simpa only [mul_assoc, cancel, mul_one] using final

end SatWalk.CodeLowerBound
