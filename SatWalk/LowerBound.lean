import SatWalk.Padding
import SatWalk.RandomizedCharge

namespace SatWalk
open FeedbackCube FeedbackBatches Model CodeLowerBound MeasureTheory
open scoped ENNReal

private def Rich (D : Formula n) (cs : List (Fin n)) :=
  ∀ g : Point n, ∃ x, OddWitness D.clauses x ∧ ∀ i ∈ cs, x i = g i

private theorem rich_children (D : Formula n) (cs : List (Fin n)) (nd : cs.Nodup) (r : Rich D cs) :
    allLeaves (fun G => ∃ x, OddWitness G.clauses x) D cs := by
  induction cs generalizing D with
  | nil =>
    obtain ⟨x,hx,_⟩ := r (fun _ => false)
    exact ⟨x,hx⟩
  | cons i rest ih =>
    intro b
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp nd
    apply ih _ tail
    intro g
    let g' := fun j => if j=i then b else g j
    obtain ⟨x,hx,agree⟩ := r g'
    have hi : x i = b := by simpa [g'] using agree i (.head _)
    refine ⟨x, ?_, fun j mem => ?_⟩
    · change ∀ c ∈ D.clauses ++ [[⟨i,b⟩]], parity c x = true
      rw [List.forall_mem_append]
      exact ⟨hx, by simp [parity, holds, hi]⟩
    · have ne : j ≠ i := fun e => absent (e ▸ mem)
      simpa [g', ne] using agree j (.tail _ mem)

private theorem leaf_size (D : Formula n) (cs : List (Fin n)) :
    allLeaves (fun G => G.clauses.length = D.clauses.length + cs.length ∧
      ∀ z, Occurrences.count G.clauses z = Occurrences.count D.clauses z + cs.count z) D cs := by
  induction cs generalizing D with
  | nil => simp [allLeaves]
  | cons i cs ih =>
    intro b
    apply allLeaves_iff.mpr
    intro G mem
    obtain ⟨len,cnt⟩ := allLeaves_iff.mp (ih (pin D i b)) G mem
    constructor
    · simp [len,pin]; omega
    · intro z
      rw [cnt, List.count_cons, pin, Occurrences.count_append]
      change _ + List.count z [i] + _ = _
      simp [List.count_cons, Nat.add_assoc, Nat.add_comm]

/-- For every size at least five this constructs the public code formula and
a list of independent secret pins. All constants here are absolute. -/
private theorem family (N : Nat) (big : 5 ≤ N) :
    ∃ (D : Formula N) (cs : List (Fin N)) (d : Nat),
      0 < d ∧ N ≤ 10 * cs.length ∧ N ≤ 262440*d ∧ Separated D d ∧
      (∀ G ∈ instances D cs, (∃ x, OddWitness G.clauses x) ∧ G.clauses.length ≤ 6*N ∧
        ∀ i, Occurrences.count G.clauses i ≤ 13) := by
  let m := N/5
  have cover : 2*m+(m+(m+m)) ≤ N := by dsimp [m]; omega
  obtain ⟨a,eq⟩ := Nat.le.dest cover
  have hN : N ≤ 10*m := by dsimp [m]; omega
  have dN : N ≤ 262440*(2*(m/26244)+1) := by dsimp [m]; omega
  obtain ⟨p, sep⟩ := LDPCCode.code_distance m
  let A := LDPCCode.wires p
  obtain ⟨cs, nd, len, free⟩ := InformationSet.free_coordinates A
  let D := ParityGadget.formula A
  let keys := cs.map (ParityGadget.input (m := m))
  have inj : Function.Injective (ParityGadget.input (b := 2*m) (m := m)) := fun _ _ eq => Fin.castAdd_inj.mp eq
  have ndKeys := nd.map inj
  have richness : Rich D keys := by
    intro g
    obtain ⟨x,hx,same⟩ := free (ParityGadget.project g)
    let y := ParityGadget.extend A x
    have eqy : ParityGadget.project y = x := ParityGadget.project_extend A x
    obtain ⟨s,o⟩ := ParityGadget.compilation A y
    refine ⟨y, o.mpr (s.mpr ⟨eqy ▸ hx, by rw [eqy]⟩), ?_⟩
    intro i mem
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp mem
    exact (congrFun eqy j).trans (same j hj)
  -- Transport the finished padded family to the prescribed ambient size.
  have make (n a target : Nat) (D : Formula n) (keys : List (Fin n)) (d : Nat)
      (hk : keys.Nodup) (rich : Rich D keys) (hd : Separated D d)
      (sz : D.clauses.length ≤ 4*n) (oc : ∀ i, Occurrences.count D.clauses i ≤ 12)
      (hn : n+a = target) (hkN : target ≤ 10*keys.length) (dpos : 0 < d) (hdN : target ≤ 262440*d) :
      ∃ (G : Formula target) (is : List (Fin target)) (u : Nat),
        0 < u ∧ target ≤ 10*is.length ∧ target ≤ 262440*u ∧ Separated G u ∧
        (∀ H ∈ instances G is, (∃ x, OddWitness H.clauses x) ∧ H.clauses.length ≤ 6*target ∧
          ∀ i, Occurrences.count H.clauses i ≤ 13) := by
    subst target
    let G := Padding.pad D a
    let is := keys.map (Fin.castAdd a)
    have nd' : is.Nodup := hk.map (fun _ _ eq => Fin.castAdd_inj.mp eq)
    have rk : Rich G is := by
      intro g
      obtain ⟨x, odd, same⟩ := rich (Padding.project g)
      refine ⟨Padding.zeroExtend x a, Padding.odd D a x odd, ?_⟩
      intro i mem
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp mem
      simpa [Padding.zeroExtend, Padding.project] using same j hj
    refine ⟨G, is, d, dpos, by simpa [is] using hkN, hdN, Padding.distance D a d hd, ?_⟩
    intro H mem
    have odd := allLeaves_iff.mp (rich_children G is nd' rk) H mem
    obtain ⟨lh,ch⟩ := allLeaves_iff.mp (leaf_size G is) H mem
    have length := nd'.length_le_of_subset (l₂ := List.finRange (n+a)) (fun j _ => List.mem_finRange j)
    simp only [List.length_finRange] at length
    refine ⟨odd, ?_, fun i => ?_⟩
    · rw [lh, show G.clauses.length = _ from Padding.size D a]; omega
    · have bnd := Padding.occurrence D a oc i
      have cnt : is.count i ≤ 1 := by
        by_cases h : i ∈ is
        · exact (List.count_eq_one_of_mem nd' h).le
        · simp [List.count_eq_zero.mpr h]
      rw [ch]; change Occurrences.count (Padding.pad D a).clauses i + is.count i ≤ _; omega
  apply make _ a N D keys (2*(m/26244)+1) ndKeys richness
  · exact ParityGadget.preserves_distance A _ (fun x y hx hy ne => sep x y hx hy ne)
  · rw [show D.clauses.length = _ from Occurrences.linear_size A]; omega
  · exact Occurrences.bounded_occurrences p
  · exact eq
  · simp [keys]; omega
  · omega
  · exact dN

/-- Randomized minimax lower bound on the shared signed width-three game. The
public order scans a good code, the public padding, then the secret message
pins. Some fixed promised instance costs at least (N+floor(N²/B))/5248820 in
expectation. The instance is chosen independently of the sampled tape. -/
theorem theorem_lower_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N B : Nat) (big : 5 ≤ N) (pos : 0 < B) (x : Point N) (alg : Ω → Solver N σ)
    (terminates : ∀ F : Formula N, (∃ w, OddWitness F.clauses w) →
      ∀ᵐ ω ∂μ, ∃ t, Hit B (alg ω) F x t)
    (meas : ∀ F : Formula N, AEMeasurable (fun ω => (first B (alg ω) F x : ℝ≥0∞)) μ) :
    ∃ F : Formula N, (∃ w, OddWitness F.clauses w) ∧ F.clauses.length ≤ 6*N ∧
      (∀ i, Occurrences.count F.clauses i ≤ 13) ∧
      ((N+N*N/B : Nat) : ℝ≥0∞) ≤ 5248820 * ∫⁻ ω, (first B (alg ω) F x : ℝ≥0∞) ∂μ := by
  obtain ⟨D, cs, d, dpos, kN, dN, sep, props⟩ := family N big
  obtain ⟨F, mem, cost⟩ := randomized_code_charge (μ := μ) pos alg x D sep cs
    (fun F hf => terminates F (props F hf).1) (fun F _ => meas F)
  have dx := covered pos d
  have tpos : 1 ≤ turns B d := by
    cases e : turns B d with
    | zero => rw [e, Nat.zero_mul] at dx; omega
    | succ t => omega
  have lin : N ≤ 10*(cs.length*turns B d) := by
    calc
      _ ≤ 10*cs.length := kN
      _ ≤ 10*(cs.length*turns B d) := by nlinarith [Nat.mul_le_mul_left cs.length tpos]
  have quad : N*N/B ≤ 2624400*(cs.length*turns B d) := by
    apply Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul kN (dN.trans (Nat.mul_le_mul_left _ dx)))) _
    rw [show 10*cs.length*(262440*(turns B d*B)) = (2624400*(cs.length*turns B d))*B by ring, Nat.mul_div_cancel _ pos]
  refine ⟨F,(props F mem).1,(props F mem).2.1,(props F mem).2.2,?_⟩
  calc
    _ ≤ (2624410 : ℝ≥0∞) * ((cs.length*turns B d : Nat) : ℝ≥0∞) := by exact_mod_cast (show N+N*N/B ≤ 2624410*(cs.length*turns B d) by omega)
    _ ≤ 2624410 * (2 * ∫⁻ ω, (first B (alg ω) F x : ℝ≥0∞) ∂μ) := by gcongr
    _ = _ := by rw [← mul_assoc]; norm_num

end SatWalk
