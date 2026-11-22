import SatWalk.Memoryless
import SatWalk.SparseBarrier
import SatWalk.SparseFamily

noncomputable section
namespace SatWalk.SparseSeparation
open FeedbackCube Model UniformWalk PlantedWalk SparseGraph
open scoped ENNReal

/-- Reserve two levels per block of A to accommodate the two boundary bands. -/
private theorem exponent_margin {t ρ : ℝ} (one : 1 < t) (lt : t < ρ) :
    ∃ A : Nat, 4 ≤ A ∧ ∀ n a : Nat, A*a ≤ n → t^n ≤ ρ^(n-2*a) := by
  have pos : 0 < t := by linarith
  have rp : 0 < ρ := by linarith
  let q := t/ρ
  have qpos : 0 ≤ q := div_nonneg pos.le rp.le
  have qlt : q < 1 := (div_lt_one rp).mpr lt
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (show 0 < 1/t^2 by positivity) qlt
  let h := k+2
  have small : q^h ≤ 1/t^2 := (pow_le_pow_of_le_one qpos qlt.le (by dsimp [h]; omega)).trans hk.le
  have gain : t^(h+2) ≤ ρ^h := by
    change (t/ρ)^h ≤ 1/t^2 at small
    rw [div_pow, div_le_div_iff₀ (pow_pos rp _) (pow_pos pos _)] at small
    simpa [pow_add] using small
  refine ⟨h+2, by dsimp [h]; omega, fun n a bound => ?_⟩
  let rem := n-(h+2)*a
  have eq : (h+2)*a+rem=n := by dsimp [rem]; omega
  have exp : h*a+rem = n-2*a := by rw [Nat.add_mul] at eq; omega
  calc
    _ = (t^(h+2))^a*t^rem := by rw [←pow_mul,←pow_add,eq]
    _ ≤ (ρ^h)^a*ρ^rem := by gcongr
    _ = _ := by rw [←pow_mul,←pow_add,exp]

/-- For every epsilon between zero and one there are linear-size,
bounded-occurrence formulas for all sufficiently large n. Both a specified
start with one correct bit and the common uniform start have the near-two
exponential lower bound. The constants depend only on epsilon. -/
theorem shared_start (ε : ℝ) (ep : 0 < ε) (e1 : ε < 1) :
    ∃ C K N : Nat, ∀ n ≥ N, ∃ F : Formula n,
      OddWitness F.clauses (fun _ => true) ∧ Memoryless.Simple F ∧ F.clauses.length ≤ C*n ∧
      (∀ i, Occurrences.count F.clauses i ≤ K) ∧
      (∀ x : Point n, level x ≤ n/2 → ENNReal.ofReal ((2-ε)^n/4) ≤ mean F x) ∧
      ENNReal.ofReal ((2-ε)^n/4)/2 ≤ startMean F := by
  let ρ := 2-ε/2
  have r1 : 1 < ρ := by dsimp [ρ]; linarith
  have r2 : ρ < 2 := by dsimp [ρ]; linarith
  obtain ⟨A, a4, margin⟩ := exponent_margin (t := 2-ε) (ρ := ρ) (by linarith) (by dsimp [ρ]; linarith)
  obtain ⟨L,hL⟩ := exists_nat_gt (3*ρ/(2-ρ))
  have gain : 3*ρ ≤ (2-ρ)*L := by
    have h := (div_lt_iff₀ (show 0 < 2-ρ by linarith)).mp hL
    linarith
  let k := 2*A*(2*L+3)
  have k2 : 2 ≤ k := by dsimp [k]; nlinarith
  obtain ⟨D, graph⟩ := exists_layers k k2
  refine ⟨1+2^D,1+3*((D+1)*2^D), k, fun n large => ?_⟩
  have npos : 0 < n := by omega
  obtain ⟨P,hit⟩ := graph n npos
  let r := threshold n k
  let a := (2*L+3)*r
  let b := n-a
  have kr : r*k ≤ n+k-1 := Nat.div_mul_le_self _ _
  have aa : A*a ≤ n := by
    have prod : r*k = 2*(A*a) := by dsimp [k,a]; ring
    omega
  have four : 4*a ≤ n := (Nat.mul_le_mul_right a a4).trans aa
  have ab : a < b := by dsimp [b]; omega
  have bn : b ≤ n := Nat.sub_le ..
  let ts := SparseFamily.triples P
  let F := formula ts
  have ratio (x : Point n) (lo : a < level x) (hi : level x < b) :
      ρ*(3*((n:ℝ)-level x)+numBad ts x) ≤ 2*numBad ts x := by
    have h := SparseFamily.band P hit L x lo.le (by
      have two : 2*r ≤ a := Nat.mul_le_mul_right r (by omega)
      dsimp [b] at hi; omega)
    have cap : level x ≤ n := by omega
    let U : ℝ := n-level x
    have up : 0 ≤ U := sub_nonneg.mpr (by exact_mod_cast cap)
    change L*(n-level x) ≤ numBad ts x at h
    have H : (L:ℝ)*U ≤ numBad ts x := by
      have hh : (↑(L*(n-level x)) : ℝ) ≤ numBad ts x := by exact_mod_cast h
      simpa [U,Nat.cast_sub cap] using hh
    have h1 := mul_le_mul_of_nonneg_right gain up
    have h2 := mul_le_mul_of_nonneg_left H (show 0 ≤ 2-ρ by linarith)
    change ρ*(3*U+_) ≤ _
    nlinarith only [h1,h2]
  have init (x : Point n) (half : level x ≤ n/2) : ENNReal.ofReal ((2-ε)^n/4) ≤ mean F x := by
    have low := SparseBarrier.walk_lower ts a b ab bn ρ r1 r2 ratio x (by dsimp [b]; omega)
    apply low.trans'
    apply ENNReal.ofReal_le_ofReal
    have eq : b-a = n-2*a := by dsimp [b]; omega
    rw [eq]; linarith only [margin n a aa]
  refine ⟨F, promised ts, Memoryless.planted_simple ts, SparseFamily.linear P, SparseFamily.occurrence P, init, paired_start_lower _ _ ?_⟩
  intro x
  by_cases ok : level x ≤ n/2
  · exact (init x ok).trans le_self_add
  · apply (init (complement n x) ?_).trans le_add_self
    rw [level_complement]; omega

end SatWalk.SparseSeparation
