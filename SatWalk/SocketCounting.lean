import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace SatWalk.SocketCounting
open Finset
open scoped BigOperators

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

private theorem transport (s t : Finset W) (eq : s.card = t.card) :
    ∃ e : Equiv.Perm W, s.map e.toEmbedding = t := by
  classical
  let f := Finset.equivOfCardEq eq
  let g : {x : W // x ∉ s} ≃ {x : W // x ∉ t} := Fintype.equivOfCardEq (by simp [eq])
  let e := Equiv.subtypeCongr f g
  refine ⟨e, Finset.eq_of_subset_of_card_le ?_ (by simp [eq])⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  have h : e a = (f ⟨a,ha⟩).val := by simp [e, Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos ha]
  exact h ▸ (f ⟨a,ha⟩).property

private def fiber (s : Finset V) (t : Finset W) :=
  (univ : Finset (V ≃ W)).filter fun p => s.map p.toEmbedding = t

private theorem fiber_eq (s : Finset V) (u t : Finset W) (eq : u.card = t.card) :
    (fiber s u).card = (fiber s t).card := by
  classical
  obtain ⟨g, hg⟩ := transport u t eq
  apply card_equiv ((Equiv.refl V).equivCongr g)
  intro p
  simp only [fiber, mem_filter, mem_univ, true_and]
  change s.map p.toEmbedding = u ↔ s.map (p.trans g).toEmbedding = t
  rw [← hg]
  change _ ↔ s.map (p.toEmbedding.trans g.toEmbedding) = _
  rw [← map_map]; simp

/-- Exact confinement probability under a uniform socket bijection, written
without division. Each set of possible images of the same size has equal mass. -/
theorem confined_exact (e : V ≃ W) (s : Finset V) (t : Finset W) :
    ((univ : Finset (V ≃ W)).filter (fun p => s.map p.toEmbedding ⊆ t)).card *
        (Fintype.card W).choose s.card =
      Fintype.card (V ≃ W) * t.card.choose s.card := by
  classical
  let image := fun p : V ≃ W => s.map p.toEmbedding
  let u := image e
  have count (a : Finset W) :
      ((univ : Finset (V ≃ W)).filter (fun p => image p ⊆ a)).card =
        a.card.choose s.card * (fiber s u).card := by
    have h := sum_card_fiberwise_eq_card_filter (univ : Finset (V ≃ W)) (a.powersetCard s.card) image
    simp only [mem_powersetCard, image, card_map, and_true] at h
    rw [← h, ← card_powersetCard]
    calc
      _ = ∑ _v ∈ a.powersetCard s.card, (fiber s u).card := by
        apply sum_congr rfl
        intro v hv
        exact fiber_eq s v u ((mem_powersetCard.mp hv).2.trans (by simp [u,image]))
      _ = _ := by simp
  have full := count univ
  simp at full
  rw [count, full]
  ring

/-- Bounding the hypergeometric probability by independent draws. -/
theorem choose_ratio (n t k : Nat) (ht : t ≤ n) :
    t.choose k * n^k ≤ n.choose k * t^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < t
    · have hn : k ≤ n := by omega
      have hs : (t-k)*n ≤ (n-k)*t := by
        rw [Nat.sub_mul, Nat.sub_mul]
        have := Nat.mul_le_mul_left k ht
        rw [Nat.mul_comm t n]; omega
      have h := Nat.mul_le_mul ih hs
      have mult : (t.choose (k+1) * n^(k+1)) * (k+1) ≤
          (n.choose (k+1) * t^(k+1)) * (k+1) := by
        calc
          _ = (t.choose (k+1)*(k+1)) * n^k * n := by rw [pow_succ]; ring
          _ = (t.choose k * n^k) * ((t-k)*n) := by rw [Nat.choose_succ_right_eq]; ring
          _ ≤ (n.choose k * t^k) * ((n-k)*t) := h
          _ = (n.choose (k+1)*(k+1)) * t^k * t := by rw [Nat.choose_succ_right_eq]; ring
          _ = _ := by rw [pow_succ]; ring
      exact Nat.le_of_mul_le_mul_right mult (by omega)
    · simp [Nat.choose_eq_zero_of_lt (show t < k+1 by omega)]

/-- A real-valued bound suitable for a union bound. -/
theorem confined_le (e : V ≃ W) (s : Finset V) (t : Finset W) (pos : 0 < Fintype.card W) :
    (((univ : Finset (V ≃ W)).filter (fun p => s.map p.toEmbedding ⊆ t)).card : ℝ) ≤
      Fintype.card (V ≃ W) * ((t.card : ℝ) / Fintype.card W) ^ s.card := by
  have hk : s.card ≤ Fintype.card W := (Fintype.card_congr e) ▸ card_le_univ s
  have hden : 0 < (Fintype.card W).choose s.card := Nat.choose_pos hk
  have h := confined_exact e s t
  have hratio := choose_ratio _ _ s.card (card_le_univ t)
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
  exact_mod_cast (show _ ≤ _ from Nat.le_of_mul_le_mul_right (by
    calc
      _ = (((univ : Finset (V ≃ W)).filter (fun p => s.map p.toEmbedding ⊆ t)).card *
          (Fintype.card W).choose s.card) * (Fintype.card W)^s.card := by ring
      _ = _ := by rw [h]; ring
      _ ≤ Fintype.card (V ≃ W) * ((Fintype.card W).choose s.card * t.card^s.card) :=
        Nat.mul_le_mul_left _ hratio
      _ = _ := by ring) hden)

private theorem choose_upper (n k : Nat) (pos : 0 < k) :
    (n.choose k : ℝ) ≤ (3 * n / k : ℝ)^k := by
  have hk : (0 : ℝ) < k := by exact_mod_cast pos
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have ex : Real.exp (k : ℝ) ≤ (3 : ℝ)^k := by
    rw [← one_mul (k : ℝ), mul_comm, Real.exp_nat_mul]
    gcongr; exact Real.exp_one_lt_three.le
  have low := (Real.pow_div_factorial_le_exp (k : ℝ) hk.le k).trans ex
  have num := Nat.choose_le_pow_div (α := ℝ) k n
  rw [div_pow, mul_pow, le_div_iff₀ (by positivity)]
  calc
    _ ≤ ((n : ℝ)^k / k.factorial) * (k : ℝ)^k := by gcongr
    _ = (n : ℝ)^k * ((k : ℝ)^k / k.factorial) := by ring
    _ ≤ (n : ℝ)^k * 3^k := by gcongr
    _ = _ := by ring

/-- Weight 2j has 6j variable sockets and can touch at most 3j checks.
After the two choices of supports, the union bound decays geometrically. -/
theorem weight_bound (m j : Nat) (pos : 0 < j) (small : 26244*j ≤ m) :
    ((2*m).choose (2*j) : ℝ) * (m.choose (3*j) : ℝ) *
        ((3*j : ℕ) / (m : ℝ))^(6*j) ≤ (1/4 : ℝ)^j := by
  have hj : (0 : ℝ) < j := by exact_mod_cast pos
  have hm : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have a := choose_upper (2*m) (2*j) (by omega)
  have b := choose_upper m (3*j) (by omega)
  calc
    _ ≤ (3 * (2*m) / (2*j) : ℝ)^(2*j) * (3*m/(3*j) : ℝ)^(3*j) *
          (3*j/m : ℝ)^(6*j) := by push_cast at *; gcongr
    _ = (6561 * j / m : ℝ)^j := by
      rw [pow_mul, pow_mul, pow_mul, ← mul_pow, ← mul_pow]
      congr 1; field_simp; ring
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ hm]
      exact_mod_cast (show (6561 : ℝ)*j ≤ 1/4 * m by
        have h : (26244 : ℝ)*j ≤ m := by exact_mod_cast small
        linarith)

end SatWalk.SocketCounting
