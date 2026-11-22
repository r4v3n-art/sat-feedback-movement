import SatWalk.SocketCounting
import SatWalk.PlantedWalk
import SatWalk.FeedbackBatches
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

noncomputable section
namespace SatWalk.SparseGraph
open Finset SocketCounting

abbrev Layers (n D : Nat) := Fin D → Equiv.Perm (Fin n)

def neighbors (P : Layers n D) (x : Fin n) := univ.image (fun l => P l x)
def threshold (n K : Nat) := (n+K-1)/K

/-- Any two sufficiently large sets share a directed edge. -/
def Hits (P : Layers n D) (r : Nat) :=
  ∀ X Y : Finset (Fin n), X.card = r → Y.card = r →
    ∃ x ∈ X, ∃ y ∈ Y, y ∈ neighbors P x

private def avoids (X Y : Finset (Fin n)) :=
  (univ : Finset (Equiv.Perm (Fin n))).filter fun p => X.map p.toEmbedding ⊆ Yᶜ

private def miss (D : Nat) (X Y : Finset (Fin n)) :=
  Fintype.piFinset (fun _ : Fin D => avoids X Y)

/-- A constant number of permutation layers suffices for every size. The
number of in-neighbors and out-neighbors is bounded by the number of layers. -/
theorem exists_layers (K : Nat) (hk : 2 ≤ K) :
    ∃ D, ∀ n, 0 < n → ∃ P : Layers n D, Hits P (threshold n K) := by
  classical
  let q : ℝ := 1-1/K
  have kp : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have q0 : 0 ≤ q := by change (0:ℝ) ≤ 1-1/K; rw [sub_nonneg, div_le_one kp]; exact_mod_cast (show 1 ≤ K by omega)
  have q1 : q < 1 := by dsimp [q]; linarith [div_pos zero_lt_one kp]
  obtain ⟨s,hs⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ)<1/8) q1
  let D := K*s
  refine ⟨D, fun n hn => ?_⟩
  let r := threshold n K
  have cover : n ≤ r*K := FeedbackBatches.covered (by omega : 0<K) n
  have rn : r ≤ n := (FeedbackBatches.turns_le (by omega : 0<K) n n).mpr (by
    have := Nat.mul_le_mul_left n (show 1 ≤ K by omega); omega)
  let choices := (univ : Finset (Fin n)).powersetCard r
  let forbidden := choices.biUnion fun X => choices.biUnion fun Y => miss D X Y
  let L : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have lp : 0 < L := by dsimp [L]; positivity
  have localBound (X : Finset (Fin n)) (hX : X ∈ choices) (Y : Finset (Fin n)) (hY : Y ∈ choices) : ((miss D X Y).card : ℝ) ≤ L^D * ((1/8 : ℝ)^n) := by
    have xc := (mem_powersetCard.mp hX).2
    have yc := (mem_powersetCard.mp hY).2
    have h := confined_le (Equiv.refl (Fin n)) X Yᶜ (by simpa)
    have frac : ((n-r:Nat) : ℝ)/n ≤ q := by
      rw [Nat.cast_sub rn, div_le_iff₀ (by positivity)]
      change _ ≤ (1-1/(K:ℝ))*_
      field_simp; nlinarith only [show (n:ℝ) ≤ r*K by exact_mod_cast cover]
    have one : ((avoids X Y).card : ℝ) ≤ L*q^r := by
      change ((avoids X Y).card : ℝ) ≤ _ at h
      simp only [card_compl, Fintype.card_fin, yc, xc] at h
      apply h.trans; gcongr
    have pow : (q^r)^D ≤ (1/8:ℝ)^n := by
      calc
        _ = (q^s)^(r*K) := by simp [D, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        _ ≤ (1/8:ℝ)^(r*K) := by gcongr
        _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) cover
    simpa [miss, Fintype.card_piFinset, mul_pow] using
      (pow_le_pow_left₀ (Nat.cast_nonneg _) one D).trans (show (L*q^r)^D ≤ L^D*((1/8:ℝ)^n) by rw [mul_pow]; gcongr)
  have total : (forbidden.card : ℝ) < L^D := by
    calc
      _ ≤ ∑ X ∈ choices, ((choices.biUnion (miss D X)).card : ℝ) := by exact_mod_cast card_biUnion_le ..
      _ ≤ ∑ X ∈ choices, ∑ Y ∈ choices, ((miss D X Y).card : ℝ) := by
        apply sum_le_sum; intro X _; exact_mod_cast card_biUnion_le ..
      _ ≤ ∑ _X ∈ choices, ∑ _Y ∈ choices, L^D*(1/8:ℝ)^n := by
        apply sum_le_sum; intro X hx; apply sum_le_sum; exact localBound X hx
      _ = (choices.card:ℝ)^2 * (L^D*(1/8:ℝ)^n) := by simp; ring
      _ ≤ ((2:ℝ)^n)^2 * (L^D*(1/8:ℝ)^n) := by
        gcongr
        exact_mod_cast (show choices.card ≤ 2^n by simpa [choices] using Nat.choose_le_two_pow n r)
      _ = L^D * ((1/2:ℝ)^n) := by
        rw [show (1/2:ℝ) = 2*2*(1/8) by norm_num, mul_pow, mul_pow]; ring
      _ < L^D := by
        have h : (1/2:ℝ)^n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) hn.ne'
        simpa using (mul_lt_mul_of_pos_left h (pow_pos lp D))
  have proper : forbidden ≠ univ := by
    intro eq; simp [eq,L,Fintype.card_pi] at total
  obtain ⟨P,hp⟩ : ∃ P, P ∉ forbidden := by simpa [eq_univ_iff_forall] using proper
  refine ⟨P, fun X Y xcard ycard => ?_⟩
  by_contra! no
  apply hp
  refine mem_biUnion.mpr ⟨X, mem_powersetCard.mpr ⟨subset_univ _,xcard⟩, mem_biUnion.mpr
    ⟨Y, mem_powersetCard.mpr ⟨subset_univ _,ycard⟩, ?_⟩⟩
  apply Fintype.mem_piFinset.mpr
  intro l
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  rintro y hy
  obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
  exact mem_compl.mpr (fun h => no x hx _ h (mem_image.mpr ⟨l,mem_univ _,rfl⟩))

end SatWalk.SparseGraph
