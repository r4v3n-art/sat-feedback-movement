import SatWalk.SocketCounting
import SatWalk.ParityGadget
import Mathlib.InformationTheory.Hamming

namespace SatWalk.LDPCCode
open Finset SocketCounting
open scoped BigOperators

abbrev Variables (m : Nat) := Fin (2*m)
abbrev Left (m : Nat) := Variables m × Fin 3
abbrev Right (m : Nat) := Fin m × Fin 6
abbrev Pairing (m : Nat) := Left m ≃ Right m

private noncomputable def pairing (m : Nat) : Pairing m :=
  Fintype.equivOfCardEq (by simp; omega)

def wires (p : Pairing m) : ParityGadget.SocketRows (2*m) m := fun j l => (p.symm (j,l)).1

def leftSockets (s : Finset (Variables m)) := s ×ˢ (univ : Finset (Fin 3))
def rightSockets (t : Finset (Fin m)) := t ×ˢ (univ : Finset (Fin 6))

private def trapped (s : Finset (Variables m)) (t : Finset (Fin m)) :=
  (univ : Finset (Pairing m)).filter fun p => (leftSockets s).map p.toEmbedding ⊆ rightSockets t

private def badAt (m j : Nat) : Finset (Pairing m) :=
  ((univ : Finset (Variables m)).powersetCard (2*j)).biUnion fun s =>
  ((univ : Finset (Fin m)).powersetCard (3*j)).biUnion fun t => trapped s t

private theorem badAt_le (m j : Nat) (pos : 0 < j) (small : 26244*j ≤ m) :
    ((badAt m j).card : ℝ) ≤ Fintype.card (Pairing m) * (1/4 : ℝ)^j := by
  have hm : 0 < m := by omega
  let ss := (univ : Finset (Variables m)).powersetCard (2*j)
  let ts := (univ : Finset (Fin m)).powersetCard (3*j)
  let prob : ℝ := (3*j/m : ℝ)^(6*j)
  let L : ℝ := Fintype.card (Pairing m)
  have localBound (s) (hs : s ∈ ss) (t) (ht : t ∈ ts) : ((trapped s t).card : ℝ) ≤ L*prob := by
    have H := confined_le (pairing m) (leftSockets s) (rightSockets t) (by simp [Right]; omega)
    have sc := (mem_powersetCard.mp hs).2
    have tc := (mem_powersetCard.mp ht).2
    change ((trapped s t).card : ℝ) ≤ _ at H
    have cards : (leftSockets s).card = 6*j := by simp [leftSockets, sc]; omega
    have ratio : ((rightSockets t).card : ℝ) / Fintype.card (Right m) = 3*j/m := by
      simp [rightSockets, Right, tc]; field_simp
    simpa only [cards, ratio, L, prob] using H
  have count : ((badAt m j).card : ℝ) ≤ (ss.card : ℝ)*ts.card*(L*prob) := by
    calc
      _ ≤ ∑ s ∈ ss, ((ts.biUnion (trapped s)).card : ℝ) := by
        exact_mod_cast card_biUnion_le (s := ss) (t := fun s => ts.biUnion (trapped s))
      _ ≤ ∑ s ∈ ss, ∑ t ∈ ts, ((trapped s t).card : ℝ) := by
        apply sum_le_sum; intro s _
        exact_mod_cast card_biUnion_le (s := ts) (t := trapped s)
      _ ≤ ∑ _s ∈ ss, ∑ _t ∈ ts, L*prob := by
        apply sum_le_sum; intro s hs; apply sum_le_sum; exact localBound s hs
      _ = _ := by simp; ring
  have w := weight_bound m j pos small
  have cardS : ss.card = (2*m).choose (2*j) := by simp [ss, Variables]
  have cardT : ts.card = m.choose (3*j) := by simp [ts]
  rw [cardS, cardT] at count
  apply count.trans
  dsimp [L, prob] at *
  push_cast at w
  calc
    _ = (Fintype.card (Pairing m) : ℝ) * (((2*m).choose (2*j) : ℝ) * (m.choose (3*j) : ℝ) * (3*j/m : ℝ)^(6*j)) := by ring
    _ ≤ _ := by gcongr

/-- A socket pairing simultaneously expands every positive even support of
size at most twice floor(m/26244). The construction is existential. -/
theorem exists_pairing (m : Nat) :
    ∃ p : Pairing m, ∀ j, 0 < j → 26244*j ≤ m →
      ∀ s : Finset (Variables m), s.card = 2*j →
      ∀ t : Finset (Fin m), t.card = 3*j →
      ¬ (leftSockets s).map p.toEmbedding ⊆ rightSockets t := by
  classical
  let H := m / 26244
  let bad := (range H).biUnion fun z => badAt m (z+1)
  let L : ℝ := Fintype.card (Pairing m)
  have lp : 0 < L := by
    have : Nonempty (Pairing m) := ⟨pairing m⟩
    change (0 : ℝ) < (Fintype.card (Pairing m) : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Pairing m))
  have geom (h : Nat) : (∑ z ∈ range h, (1/4 : ℝ)^(z+1)) ≤ (1-(1/4 : ℝ)^h)/3 := by
    induction h with
    | zero => simp
    | succ h ih => rw [sum_range_succ, pow_succ (1/4 : ℝ) h] at *; linarith
  have bound : (bad.card : ℝ) < L := by
    calc
      _ ≤ ∑ z ∈ range H, ((badAt m (z+1)).card : ℝ) := by
        exact_mod_cast card_biUnion_le (s := range H) (t := fun z => badAt m (z+1))
      _ ≤ ∑ z ∈ range H, L*(1/4 : ℝ)^(z+1) := by
        apply sum_le_sum; intro z hz
        have h := (Nat.le_div_iff_mul_le (by decide : 0 < 26244)).mp (show z+1 ≤ m/26244 from mem_range.mp hz)
        exact badAt_le m _ (by omega) (by omega)
      _ = L * ∑ z ∈ range H, (1/4 : ℝ)^(z+1) := by rw [mul_sum]
      _ < L := by
        have h := geom H
        have positive : 0 < (1/4 : ℝ)^H := by positivity
        exact ((mul_lt_mul_iff_right₀ lp).mpr (show (∑ z ∈ range H, (1/4 : ℝ)^(z+1)) < 1 by linarith)).trans_eq (mul_one L)
  have ne : bad ≠ univ := by intro eq; simp [eq, L] at bound
  obtain ⟨p, hp⟩ := (show ∃ p, p ∉ bad by simpa [eq_univ_iff_forall] using ne)
  refine ⟨p, fun j hj hsmall s hs t ht conf => hp ?_⟩
  cases j with
  | zero => omega
  | succ z =>
    apply mem_biUnion.mpr
    refine ⟨z, mem_range.mpr ((Nat.le_div_iff_mul_le (by decide)).mpr (by omega)), ?_⟩
    apply mem_biUnion.mpr
    refine ⟨s, mem_powersetCard.mpr ⟨subset_univ _, hs⟩, mem_biUnion.mpr ?_⟩
    exact ⟨t, mem_powersetCard.mpr ⟨subset_univ _, ht⟩, mem_filter.mpr ⟨mem_univ _,conf⟩⟩


/-- The executable learner and Mathlib's finite Hamming metric count precisely
the same coordinates. -/
theorem hamming_eq_gap (x y : FeedbackCube.Point n) : hammingDist x y = FeedbackCube.gap x y := by
  have eq : Finset.univ.filter (fun i => x i ≠ y i) = (FeedbackCube.differences x y).toFinset := by
    ext; simp
  rw [hammingDist,eq,List.toFinset_card_of_nodup (FeedbackCube.differences_nodup x y)]; rfl

private def support (x y : FeedbackCube.Point (2*m)) := univ.filter fun i => x i ≠ y i

private def neighbors (A : ParityGadget.SocketRows (2*m) m) (s : Finset (Variables m)) (j : Fin m) :=
  univ.filter fun h : Fin 6 => A j h ∈ s

private theorem socket_sum (p : Pairing m) (s : Finset (Variables m)) :
    ∑ j, (neighbors (wires p) s j).card = 3*s.card := by
  classical
  let active := (leftSockets s).map p.toEmbedding
  have mem (v : Right m) : v ∈ active ↔ (p.symm v).1 ∈ s := by
    change _ ∈ Finset.map _ _ ↔ _
    simp [Finset.mem_map_equiv, leftSockets]
  have fiber (j : Fin m) : (active.filter (fun v => v.1 = j)).card =
      (neighbors (wires p) s j).card := by
    refine card_bij' (fun v _ => v.2) (fun h _ => (j,h)) ?_ ?_ ?_ ?_
    · rintro ⟨l,h⟩ hv
      obtain ⟨yes, rfl⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨mem_univ _, (mem _).mp yes⟩
    · intro h hh
      exact mem_filter.mpr ⟨(mem _).mpr (mem_filter.mp hh).2, rfl⟩
    · rintro ⟨l,h⟩ hv; simp [(mem_filter.mp hv).2.symm]
    · intros; rfl
  calc
    _ = ∑ j, (active.filter (fun v => v.1 = j)).card := sum_congr rfl (fun j _ => (fiber j).symm)
    _ = active.card := (card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ)
      (s := active) (fun _ _ => mem_univ _)).symm
    _ = _ := by simp [active, leftSockets, Nat.mul_comm]

private theorem parity6 {x y : Fin 6 → Bool}
    (hx : x 5 = ((((x 0 ^^ x 1) ^^ x 2) ^^ x 3) ^^ x 4))
    (hy : y 5 = ((((y 0 ^^ y 1) ^^ y 2) ^^ y 3) ^^ y 4)) :
    Even ((univ.filter (fun i => x i ≠ y i)).card) := by
  rw [Nat.even_iff, card_filter]
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, sum_empty, add_zero]
  simp only [← Nat.add_assoc]
  change ((if x 0 ≠ y 0 then 1 else 0) + (if x 1 ≠ y 1 then 1 else 0) + (if x 2 ≠ y 2 then 1 else 0) + (if x 3 ≠ y 3 then 1 else 0) + (if x 4 ≠ y 4 then 1 else 0) + (if x 5 ≠ y 5 then 1 else 0)) % 2 = 0
  simp only [hx, hy]
  generalize x 0 = a, x 1 = b, x 2 = c, x 3 = d, x 4 = e,
    y 0 = f, y 1 = g, y 2 = h, y 3 = i, y 4 = j
  decide +revert

/-- Among all six-socket, three-incidence codes on 2m coordinates there is
one in which distinct words differ on more than 2 floor(m/26244) coordinates. -/
theorem code_distance (m : Nat) : ∃ p : Pairing m,
    ∀ x y, ParityGadget.Valid (wires p) x → ParityGadget.Valid (wires p) y → x ≠ y →
      2*(m/26244) < FeedbackCube.gap x y := by
  classical
  obtain ⟨p,hp⟩ := exists_pairing m
  refine ⟨p, fun x y hx hy ne => ?_⟩
  let s := support (m := m) x y
  let A := wires p
  have occ (j : Fin m) : Even (neighbors A s j).card := by
    simpa [neighbors, s, support, A] using
      (parity6 (x := fun l => x (A j l)) (y := fun l => y (A j l)) (hx j) (hy j))
  have total := socket_sum p s
  change ∑ j, (neighbors A s j).card = 3*s.card at total
  have he : Even (3*s.card) := total ▸ Finset.even_sum _ (fun j _ => occ j)
  have se : Even s.card := by rw [Nat.even_iff] at he ⊢; omega
  obtain ⟨j, hj⟩ := se
  have jpos : 0 < j := by
    by_contra! h
    have empty : s = ∅ := card_eq_zero.mp (by omega)
    apply ne; funext i; by_contra hi
    have mem : i ∈ s := mem_filter.mpr ⟨mem_univ _, hi⟩
    simp [empty] at mem
  have size : s.card = FeedbackCube.gap x y := by
    exact hamming_eq_gap x y
  by_contra! small
  have jsmall : 26244*j ≤ m := by
    have h : j ≤ m/26244 := by omega
    exact Nat.mul_comm j _ ▸ (Nat.le_div_iff_mul_le (by decide)).mp h
  let touched := univ.filter fun i => 0 < (neighbors A s i).card
  have touchCount : 2*touched.card ≤ 3*s.card := by
    rw [← total]
    calc
      2*touched.card = ∑ i, if 0 < (neighbors A s i).card then 2 else 0 := by rw [← sum_filter]; simp [touched, Nat.mul_comm]
      _ ≤ _ := by
        apply sum_le_sum; intro i _
        obtain ⟨u,hu⟩ := occ i
        split <;> omega
  obtain ⟨t, sub, _, ht⟩ := exists_subsuperset_card_eq (subset_univ touched)
    (show touched.card ≤ 3*j by omega) (show 3*j ≤ (univ : Finset (Fin m)).card by simp; omega)
  apply hp j jpos jsmall s (by omega) t ht
  intro v hv
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hv
  have slot : (p a).2 ∈ neighbors A s (p a).1 := by
    simpa [neighbors, A, wires, leftSockets] using (show a.1 ∈ s from (mem_product.mp ha).1)
  exact mem_product.mpr ⟨sub (mem_filter.mpr ⟨mem_univ _, card_pos.mpr ⟨_,slot⟩⟩), mem_univ _⟩

end SatWalk.LDPCCode
