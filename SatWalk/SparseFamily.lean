import SatWalk.SparseGraph
import SatWalk.Occurrences

noncomputable section
namespace SatWalk.SparseFamily
open SparseGraph PlantedWalk FeedbackCube Model Finset

def allowed (P : Layers n D) := univ.filter fun t : Triple n => t.tails ⊆ neighbors P t.owner
def triples (P : Layers n D) := (allowed P).toList

private theorem degree (P : Layers n D) (i) : (neighbors P i).card ≤ D := by
  simpa [neighbors] using (card_image_le (s := (univ : Finset (Fin D))) (f := fun l => P l i))

private theorem fiber_bound (P : Layers n D) (S : Finset (Triple n)) (sub : S ⊆ allowed P)
    (i : Fin n) : (S.filter (fun t => t.owner = i)).card ≤ 2^D := by
  apply (card_le_card_of_injOn (t := (neighbors P i).powerset) (fun t => t.tails) ?_ ?_).trans
  · rw [card_powerset]; exact Nat.pow_le_pow_right (by decide) (degree P i)
  · intro t ht
    obtain ⟨yes, eq⟩ := mem_filter.mp ht
    exact mem_powerset.mpr (eq ▸ (mem_filter.mp (sub yes)).2)
  · rintro ⟨u,x,_,_⟩ hu ⟨v,y,_,_⟩ hv eq
    obtain ⟨_,rfl⟩ := mem_filter.mp hu
    obtain ⟨_,h⟩ := mem_filter.mp hv
    cases h; cases eq; rfl

theorem linear (P : Layers n D) : (formula (triples P)).clauses.length ≤ (1+2^D)*n := by
  have h := card_le_mul_card_image_of_maps_to (s := allowed P) (t := univ) (f := Triple.owner)
    (fun _ _ => mem_univ _) (2^D) (fun i _ => fiber_bound P _ (fun _ h => h) i)
  simp [formula,triples,add_mul] at *; omega

private def relevant (P : Layers n D) (z : Fin n) :=
  (allowed P).filter fun t => t.owner = z ∨ z ∈ t.tails

theorem occurrence (P : Layers n D) (z : Fin n) :
    Occurrences.count (formula (triples P)).clauses z ≤ 1+3*((D+1)*2^D) := by
  let owners := insert z (univ.image (fun l : Fin D => (P l).symm z))
  have size : owners.card ≤ D+1 := by
    apply (card_insert_le ..).trans; exact Nat.succ_le_succ (by simpa using (card_image_le (s := (univ : Finset (Fin D))) (f := fun l => (P l).symm z)))
  have sub : relevant P z ⊆ allowed P := filter_subset _ _
  have rel := card_le_mul_card_image_of_maps_to (s := relevant P z) (t := owners) (f := Triple.owner)
    (fun t ht => by
      obtain ⟨ok,own|tail⟩ := mem_filter.mp ht
      · exact own ▸ mem_insert_self _ _
      · obtain ⟨l,_,eq⟩ := mem_image.mp ((mem_filter.mp ok).2 tail)
        exact mem_insert_of_mem (mem_image.mpr ⟨l,mem_univ _,(Equiv.symm_apply_eq _).mpr eq.symm⟩))
    (2^D) (fun i _ => fiber_bound P _ sub i)
  have pinCount : Occurrences.count ((List.finRange n).map pin) z = 1 := by
    unfold Occurrences.count
    have flat (xs : List (Fin n)) : (xs.map pin).flatMap (fun c => c.map Literal.var) = xs := by
      induction xs with
      | nil => rfl
      | cons _ _ ih => simp [pin, ih, List.flatMap_map, Function.comp_def] at *
    rw [flat, List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange _)]
  have triCount (ts : List (Triple n)) : Occurrences.count (ts.map clause) z ≤
      3*(ts.filter (fun t => decide (t.owner=z ∨ z ∈ t.tails))).length := by
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      change Occurrences.count ([clause t] ++ ts.map clause) z ≤ _
      rw [Occurrences.count_append]
      by_cases mem : t.owner=z ∨ z ∈ t.tails
      · have bnd : Occurrences.count [clause t] z ≤ 3 := by
          unfold Occurrences.count
          simpa [clause,t.two] using (List.count_le_length (l := (clause t).map Literal.var) (a := z))
        rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using mem), List.length_cons]; omega
      · have zero : Occurrences.count [clause t] z = 0 := by
          apply List.count_eq_zero.mpr; simp [clause] at *; tauto
        rw [List.filter_cons_of_neg (by simpa only [decide_eq_true_eq] using mem),zero,Nat.zero_add]; exact ih
  let ls := (triples P).filter (fun t => decide (t.owner=z ∨ z ∈ t.tails))
  have eq : ls.toFinset = relevant P z := by ext; simp [ls,triples,relevant]
  have countEq : ls.length = (relevant P z).card := by
    rw [← eq, List.toFinset_card_of_nodup (show ls.Nodup from List.filter_sublist.nodup (Finset.nodup_toList _))]
  change Occurrences.count (_ ++ _) z ≤ _
  rw [Occurrences.count_append,pinCount]
  have h := triCount (triples P)
  change _ ≤ 3*ls.length at h
  rw [countEq] at h
  have hs := Nat.mul_le_mul_left (2^D) size
  rw [Nat.mul_comm (D+1)]; omega

/-- If every large pair of sets has an edge, fewer than r owners can have
fewer than ell distinct neighbors in S, provided S is large enough. -/
private theorem weak_count (P : Layers n D) (hit : Hits P r) (S : Finset (Fin n)) (ell : Nat)
    (big : (ell+1)*r ≤ S.card) :
    (univ.filter (fun i => ((neighbors P i) ∩ S).card < ell)).card < r := by
  by_contra! tooMany
  obtain ⟨X,weak,xc⟩ := exists_subset_card_eq tooMany
  let used := X.biUnion (fun i => neighbors P i ∩ S)
  have usedSmall : used.card ≤ ell*r := by
    calc
      _ ≤ ∑ i ∈ X, (neighbors P i ∩ S).card := card_biUnion_le
      _ ≤ ∑ _ ∈ X, ell := sum_le_sum (fun i hi => ((mem_filter.mp (weak hi)).2).le)
      _ = _ := by simp [xc,Nat.mul_comm]
  have left := card_le_card_sdiff_add_card (s := S) (t := used)
  obtain ⟨Y,free,yc⟩ := exists_subset_card_eq (show r ≤ (S \ used).card by rw [Nat.add_mul] at big; omega)
  obtain ⟨i,xi,y,xy,edge⟩ := hit X Y xc yc
  obtain ⟨mem,no⟩ := mem_sdiff.mp (free xy)
  exact no (mem_biUnion.mpr ⟨i,xi,mem_inter.mpr ⟨edge,mem⟩⟩)

theorem band (P : Layers n D) (hit : Hits P r) (L : Nat) (x : Point n)
    (hs : (2*L+3)*r ≤ level x) (ho : 2*r ≤ n-level x) :
    L*(n-level x) ≤ numBad (triples P) x := by
  let S := bits x
  let ell := 2*L+2
  let weak := univ.filter (fun i => ((neighbors P i) ∩ S).card < ell)
  let good := Sᶜ \ weak
  have few : weak.card < r := weak_count P hit S ell hs
  have many : n-level x ≤ 2*good.card := by
    have h := card_le_card_sdiff_add_card (s := Sᶜ) (t := weak)
    change Sᶜ.card ≤ good.card+weak.card at h
    rw [card_compl,Fintype.card_fin] at h
    change n-level x ≤ good.card+weak.card at h; omega
  let bads := (allowed P).filter fun t => bad t x
  have countEq : numBad (triples P) x = bads.card := by
    let ls := (triples P).filter (fun t => decide (bad t x))
    have eq : ls.toFinset = bads := by ext; simp [ls,triples,bads]
    rw [← eq,List.toFinset_card_of_nodup (show ls.Nodup from List.filter_sublist.nodup (Finset.nodup_toList _))]; rfl
  let per := fun i => bads.filter (fun t => t.owner = i)
  have enough (i) (hi : i ∈ good) : 2*L ≤ (per i).card := by
    obtain ⟨outside, nw⟩ := mem_sdiff.mp hi
    have out : i ∉ S := mem_compl.mp outside
    let A := neighbors P i ∩ S
    have len : ell ≤ A.card := by simpa [weak, A] using nw
    have two : 2*L ≤ ell.choose 2 := by simp [ell,Nat.choose_succ_succ]; omega
    have inj : (A.powersetCard 2).card ≤ (per i).card := by
      apply card_le_card_of_injOn (fun t : Finset (Fin n) =>
        if h : t.card=2 ∧ i ∉ t then (⟨i,t,h.1,h.2⟩ : Triple n) else
        Classical.choice (show Nonempty (Triple n) from by
          obtain ⟨q,hq,hc⟩ := exists_subset_card_eq (show 2 ≤ A.card by dsimp [ell] at len; omega)
          exact ⟨⟨i,q,hc,fun h => out (mem_inter.mp (hq h)).2⟩⟩))
      · intro t mem
        obtain ⟨st,hc⟩ := mem_powersetCard.mp mem
        have ni : i ∉ t := fun h => out (mem_inter.mp (st h)).2
        have ok : t.card = 2 ∧ i ∉ t := ⟨hc,ni⟩
        simp only [dite_eq_left ok]
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, fun k hk => (mem_inter.mp (st hk)).1⟩,
          ?_, fun k hk => (mem_inter.mp (st hk)).2⟩,rfl⟩
        simpa [S,bits] using out
      · intro t ht u hu eq
        have h (q : Finset (Fin n)) (hq : q ∈ A.powersetCard 2) : q.card=2 ∧ i ∉ q := by
          obtain ⟨sq,hc⟩ := mem_powersetCard.mp hq
          exact ⟨hc, fun hm => out (mem_inter.mp (sq hm)).2⟩
        simpa [h t ht,h u hu] using congrArg Triple.tails eq
    rw [card_powersetCard] at inj
    exact two.trans ((Nat.choose_le_choose _ len).trans inj)
  have total := sum_card_fiberwise_eq_card_filter bads good Triple.owner
  rw [countEq]
  calc
    _ ≤ (2*L)*good.card := by simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left L many
    _ = ∑ _ ∈ good, 2*L := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ good, (per i).card := sum_le_sum enough
    _ ≤ _ := total.trans_le (card_filter_le ..)

end SatWalk.SparseFamily
