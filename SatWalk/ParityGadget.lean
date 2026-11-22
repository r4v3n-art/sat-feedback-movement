import SatWalk.CodeLowerBound

namespace SatWalk.ParityGadget
open Model FeedbackCube

/-- Four signed clauses exclude exactly the four odd tuples. Literal
positions retain multiplicity even if two sockets name one variable. -/
def gate (a b c : Fin n) : List (Clause n) :=
  [[⟨a,false⟩, ⟨b,true⟩, ⟨c,true⟩],
   [⟨a,true⟩, ⟨b,false⟩, ⟨c,true⟩],
   [⟨a,true⟩, ⟨b,true⟩, ⟨c,false⟩],
   [⟨a,false⟩, ⟨b,false⟩, ⟨c,false⟩]]

theorem gate_spec (a b c : Fin n) (x : Point n) :
    (Solved (gate a b c) x ↔ x c = (x a ^^ x b)) ∧
    (OddWitness (gate a b c) x ↔ x c = (x a ^^ x b)) := by
  cases ea : x a <;> cases eb : x b <;> cases ec : x c <;>
    simp [Solved, Broken, OddWitness, gate, parity, holds, ea, eb, ec]

theorem gate_width {q : Clause n} (mem : q ∈ gate a b c) : q.length = 3 := by
  simp [gate] at mem
  rcases mem with rfl | rfl | rfl | rfl <;> rfl

abbrev Wires (n : Nat) := Fin n × Fin n × Fin n

def encode (qs : List (Wires n)) : Formula n where
  clauses := qs.flatMap fun (a,b,c) => gate a b c
  width := by
    intro q mem
    obtain ⟨⟨a,b,c⟩,_,h⟩ := List.mem_flatMap.mp mem
    exact Nat.le_of_eq (gate_width h)

def Checks (qs : List (Wires n)) (x : Point n) :=
  ∀ t ∈ qs, x t.2.2 = (x t.1 ^^ x t.2.1)

theorem encode_spec (qs : List (Wires n)) (x : Point n) :
    (Solved (encode qs).clauses x ↔ Checks qs x) ∧
    (OddWitness (encode qs).clauses x ↔ Checks qs x) := by
  constructor
  · constructor
    · intro ok ⟨a,b,c⟩ mem
      exact (gate_spec a b c x).1.mp fun q h => ok q (List.mem_flatMap.mpr ⟨_,mem,h⟩)
    · intro ok q h
      obtain ⟨⟨a,b,c⟩, mem, hg⟩ := List.mem_flatMap.mp h
      exact (gate_spec a b c x).1.mpr (ok _ mem) q hg
  · constructor
    · intro ok ⟨a,b,c⟩ mem
      exact (gate_spec a b c x).2.mp fun q h => ok q (List.mem_flatMap.mpr ⟨_,mem,h⟩)
    · intro ok q h
      obtain ⟨⟨a,b,c⟩, mem, hg⟩ := List.mem_flatMap.mp h
      exact (gate_spec a b c x).2.mpr (ok _ mem) q hg

/-- Six ordered sockets per check, with no simplicity assumption. -/
abbrev SocketRows (b m : Nat) := Fin m → Fin 6 → Fin b
abbrev Coord (b m : Nat) := Fin (b+(m+(m+m)))
def input (i : Fin b) : Coord b m := i.castAdd _
def u (j : Fin m) : Coord b m := (j.castAdd _).natAdd b
def v (j : Fin m) : Coord b m := ((j.castAdd m).natAdd m).natAdd b
def w (j : Fin m) : Coord b m := ((j.natAdd m).natAdd m).natAdd b

def block (A : SocketRows b m) (j : Fin m) : List (Wires (b+(m+(m+m)))) :=
  let s := fun l => input (m := m) (A j l)
  [(s 0, s 1, u j), (u j, s 2, v j), (v j, s 3, w j), (w j, s 4, s 5)]

def formula (A : SocketRows b m) := encode ((List.finRange m).flatMap (block A))
def project (x : Coord b m → Bool) : Point b := fun i => x (input i)
def Valid (A : SocketRows b m) (x : Point b) :=
  ∀ j, let s := fun l => x (A j l)
       s 5 = ((((s 0 ^^ s 1) ^^ s 2) ^^ s 3) ^^ s 4)

def extend (A : SocketRows b m) (x : Point b) : Coord b m → Bool :=
  let fu := fun j => x (A j 0) ^^ x (A j 1)
  let fv := fun j => fu j ^^ x (A j 2)
  let fw := fun j => fv j ^^ x (A j 3)
  Fin.addCases x (Fin.addCases fu (Fin.addCases fv fw))

@[simp] theorem project_extend (A : SocketRows b m) (x : Point b) :
    project (extend A x) = x := by funext i; simp [project, extend, input]

private theorem block_checks (A : SocketRows b m) (x : Coord b m → Bool) :
    Checks ((List.finRange m).flatMap (block A)) x ↔
    ∀ j, let s := fun l => x (input (A j l))
         x (u j) = (s 0 ^^ s 1) ∧ x (v j) = (x (u j) ^^ s 2) ∧
         x (w j) = (x (v j) ^^ s 3) ∧ s 5 = (x (w j) ^^ s 4) := by
  unfold Checks
  rw [List.forall_mem_flatMap]
  simp only [List.mem_finRange, forall_const, block, List.forall_mem_cons,
    List.not_mem_nil, false_implies, implies_true, and_true]

/-- Every valid socket word has an odd witness extension, and every satisfying
assignment has the unique auxiliary values determined by its projection. -/
theorem compilation (A : SocketRows b m) (x : Coord b m → Bool) :
    (Solved (formula A).clauses x ↔ Valid A (project x) ∧ x = extend A (project x)) ∧
    (OddWitness (formula A).clauses x ↔ Solved (formula A).clauses x) := by
  obtain ⟨sol, odd⟩ := encode_spec ((List.finRange m).flatMap (block A)) x
  refine ⟨?_, odd.trans sol.symm⟩
  rw [show Solved (formula A).clauses x ↔ _ from sol, block_checks]
  constructor
  · intro h
    have hu j := (h j).1
    have hv j := (h j).2.1
    have hw j := (h j).2.2.1
    refine ⟨fun j => ?_, ?_⟩
    · simpa only [hw, hv, hu, project] using (h j).2.2.2
    · funext i
      refine Fin.addCases (fun a => ?_) (fun rest => ?_) i
      · simp [extend, project, input]
      · refine Fin.addCases (fun a => ?_) (fun last => ?_) rest
        · simpa [u, extend, project] using hu a
        · refine Fin.addCases (fun a => ?_) (fun a => ?_) last
          · simpa [v, extend, project, hu] using hv a
          · simpa only [w, extend, project, hv, hu, Fin.addCases_right] using hw a
  · rintro ⟨ok,eq⟩ j
    rw [eq]
    simp only [extend, input, u, v, w, Fin.addCases_left, Fin.addCases_right, true_and, eq_self]
    exact ok j

private theorem report_none (F : Formula n) (x : Point n) :
    orderedReport F x = none ↔ Solved F.clauses x := by
  simp [orderedReport, List.find?_eq_none, Solved]

/-- Hamming distance on the live input coordinates cannot increase under projection. -/
theorem project_gap (x y : Coord b m → Bool) : gap (project x) (project y) ≤ gap x y := by
  let xs := (differences (project x) (project y)).map (input (m := m))
  have nd : xs.Nodup := List.Pairwise.map input (fun a b ne eq => ne (Fin.ext (congrArg (fun j : Coord _ m => j.val) eq))) (differences_nodup ..)
  have sub : xs ⊆ differences x y := by
    intro i mem
    obtain ⟨a, h, rfl⟩ := List.mem_map.mp mem
    have ne := (mem_differences (x := project x) (y := project y)).mp h
    exact mem_differences.mpr ne
  simpa [xs, gap] using nd.length_le_of_subset sub

theorem preserves_distance (A : SocketRows b m) (d : Nat)
    (dist : ∀ x y, Valid A x → Valid A y → x ≠ y → d ≤ gap x y) :
    CodeLowerBound.Separated (formula A) d := by
  intro x y hx hy ne
  have X := (compilation A x).1.mp ((report_none ..).mp hx)
  have Y := (compilation A y).1.mp ((report_none ..).mp hy)
  have neq : project x ≠ project y := fun eq => ne (X.2.trans ((congrArg (extend A) eq).trans Y.2.symm))
  exact Nat.le_trans (dist _ _ X.1 Y.1 neq) (project_gap ..)

end SatWalk.ParityGadget
