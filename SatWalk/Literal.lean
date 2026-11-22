namespace SatWalk

/-- A literal on one of n Boolean variables, with its satisfying bit. -/
structure Literal (n : Nat) where
  var : Fin n
  value : Bool

end SatWalk
