def gcd (a b : Nat) : Nat :=
  match a with
  | 0 => b
  | a + 1 => gcd (b % (a + 1)) (a + 1)
termination_by a
decreasing_by
  exact Nat.mod_lt b (Nat.succ_pos a)

#eval gcd 18 9
