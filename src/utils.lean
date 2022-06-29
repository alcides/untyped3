
theorem smaller_than2 {a b x y: ℕ}
 (h1: a ≤ x)
 (h2: b ≤ y) :
 (a + b ≤ x + y) := begin
  exact add_le_add h1 h2
 end

theorem smaller_than3 {a b c x y z: ℕ}
 (h1: a ≤ x)
 (h2: b ≤ y)
 (h3: c ≤ z) :
  a + (b + c) ≤ x + (y + z) := begin
  generalize hbc : b + c = bc,
  generalize hyz : y + z = yz,
  refine add_le_add h1 _,
  rw [←hbc, ←hyz],
  refine add_le_add h2 h3,
 end