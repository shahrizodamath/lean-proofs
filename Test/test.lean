-- My first proofs in Lean 4

theorem add_comm_test : 1 + 2 = 2 + 1 := by rfl

theorem and_intro (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  exact ⟨hp, hq⟩

#check Nat.add_comm
