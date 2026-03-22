import Mathlib

-- Absorption Laws (Boolean Algebra)

-- p ∧ (p ∨ q) = p
theorem absorption_and (p q : Prop) : p ∧ (p ∨ q) ↔ p := by
  constructor
  · intro ⟨hp, _⟩
    exact hp
  · intro hp
    exact ⟨hp, Or.inl hp⟩

-- p ∨ (p ∧ q) = p
theorem absorption_or (p q : Prop) : p ∨ (p ∧ q) ↔ p := by
  constructor
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hpq => exact hpq.1
  · intro hp
    left
    exact hp
