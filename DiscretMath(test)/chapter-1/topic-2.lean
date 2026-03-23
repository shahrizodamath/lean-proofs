import Mathlib

-- De Morgan's Laws

-- ¬(p ∧ q) ↔ ¬p ∨ ¬q
theorem demorgan_and (p q : Prop) : ¬(p ∧ q) ↔ ¬p ∨ ¬q := by
  constructor
  · intro h
    by_cases hp : p
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp
  · intro h ⟨hp, hq⟩
    cases h with
    | inl hnp => exact hnp hp
    | inr hnq => exact hnq hq

-- ¬(p ∨ q) ↔ ¬p ∧ ¬q
theorem demorgan_or (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  · intro h
    constructor
    · intro hp; exact h (Or.inl hp)
    · intro hq; exact h (Or.inr hq)
  · intro ⟨hnp, hnq⟩ h
    cases h with
    | inl hp => exact hnp hp
    | inr hq => exact hnq hq
