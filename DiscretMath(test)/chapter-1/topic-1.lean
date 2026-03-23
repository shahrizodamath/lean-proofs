import Mathlib

-- Distributive Laws (Discrete Math)

-- AND distributes over OR
theorem distrib_and_or (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · intro ⟨hp, hqr⟩
    cases hqr with
    | inl hq => left; exact ⟨hp, hq⟩
    | inr hr => right; exact ⟨hp, hr⟩
  · intro h
    cases h with
    | inl hpq => exact ⟨hpq.1, Or.inl hpq.2⟩
    | inr hpr => exact ⟨hpr.1, Or.inr hpr.2⟩

-- OR distributes over AND
theorem distrib_or_and (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  · intro h
    cases h with
    | inl hp => exact ⟨Or.inl hp, Or.inl hp⟩
    | inr hqr => exact ⟨Or.inr hqr.1, Or.inr hqr.2⟩
  · intro ⟨hpq, hpr⟩
    cases hpq with
    | inl hp => left; exact hp
    | inr hq =>
      cases hpr with
      | inl hp => left; exact hp
      | inr hr => right; exact ⟨hq, hr⟩
