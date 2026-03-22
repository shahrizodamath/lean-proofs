import Mathlib

-- Associative Laws (Discrete Math)

-- (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
theorem assoc_and (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  · intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, hq, hr⟩
  · intro ⟨hp, hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩

-- (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
theorem assoc_or (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  · intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => left; exact hp
      | inr hq => right; left; exact hq
    | inr hr => right; right; exact hr
  · intro h
    cases h with
    | inl hp => left; left; exact hp
    | inr hqr =>
      cases hqr with
      | inl hq => left; right; exact hq
      | inr hr => right; exact hr
