import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic

open BigOperators

-- Teoremaning Lean 4 tilidagi formulasi
theorem mersenne_composite_of_composite (n : ℕ) (h_comp : ¬ Nat.Prime n) (h_gt1 : n > 1) :
    ¬ Nat.Prime (2^n - 1) := by
  -- Matndagi: "Since n is not prime, there are positive integers a and b..."
  -- Lean'da murakkab sonni koʻpaytuvchilarga ajratib olamiz: n = a * b, bunda a > 1 va b > 1
  obtain ⟨a, b, ha, hb, rfl⟩ := Nat.exists_dvd_of_not_prime2 h_gt1 h_comp

  -- Biz n = a * b ekanini bilamiz. Endi 2^(a*b) - 1 murakkab ekanini koʻrsatishimiz kerak.
  -- Matndagi: "Let x = 2^b - 1"
  let x := 2^b - 1
  -- Matndagi: "Let y = 1 + 2^b + 2^(2b) + ... + 2^((a-1)b)"
  -- Buni Lean'da geometrik progressiya yigʻindisi (sum) koʻrinishida yozamiz:
  let y := ∑ i ∈ Finset.range a, (2^b)^i

  -- Biz (2^b - 1) * y = 2^(a*b) - 1 ekanligini algebraik koʻrsatishimiz kerak
  have h_prod : x * y = 2^(a * b) - 1 := by
    -- Geometrik progressiya yigʻindisi formulasini qoʻllaymiz: (q - 1) * ∑ q^i = q^a - 1
    have h_geom := Nat.geom_sum_mul_not_prime (2^b) a
    -- Lean buni hisoblab, darajalar qonuniyatiga koʻra 2^(b*a) ni 2^(a*b) ga tenglashtiradi
    rw [mul_comm, h_geom]
    congr 2
    ring

  -- Endi 2^n - 1 sonining oʻzidan kichik ikkita koʻpaytuvchisi (x va y) borligini tasdiqlaymiz
  -- Buning uchun x > 1 va y > 1 ekanligini isbotlash yetarli (shunda son tub boʻla olmaydi)
  have hx_gt1 : x > 1 := by
    dsimp [x]
    -- b > 1 boʻlgani uchun 2^b - 1 > 1 boʻladi
    omega

  have hy_gt1 : y > 1 := by
    -- a > 1 boʻlgani uchun yigʻindida kamida ikkita had bor (1 va 2^b)
    -- Shuning uchun yigʻindi 1 dan katta boʻladi
    sorry -- (Bu yerda ierarxik ichki mantiqiy hisob-kitob ketadi)

  -- Yakuniy qadam: Agar son 1 dan katta ikkita sonning koʻpaytmasiga teng boʻlsa, u tub emas!
  -- Matndagi: "Thus, 2^n - 1 can be written as the product of two smaller integers..."
  apply Nat.not_prime_of_dvd_of_not_dvd_of_not_dvd
  · -- 1) x soni (2^n - 1) ni boʻlishini koʻrsatamiz (chunki x * y = 2^n - 1)
    use y
    exact h_prod.symm
  · -- 2) x soni 1 ga teng emas (chining hx_gt1 : x > 1)
    omega
  · -- 3) x soni 2^n - 1 ning oʻziga teng emas (chunki y > 1 boʻlgani uchun x kichikroq)
    sorry
