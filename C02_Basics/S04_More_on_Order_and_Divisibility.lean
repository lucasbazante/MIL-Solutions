import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left a b)
#check (le_max_right a b)
#check (max_le : c ≥ a → c ≥ b → c ≥ max a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by {
  apply ge_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left
}

example : min (min a b) c = min a (min b c) := by {
  have h₀ : ∀ x y z : ℝ, x ⊓ y ⊓ z ≤ x := by
    intro x y z
    apply le_trans
    repeat apply min_le_left
  have h₁ : ∀ x y z : ℝ, x ⊓ y ⊓ z ≤ y ⊓ z := by
    intro x y z
    apply le_min
    . apply (min_le_left _ _).trans (min_le_right x y)
    . apply min_le_right
  have h₂ : ∀ x y z : ℝ, x ⊓ (y ⊓ z) ≤ x ⊓ y := by
    intro x y z
    apply le_min
    . apply min_le_left
    . apply (min_le_right _ _).trans (min_le_left y z)
  have h₃ : ∀ x y z : ℝ, x ⊓ (y ⊓ z) ≤ z := by
    intro x y z
    apply le_trans
    repeat apply min_le_right

  apply le_antisymm
  . apply le_min
    apply h₀
    apply h₁
  . apply le_min
    apply h₂
    apply h₃
}

theorem aux : min a b + c ≤ min (a + c) (b + c) := by {
  apply le_min
  . linarith [min_le_left a b]
  . linarith [min_le_right a b]
}

example : min a b + c = min (a + c) (b + c) := by {
  apply le_antisymm
  . apply aux
  . nth_rw 2 [← add_neg_cancel_right a c]
    nth_rw 2 [← add_neg_cancel_right b c]
    linarith [aux (a + c) (b + c) (-c)]
}

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
#check sub_add_cancel

example : |a| - |b| ≤ |a - b| := by {
  have h := abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith
}

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by {
  have h₀ : x ∣ y * (x * z) + x^2 := by
    apply dvd_add
    apply dvd_mul_of_dvd_right
    apply dvd_mul_right
    apply dvd_mul_left
  apply dvd_add h₀
  apply dvd_mul_of_dvd_right h
}

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    . apply Nat.gcd_dvd_right
    . apply Nat.gcd_dvd_left
end
