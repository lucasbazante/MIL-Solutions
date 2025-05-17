import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by {
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
  . linarith [abs_of_neg h]
}

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by {
  match le_or_gt 0 x with
    | Or.inl h =>
      linarith [abs_of_nonneg h]
    | Or.inr h =>
      rw [abs_of_neg h]
}

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by {
  rcases le_or_gt 0 (x + y) with h | h
  . linarith [abs_of_nonneg h, le_abs_self x, le_abs_self y]
  . linarith [abs_of_neg h, neg_le_abs_self x, neg_le_abs_self y]
}

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by {
  constructor <;> intro h
  . rcases le_or_gt 0 y with hy | hy
    . rw [abs_of_nonneg hy] at h
      left; assumption
    . rw [abs_of_neg hy] at h
      right ; assumption
  . rcases h with h | h
    . linarith [le_abs_self y]
    . linarith [neg_le_abs_self y]
}

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by {
  constructor <;> intro h
  . rcases le_or_gt 0 x with hx | hx
    . rw [abs_of_nonneg hx] at h
      constructor <;> linarith
    . rw [abs_of_neg hx] at h
      constructor <;> linarith
  . rcases le_or_gt 0 x with hx | hx
    . rw [abs_of_nonneg hx]
      exact h.right
    . rw [abs_of_neg hx]
      linarith [h.left] -- just to make it explicit
}

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl, rfl⟩ <;> linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by {
  rw [← sub_eq_zero] at h
  have h : (x + 1) * (x - 1) = 0 := by
    rw [← h]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with h | h
  . right; linarith
  . left; linarith
}

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by {
  rw [← sub_eq_zero] at h
  have h : (x + y) * (x - y) = 0 := by rw [← h]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with h | h
  . right; linarith
  . left; linarith
}

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by {
  rw [← sub_eq_zero] at h
  have h : (x + 1) * (x - 1) = 0 := by rw [← h]; noncomm_ring -- the regular laws will suffice
  -- could have proved with a bunch of rw, did it but it was so long and tedious

  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with h | h
  . right
    apply eq_neg_iff_add_eq_zero.mpr
    exact h
  . left
    apply eq_of_sub_eq_zero
    exact h
}

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by {
  rw [← sub_eq_zero] at h
  have h : (x + y) * (x - y) = 0 := by rw [← h]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with h | h
  . right
    apply add_eq_zero_iff_eq_neg.mp
    exact h
  . left
    apply eq_of_sub_eq_zero
    exact h
}

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by {
  constructor <;> intro h
  . by_cases h' : P
    . exact Or.inr $ h h'
    . exact Or.inl h'
  . intro hp
    match h with
    | Or.inl _ => contradiction
    | Or.inr _ => assumption
}
