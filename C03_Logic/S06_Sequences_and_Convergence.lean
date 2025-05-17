import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  simp -- same as below
  -- rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by {
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt

  intro n nge
  have hsn : |s n - a| < ε / 2 := hs _ (le_of_max_le_left nge)
  have htn : |t n - b| < ε / 2 := ht _ (le_of_max_le_right nge)
  have hstn : |s n - a| + |t n - b| < ε := by
    convert add_lt_add hsn htn
    norm_num
  have : |s n + t n - (a + b)| ≤ |s n - a| + |t n - b| := by
    calc |s n + t n - (a + b)| = |s n - a + (t n - b)| := by congr; ring
    _ ≤ |s n - a| + |t n - b| := by apply abs_add _ _
  exact lt_of_le_of_lt this hstn
}

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by {
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    . rw [h]
      ring

  . have acpos : 0 < |c| := abs_pos.mpr h
    intro ε εpos
    have εcpos : 0 < ε / |c| := div_pos εpos acpos
    obtain ⟨Ns, hs⟩ := cs _ εcpos
    use Ns
    intro n nge
    specialize hs _ nge
    dsimp
    calc
      |c * s n - c * a| = |c| * |s n - a| := by rw [← mul_sub, abs_mul]
      _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left hs acpos
      _ = ε := by rw [mul_div_cancel₀ ε (ne_of_lt acpos).symm]
}

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  specialize h _ hn
  have : |s n| - |a| ≤ |s n - a| := by apply abs_sub_abs_le_abs_sub
  apply lt_add_of_sub_left_lt
  calc
    |s n| - |a| ≤ |s n - a| := this
    _ < 1 := h

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n nge
  specialize h₀ _ (le_of_max_le_left nge)
  specialize h₁ _ (le_of_max_le_right nge)
  simp at h₁
  simp
  calc
    |s n * t n| = |s n| * |t n| := by rw [abs_mul]
    _ ≤ B * |t n| := by apply mul_le_mul (le_of_lt h₀) (by rfl) (abs_nonneg _) (le_of_lt Bpos)
    _ < B * (ε / B) := by apply (mul_lt_mul_left Bpos).mpr h₁
    _ = ε := by rw [mul_div_cancel₀ ε (ne_of_lt Bpos).symm]

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert this using 1
  · ext; ring
  ring

theorem my_convergesTo_unique {s : ℕ → ℝ} {a b : ℝ} (sa : ConvergesTo s a) (sb : ConvergesTo s b) : a = b := by {
  by_contra ab_ne
  have h : |a - b| / 2 > 0 := half_pos (abs_sub_pos.mpr ab_ne)
  obtain ⟨N₀, h₀⟩ := sa _ h
  obtain ⟨N₁, h₁⟩ := sb _ h
  let n := max N₀ N₁
  have nge₀ : n ≥ N₀ := by apply le_max_left
  have nge₁ : n ≥ N₁ := by apply le_max_right
  specialize h₀ _ nge₀
  specialize h₁ _ nge₁ 
  have : |a - b| < |a - b| :=
    calc
      |a - b| = |a - s n + (s n - b)| := by congr; ring
      _ ≤ |s n - a| + |s n - b| := by rw [abs_sub_comm (s n)]; apply abs_add
      _ < (|a - b| / 2) + (|a - b| / 2) := add_lt_add h₀ h₁
      _ = |a - b| := by apply add_halves
  apply lt_irrefl _ this
}

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := (abs_sub_pos.mpr abne)
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (by apply le_max_left)
  have absb : |s N - b| < ε := hNb N (by apply le_max_right)
  have : |a - b| < |a - b| := calc
    |a - b| = |a - s N + (s N - b)| := by congr; ring
    _ ≤ |s N - a| + |s N - b| := by rw [abs_sub_comm (s N)]; apply abs_add
    _ < ε + ε := add_lt_add absa absb
    _ = 2 * (|a - b| / 2) := by rw [← mul_two, mul_comm]
    _ = |a - b| := by linarith
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end

