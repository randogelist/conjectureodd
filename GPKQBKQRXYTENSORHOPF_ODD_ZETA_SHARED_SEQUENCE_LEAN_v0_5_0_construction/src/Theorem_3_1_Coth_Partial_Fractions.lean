import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Tactic

/-! The real positive-axis partial-fraction identity obtained from cotangent.
This evaluates the pole sum used in the analytic change-of-variables proof. -/

noncomputable section
open scoped BigOperators

namespace ManuscriptChain.Hyperbolic

theorem summable_coth_terms {t a : ℝ} (_ht : 0 < t) (ha : 0 < a) :
    Summable (fun n : ℕ => 1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)) := by
  have hs : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr (_root_.Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply (hs.mul_left (1 / a ^ 2)).of_nonneg_of_le (fun n => by positivity)
  intro n
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2) ≤
        1 / (a * ((n + 1 : ℕ) : ℝ)) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [sq_nonneg t]
    _ = (1 / a ^ 2) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      rw [mul_pow, one_div_mul_one_div]

private theorem cot_term_imaginary (x r : ℝ) (hx : 0 < x) :
    1 / ((x : ℂ) * Complex.I - r) + 1 / ((x : ℂ) * Complex.I + r) =
      (-2 * (x : ℂ) * Complex.I) * ((1 / (x ^ 2 + r ^ 2) : ℝ) : ℂ) := by
  have hm : (x : ℂ) * Complex.I - r ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simpa using (hx.ne' (by simpa using hh))
  have hp : (x : ℂ) * Complex.I + r ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simpa using (hx.ne' (by simpa using hh))
  have hd : (x : ℂ) ^ 2 + (r : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < x ^ 2 + r ^ 2 by positivity))
  push_cast
  field_simp
  ring_nf
  simp

private theorem coth_partial_fractions_one {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, 1 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2)) =
      Real.pi / x * (1 / 2 + 1 / (Real.exp (2 * Real.pi * x) - 1)) -
        1 / (2 * x ^ 2) := by
  have hz : (x : ℂ) * Complex.I ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hh := congrArg Complex.im hn
    have : x = 0 := by simpa using hh.symm
    exact hx.ne' this
  have hcot := cot_series_rep' hz
  have ht : (∑' n : ℕ,
      (1 / ((x : ℂ) * Complex.I - (n + 1)) +
       1 / ((x : ℂ) * Complex.I + (n + 1)))) =
      (-2 * (x : ℂ) * Complex.I) *
        ((∑' n : ℕ, 1 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simpa only [Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one] using cot_term_imaginary x (n + 1) hx
  rw [ht, Complex.cot_pi_eq_exp_ratio] at hcot
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((x : ℂ) * Complex.I) =
      ((-(2 * Real.pi * x) : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (2 * (Real.pi : ℂ) * (x : ℂ)) * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [he, ← Complex.ofReal_exp] at hcot
  generalize hq : Real.exp (-(2 * Real.pi * x)) = q at hcot
  have hi := congrArg Complex.im hcot
  simp [Complex.div_im, Complex.normSq, Complex.mul_re, Complex.mul_im] at hi
  have hx0 : x ≠ 0 := hx.ne'
  have hq1 : 1 - q ≠ 0 := by
    apply ne_of_gt
    rw [← hq]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (by positivity)))
  have hform : (∑' n : ℕ, 1 / (x ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2)) =
      Real.pi / (2 * x) * ((q + 1) / (1 - q)) - 1 / (2 * x ^ 2) := by
    simp only [Nat.cast_add, Nat.cast_one] at hi ⊢
    field_simp at hi ⊢
    linarith [hi]
  rw [hform, ← hq, Real.exp_neg]
  have he0 : Real.exp (2 * Real.pi * x) ≠ 0 := Real.exp_ne_zero _
  have he1 : Real.exp (2 * Real.pi * x) - 1 ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  generalize hE : Real.exp (2 * Real.pi * x) = E at he0 he1 ⊢
  field_simp [he0, he1]
  ring

theorem coth_partial_fractions {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    (∑' n : ℕ, 1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)) =
      Real.pi / (a * t) * (1 / 2 + 1 / (Real.exp (2 * Real.pi * t / a) - 1)) -
        1 / (2 * t ^ 2) := by
  have ha0 := ha.ne'
  have ht0 := ht.ne'
  have hscale : (∑' n : ℕ, 1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)) =
      (1 / a ^ 2) * ∑' n : ℕ, 1 / ((t / a) ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    field_simp
  rw [hscale, coth_partial_fractions_one (div_pos ht ha)]
  rw [show 2 * Real.pi * (t / a) = 2 * Real.pi * t / a by ring]
  field_simp

end ManuscriptChain.Hyperbolic

#print axioms ManuscriptChain.Hyperbolic.coth_partial_fractions
#print axioms ManuscriptChain.Hyperbolic.summable_coth_terms
