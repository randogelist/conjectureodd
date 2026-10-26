import MAIN_CHAIN_IRRATIONALITY

/-!
# Exact leading-coefficient and determinant-ratio arithmetic frontier

For the canonical primitive integer polynomial P_p, let Lambda_p be the
absolute value of its integer leading coefficient, and let R_p be the
positive Gram determinant divided by the absolute derivative determinant.
The exact identity P_p(zeta(2k+1)) = Lambda_p * R_p eliminates a freely
chosen normalization scalar. Eventual bounds with a strict exponential-rate
gap imply the existing normalized decay condition. Those bounds remain inputs.
-/

noncomputable section
open Polynomial

namespace ManuscriptChain.LeadingCoefficientGap
open GeneralIrrationality

/-- Lambda_p: the size of the canonical primitive integer leading coefficient. -/
def leadingSize (p : Real.Parameters) : ℝ :=
  |((primitivePolynomial p).leadingCoeff : ℝ)|

/-- R_p: the actual Gram determinant divided by the absolute slope determinant. -/
def determinantRatio (p : Real.Parameters) : ℝ :=
  (Real.gram p (Real.zeta p.weight)).det / |(Real.derivativeMatrix p).det|

theorem primitive_leadingCoeff_real (p : Real.Parameters) :
    ((primitivePolynomial p).leadingCoeff : ℝ) =
      ((normalization p).scale : ℝ) * (Real.derivativeMatrix p).det := by
  have h := congrArg Polynomial.leadingCoeff (normalization p).identity
  rw [Polynomial.leadingCoeff_map_of_injective
      (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective),
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    PoleDiagonalization.delta_leadingCoeff] at h
  have hreal : ((primitivePolynomial p).leadingCoeff : ℝ) =
      ((normalization p).scale : ℝ) *
        ((PoleDiagonalization.rationalDerivativeMatrix p).det : ℝ) := by
    exact_mod_cast h
  rw [Rat.cast_det] at hreal
  exact hreal

theorem leadingSize_eq_scale_mul_abs_det (p : Real.Parameters) :
    leadingSize p = ((normalization p).scale : ℝ) *
      |(Real.derivativeMatrix p).det| := by
  unfold leadingSize
  rw [primitive_leadingCoeff_real, abs_mul,
    abs_of_pos (show (0 : ℝ) < ((normalization p).scale : ℝ) by
      exact_mod_cast (normalization p).scale_pos)]

theorem leadingSize_ge_one (p : Real.Parameters) : 1 ≤ leadingSize p := by
  have hn : (primitivePolynomial p).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (primitivePolynomial_isPrimitive p).ne_zero
  have hp : (0 : ℤ) < |(primitivePolynomial p).leadingCoeff| := abs_pos.mpr hn
  have hle : (1 : ℤ) ≤ |(primitivePolynomial p).leadingCoeff| := by omega
  unfold leadingSize
  exact_mod_cast hle

theorem determinantRatio_pos (p : Real.Parameters) (hp : Real.Admissible p) :
    0 < determinantRatio p :=
  div_pos (GRAM_POSITIVE p hp).det_pos
    (abs_pos.mpr (General.derivative_nonsingular p))

/-- Exact factorization of the actual normalized value into two fixed scalars. -/
theorem primitivePolynomial_eval_eq (p : Real.Parameters) :
    RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight) =
      leadingSize p * determinantRatio p := by
  rw [primitivePolynomial_eval, Real.delta_eval_eq_det_gram,
    leadingSize_eq_scale_mul_abs_det]
  unfold determinantRatio
  have hne : |(Real.derivativeMatrix p).det| ≠ 0 :=
    ne_of_gt (abs_pos.mpr (General.derivative_nonsingular p))
  field_simp

/-- A strict gap between the leading-coefficient growth and determinant-ratio
decay rates supplies the one normalized quadratic decay estimate. -/
theorem normalizedQuadraticDecay_of_gap (p : ℕ → Real.Parameters)
    (A B : ℝ) (hAB : A < B) (n₀ : ℕ)
    (leading : ∀ n, n₀ ≤ n → leadingSize (p n) ≤
      _root_.Real.exp (A * ((p n).K : ℝ) ^ 2))
    (ratio : ∀ n, n₀ ≤ n → determinantRatio (p n) ≤
      _root_.Real.exp (-B * ((p n).K : ℝ) ^ 2)) :
    NormalizedQuadraticDecay p := by
  refine ⟨B - A, sub_pos.mpr hAB, n₀, ?_⟩
  intro n hn
  rw [primitivePolynomial_eval_eq]
  calc
    leadingSize (p n) * determinantRatio (p n) ≤
        leadingSize (p n) * _root_.Real.exp (-B * ((p n).K : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (ratio n hn)
        ((show (0 : ℝ) ≤ 1 by norm_num).trans (leadingSize_ge_one (p n)))
    _ ≤ _root_.Real.exp (A * ((p n).K : ℝ) ^ 2) *
        _root_.Real.exp (-B * ((p n).K : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (leading n hn) (_root_.Real.exp_pos _).le
    _ = _root_.Real.exp (-(B - A) * ((p n).K : ℝ) ^ 2) := by
      rw [← _root_.Real.exp_add]
      congr 1
      ring

/-- The strict-gap criterion applied to an actual unbounded fixed-weight family.
No spectral growth or freely chosen normalization hypothesis is required. -/
theorem irrational_riemannZeta_of_gap (k : ℕ) (hk : 0 < k)
    (p : ℕ → Real.Parameters) (hp : ∀ n, Real.Admissible (p n))
    (hweight : ∀ n, (p n).k = k) (hunbounded : UnboundedOnTails p)
    (A B : ℝ) (hAB : A < B) (n₀ : ℕ)
    (leading : ∀ n, n₀ ≤ n → leadingSize (p n) ≤
      _root_.Real.exp (A * ((p n).K : ℝ) ^ 2))
    (ratio : ∀ n, n₀ ≤ n → determinantRatio (p n) ≤
      _root_.Real.exp (-B * ((p n).K : ℝ) ^ 2)) :
    Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re :=
  irrational_riemannZeta_of_normalized_decay k hk p hp hweight hunbounded
    (normalizedQuadraticDecay_of_gap p A B hAB n₀ leading ratio)

end ManuscriptChain.LeadingCoefficientGap

#print axioms ManuscriptChain.LeadingCoefficientGap.primitive_leadingCoeff_real
#print axioms ManuscriptChain.LeadingCoefficientGap.leadingSize_ge_one
#print axioms ManuscriptChain.LeadingCoefficientGap.determinantRatio_pos
#print axioms ManuscriptChain.LeadingCoefficientGap.primitivePolynomial_eval_eq
#print axioms ManuscriptChain.LeadingCoefficientGap.normalizedQuadraticDecay_of_gap
#print axioms ManuscriptChain.LeadingCoefficientGap.irrational_riemannZeta_of_gap
