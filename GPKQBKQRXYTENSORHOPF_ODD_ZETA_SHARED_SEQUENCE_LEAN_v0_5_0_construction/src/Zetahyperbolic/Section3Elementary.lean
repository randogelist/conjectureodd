import Zetahyperbolic.Foundations

/-!
# Section 3: exact elementary positivity lemmas

This module starts the Section 3 work independently of the still-open
finite-product derivative proof in Section 2. The Fekete factorization
positivity theorem is the elementary positivity component of manuscript
Theorem 3.9. The denominator positivity lemma is a reusable input for
positive Gram-integral arguments.
-/

namespace Zetahyperbolic

/-- The five factored Fekete polynomials used for the real-character
extensions in manuscript Theorem 3.9 are strictly positive on (0,1). -/
theorem fekete_polynomial_positivity_basic {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    0 < z * (1 - z) ∧
    0 < z * (1 - z ^ 2) ∧
    0 < z * (1 - z) ^ 2 * (1 + z) ∧
    0 < z * (1 - z ^ 2) * (1 - z ^ 4) ∧
    0 < z * (1 + z ^ 2) * (1 - z ^ 4) := by
  have h1 : 0 < 1 - z := sub_pos.mpr hz1
  have h2 : 0 < 1 + z := by linarith
  have h3 : 0 < 1 - z ^ 2 := by nlinarith
  have h4 : 0 < 1 + z ^ 2 := by positivity
  have h5 : 0 < 1 - z ^ 4 := by nlinarith
  refine ⟨mul_pos hz0 h1, mul_pos hz0 h3, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity

/-- The denominator polynomial D_m(x) = product over j=1..m of (x+j^2)
is positive for every positive real x. This is the elementary denominator-sign
input for the positive Gram integrals in Section 3. -/
theorem denominatorPolynomial_eval_pos (m : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < Polynomial.eval x
      ((denominatorPolynomial m).map (algebraMap ℚ ℝ)) := by
  classical
  unfold denominatorPolynomial
  rw [Polynomial.eval_map, Polynomial.eval₂_finsetProd]
  apply Finset.prod_pos
  intro j hj
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
  positivity

/-- The full denominator product is at least one on the positive axis.
This coarse lower bound is useful when estimating the rational Gram weight. -/
theorem denominatorPolynomial_eval_ge_one (m : ℕ) {x : ℝ} (hx : 0 < x) :
    1 ≤ Polynomial.eval x
      ((denominatorPolynomial m).map (algebraMap ℚ ℝ)) := by
  classical
  unfold denominatorPolynomial
  rw [Polynomial.eval_map, Polynomial.eval₂_finsetProd]
  apply Finset.one_le_prod
  intro j hj
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hjSq : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((j : ℝ) - 1)]
  push_cast
  linarith

/-- The tail denominator product is at least one on the positive axis.
The estimate is uniform in the tail interval and complements the full-product
bound above. -/
theorem tailPolynomial_eval_ge_one (N K : ℕ) {x : ℝ} (hx : 0 < x) :
    1 ≤ Polynomial.eval x
      ((tailPolynomial N K).map (algebraMap ℚ ℝ)) := by
  classical
  unfold tailPolynomial
  rw [Polynomial.eval_map, Polynomial.eval₂_finsetProd]
  apply Finset.one_le_prod
  intro j hj
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
  have hjN : N + 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hj1 : 1 ≤ j := by omega
  have hj1R : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hjSq : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((j : ℝ) - 1)]
  push_cast
  linarith

/-- The tail denominator is strictly positive on the positive real axis.
This is the tail-product analogue of denominatorPolynomial_eval_pos and is
used in positive Gram-integral estimates. -/
theorem tailPolynomial_eval_pos (N K : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < Polynomial.eval x
      ((tailPolynomial N K).map (algebraMap ℚ ℝ)) := by
  classical
  unfold tailPolynomial
  rw [Polynomial.eval_map, Polynomial.eval₂_finsetProd]
  apply Finset.prod_pos
  intro j hj
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
  positivity

end Zetahyperbolic
