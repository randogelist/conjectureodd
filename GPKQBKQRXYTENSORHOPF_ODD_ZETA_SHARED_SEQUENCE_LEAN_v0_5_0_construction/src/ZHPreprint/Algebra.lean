import Theorem_4_1_Leading_Coefficient_Gap
import Theorem_2_5_Weight_Change

/-!
# Concrete ZH algebra for the primitive-growth preprint

Every object below is defined from the pinned repository's actual rational
moment pencil. There are no new axioms, abstract polynomial selectors, or
assumed normalization/positivity/denominator-transfer declarations.

The profile is t = n + 1, m = 3, N = 3t, K = 30t, h = 27t.
The statements in this file are proposed Lean proofs until the requested
native Lean 4.33.0 build and axiom audit have completed.
-/

noncomputable section
open scoped BigOperators

namespace ZHPreprint

abbrev parameters (k n : ℕ) : ManuscriptChain.Real.Parameters :=
  ManuscriptChain.GeneralIrrationality.affineFamily k n

def primitive (k n : ℕ) : Polynomial ℤ :=
  ManuscriptChain.GeneralIrrationality.primitivePolynomial (parameters k n)

def value (k n : ℕ) : ℝ :=
  ManuscriptChain.RealTransfer.evalReal (primitive k n)
    (ManuscriptChain.Real.zeta (2 * k + 1))

def leading (k n : ℕ) : ℝ :=
  ManuscriptChain.LeadingCoefficientGap.leadingSize (parameters k n)

def gram (k n : ℕ) : ℝ :=
  (ManuscriptChain.Real.gram (parameters k n)
    (ManuscriptChain.Real.zeta (2 * k + 1))).det

def derivativeMagnitude (k n : ℕ) : ℝ :=
  |(ManuscriptChain.Real.derivativeMatrix (parameters k n)).det|

theorem parameters_admissible (k n : ℕ) (hk : 0 < k) :
    ManuscriptChain.Real.Admissible (parameters k n) :=
  ManuscriptChain.GeneralIrrationality.affineFamily_admissible k hk n

theorem primitive_degree (k n : ℕ) :
    (primitive k n).natDegree = 27 * (n + 1) := by
  rw [primitive,
    ManuscriptChain.GeneralIrrationality.primitivePolynomial_natDegree]
  exact ManuscriptChain.GeneralIrrationality.affineFamily_h k n

theorem value_pos (k n : ℕ) (hk : 0 < k) : 0 < value k n := by
  exact ManuscriptChain.GeneralIrrationality.primitivePolynomial_eval_pos
    (parameters k n) (parameters_admissible k n hk)

theorem leading_ge_one (k n : ℕ) : 1 ≤ leading k n :=
  ManuscriptChain.LeadingCoefficientGap.leadingSize_ge_one (parameters k n)

theorem leading_pos (k n : ℕ) : 0 < leading k n :=
  lt_of_lt_of_le (by norm_num) (leading_ge_one k n)

theorem gram_pos (k n : ℕ) (hk : 0 < k) : 0 < gram k n := by
  exact (ManuscriptChain.GRAM_POSITIVE
    (parameters k n) (parameters_admissible k n hk)).det_pos

theorem derivativeMagnitude_pos (k n : ℕ) :
    0 < derivativeMagnitude k n :=
  abs_pos.mpr (ManuscriptChain.General.derivative_nonsingular (parameters k n))

/-- The raw slope determinant cannot decrease in magnitude as the odd-weight
index increases from 2 to k. The comparison factor is the actual finite pole
product; no asymptotic input is used. -/
theorem derivativeMagnitude_mono (k n : ℕ) (hk : 2 ≤ k) :
    derivativeMagnitude 2 n ≤ derivativeMagnitude k n := by
  let p := parameters 2 n
  let F : ℚ := ∏ a : Fin p.h,
    (ManuscriptChain.PoleDiagonalization.poleIndex p a : ℚ) ^ (2 * (k - 2))
  have hF : (1 : ℚ) ≤ F := by
    dsimp [F]
    apply Finset.one_le_prod
    intro a _
    have hnat : 1 ≤ ManuscriptChain.PoleDiagonalization.poleIndex p a := by
      have h := ManuscriptChain.PoleDiagonalization.poleIndex_pos p a
      omega
    have hrat : (1 : ℚ) ≤
        (ManuscriptChain.PoleDiagonalization.poleIndex p a : ℚ) := by
      exact_mod_cast hnat
    exact one_le_pow₀ hrat
  have hdet :
      (ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
        (parameters k n)).det =
      (ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
        (parameters 2 n)).det * F := by
    have h :=
      ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix_det_reweight_add
        p 2 (k - 2)
    have hindex : 2 + (k - 2) = k := by omega
    rw [hindex] at h
    exact h
  have hmono :
      |(ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
        (parameters 2 n)).det| ≤
      |(ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
        (parameters k n)).det| := by
    rw [hdet, abs_mul, abs_of_nonneg (le_trans (by norm_num) hF)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hF
        (abs_nonneg (ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
          (parameters 2 n)).det)
  have hcast :
      |((ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
        (parameters 2 n)).det : ℝ)| ≤
      |((ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix
        (parameters k n)).det : ℝ)| := by
    exact_mod_cast hmono
  simp only [Rat.cast_det] at hcast
  exact hcast

theorem value_eq_leading_mul_gram_div (k n : ℕ) :
    value k n = leading k n * gram k n / derivativeMagnitude k n := by
  have h := ManuscriptChain.LeadingCoefficientGap.primitivePolynomial_eval_eq
    (parameters k n)
  change value k n = leading k n * (gram k n / derivativeMagnitude k n) at h
  simpa only [mul_div_assoc] using h

theorem value_mul_derivativeMagnitude (k n : ℕ) :
    value k n * derivativeMagnitude k n = leading k n * gram k n := by
  rw [value_eq_leading_mul_gram_div,
    div_mul_cancel₀ _ (ne_of_gt (derivativeMagnitude_pos k n))]

/-- Actual leading and Gram comparisons imply a primitive-value comparison.
All three functions are the concrete ZH family above. -/
theorem value_upper_of_leading_gram_bounds
    (k n : ℕ) (hk : 2 ≤ k) (a b : ℝ)
    (hleading : leading k n ≤ Real.exp a * leading 2 n)
    (hgram : gram k n ≤ Real.exp b * gram 2 n) :
    value k n ≤ value 2 n * Real.exp (a + b) := by
  have hkpos : 0 < k := by omega
  have hmul :
      value k n * derivativeMagnitude 2 n ≤
        (value 2 n * Real.exp (a + b)) * derivativeMagnitude 2 n := by
    calc
      value k n * derivativeMagnitude 2 n ≤
          value k n * derivativeMagnitude k n :=
        mul_le_mul_of_nonneg_left (derivativeMagnitude_mono k n hk)
          (value_pos k n hkpos).le
      _ = leading k n * gram k n := value_mul_derivativeMagnitude k n
      _ ≤ (Real.exp a * leading 2 n) * (Real.exp b * gram 2 n) :=
        mul_le_mul hleading hgram (gram_pos k n hkpos).le
          (mul_nonneg (Real.exp_pos a).le (leading_pos 2 n).le)
      _ = (leading 2 n * gram 2 n) * (Real.exp a * Real.exp b) := by ring
      _ = (value 2 n * derivativeMagnitude 2 n) *
          (Real.exp a * Real.exp b) := by
        rw [value_mul_derivativeMagnitude]
      _ = (value 2 n * Real.exp (a + b)) * derivativeMagnitude 2 n := by
        rw [Real.exp_add]
        ring
  by_contra hnot
  have hgt : value 2 n * Real.exp (a + b) < value k n :=
    lt_of_not_ge hnot
  exact (not_lt_of_ge hmul)
    (mul_lt_mul_of_pos_right hgt (derivativeMagnitude_pos 2 n))

end ZHPreprint

#print axioms ZHPreprint.primitive_degree
#print axioms ZHPreprint.value_pos
#print axioms ZHPreprint.derivativeMagnitude_mono
#print axioms ZHPreprint.value_eq_leading_mul_gram_div
#print axioms ZHPreprint.value_upper_of_leading_gram_bounds
