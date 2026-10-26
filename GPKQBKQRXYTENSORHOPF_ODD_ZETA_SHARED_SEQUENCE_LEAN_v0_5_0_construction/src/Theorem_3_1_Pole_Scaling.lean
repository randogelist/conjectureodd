import Theorem_3_1_Hyperbolic_Moments
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! A direct series-and-scaling reduction of the actual simple-pole integral.
No Hermite formula or pole-moment identity is assumed here. -/
noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

def poleTerm (k n : ℕ) (a y : ℝ) : ℝ :=
  momentTerm k 0 n y / (y ^ 2 + a ^ 2)

def scaledPoleTerm (k n : ℕ) (a t : ℝ) : ℝ :=
  (t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t))) /
    (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2)

theorem poleTerm_nonneg (k n : ℕ) {a y : ℝ} (hy : 0 ≤ y) :
    0 ≤ poleTerm k n a y := by
  unfold poleTerm
  exact div_nonneg (momentTerm_nonneg _ _ _ hy) (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem norm_poleTerm_le (k n : ℕ) {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    ‖poleTerm k n a y‖ ≤ (1 / a ^ 2) * momentTerm k 0 n y := by
  rw [Real.norm_of_nonneg (poleTerm_nonneg k n hy)]
  unfold poleTerm
  have h := div_le_div_of_nonneg_left (momentTerm_nonneg k 0 n hy)
    (show 0 < a ^ 2 by positivity) (show a ^ 2 ≤ y ^ 2 + a ^ 2 by nlinarith [sq_nonneg y])
  simpa [div_eq_mul_inv, mul_comm] using h

theorem poleTerm_integrable (k n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (poleTerm k n a) (Ioi 0) := by
  apply ((momentTerm_integrable k 0 n).const_mul (1 / a ^ 2)).mono'
  · exact (show Measurable (poleTerm k n a) by
      unfold poleTerm momentTerm
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact norm_poleTerm_le k n ha hy.le

theorem summable_integral_norm_poleTerm (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => ∫ y in Ioi (0 : ℝ), ‖poleTerm k n a y‖) := by
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
    ((summable_integral_norm_momentTerm k 0).mul_left (1 / a ^ 2))
  intro n
  rw [← integral_const_mul]
  apply integral_mono_ae (poleTerm_integrable k n ha).norm
    ((momentTerm_integrable k 0 n).norm.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_of_nonneg (momentTerm_nonneg k 0 n hy.le)]
  exact norm_poleTerm_le k n ha hy.le

theorem scaledPoleTerm_nonneg (k n : ℕ) {a t : ℝ} (ht : 0 ≤ t) :
    0 ≤ scaledPoleTerm k n a t := by
  unfold scaledPoleTerm
  positivity

theorem norm_scaledPoleTerm_le (k n : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    ‖scaledPoleTerm k n a t‖ ≤
      (1 / (a * ((n + 1 : ℕ) : ℝ)) ^ 2) *
        (t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t))) := by
  rw [Real.norm_of_nonneg (scaledPoleTerm_nonneg k n ht)]
  unfold scaledPoleTerm
  have h := div_le_div_of_nonneg_left
    (show 0 ≤ t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t)) by positivity)
    (show 0 < (a * ((n + 1 : ℕ) : ℝ)) ^ 2 by positivity)
    (show (a * ((n + 1 : ℕ) : ℝ)) ^ 2 ≤
      t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2 by nlinarith [sq_nonneg t])
  simpa [div_eq_mul_inv, mul_comm] using h

theorem scaledPoleTerm_integrable (k n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (scaledPoleTerm k n a) (Ioi 0) := by
  apply ((integrableOn_pow_mul_exp (2 * k + 1) (by positivity : 0 < 2 * Real.pi)).const_mul
    (1 / (a * ((n + 1 : ℕ) : ℝ)) ^ 2)).mono'
  · exact (show Measurable (scaledPoleTerm k n a) by
      unfold scaledPoleTerm
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_scaledPoleTerm_le k n ha ht.le

theorem summable_scaledPole_bound (a : ℝ) :
    Summable (fun n : ℕ => 1 / (a * ((n + 1 : ℕ) : ℝ)) ^ 2) := by
  simp_rw [mul_pow, one_div, mul_inv]
  simpa only [one_div] using
    (Real.zeta_series_summable (s := 2) (by omega)).mul_left ((a ^ 2)⁻¹)

theorem summable_integral_norm_scaledPoleTerm (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖scaledPoleTerm k n a t‖) := by
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
    ((summable_scaledPole_bound a).mul_right
      ((Nat.factorial (2 * k + 1) : ℝ) / (2 * Real.pi) ^ (2 * k + 2)))
  intro n
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by omega, ← integral_pow_mul_exp (2 * k + 1)
    (by positivity : 0 < 2 * Real.pi), ← integral_const_mul]
  apply integral_mono_ae (scaledPoleTerm_integrable k n ha).norm
    ((integrableOn_pow_mul_exp (2 * k + 1) (by positivity : 0 < 2 * Real.pi)).const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_scaledPoleTerm_le k n ha ht.le

theorem poleTerm_eq_scaled (k n : ℕ) {a : ℝ} (ha : 0 < a) (y : ℝ) :
    poleTerm k n a y = ((n + 1 : ℕ) : ℝ) *
      scaledPoleTerm k n a (((n + 1 : ℕ) : ℝ) * y) := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hd : y ^ 2 + a ^ 2 ≠ 0 := by positivity
  unfold poleTerm momentTerm scaledPoleTerm
  simp only [Nat.mul_zero, Nat.add_zero, mul_pow, pow_add, pow_one]
  have he : -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y) =
      -(2 * Real.pi * (((n + 1 : ℕ) : ℝ) * y)) := by ring
  rw [he]
  field_simp

theorem integral_poleTerm_eq_scaled (k n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ y in Ioi (0 : ℝ), poleTerm k n a y) =
      ∫ t in Ioi (0 : ℝ), scaledPoleTerm k n a t := by
  simp_rw [poleTerm_eq_scaled k n ha]
  rw [integral_const_mul, integral_comp_mul_left_Ioi _ 0 (by positivity)]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [mul_zero, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]

theorem density_div_quadratic_eq_tsum (k : ℕ) (a y : ℝ) :
    density k y / (y ^ 2 + a ^ 2) =
      (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
        ∑' n, poleTerm k n a y := by
  have h := monomial_density_eq_tsum k 0 y
  simp only [Nat.mul_zero, pow_zero, one_mul] at h
  rw [h, mul_div_assoc, ← tsum_div_const]
  rfl

theorem tsum_scaledPoleTerm (k : ℕ) (a t : ℝ) :
    (∑' n, scaledPoleTerm k n a t) =
      (t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t))) *
        ∑' n : ℕ, 1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2) := by
  simp only [scaledPoleTerm, div_eq_mul_inv, one_mul]
  rw [tsum_mul_left]

/-- The actual density-pole integral is reduced to an elementary resolvent sum. -/
theorem integral_density_div_quadratic (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ y in Ioi (0 : ℝ), density k y / (y ^ 2 + a ^ 2)) =
      (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
        ∫ t in Ioi (0 : ℝ),
          (t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t))) *
            ∑' n : ℕ, 1 / (t ^ 2 + (a * ((n + 1 : ℕ) : ℝ)) ^ 2) := by
  simp_rw [density_div_quadratic_eq_tsum]
  rw [integral_const_mul,
    ← integral_tsum_of_summable_integral_norm (fun n => poleTerm_integrable k n ha)
      (summable_integral_norm_poleTerm k ha)]
  simp_rw [integral_poleTerm_eq_scaled k _ ha]
  rw [integral_tsum_of_summable_integral_norm (fun n => scaledPoleTerm_integrable k n ha)
    (summable_integral_norm_scaledPoleTerm k ha)]
  simp_rw [tsum_scaledPoleTerm]

end ManuscriptChain.Hyperbolic

#print axioms ManuscriptChain.Hyperbolic.integral_density_div_quadratic
