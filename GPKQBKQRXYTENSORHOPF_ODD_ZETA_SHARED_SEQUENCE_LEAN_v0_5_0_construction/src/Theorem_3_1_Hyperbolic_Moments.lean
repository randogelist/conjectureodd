import Theorem_3_1_Hyperbolic_Weight
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-!
Polynomial moments of the positive hyperbolic density.  These identities do
not assert the remaining simple-pole identity.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

theorem integral_pow_mul_exp (d : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ y : ℝ in Ioi 0, y ^ d * Real.exp (-(a * y))) =
      (Nat.factorial d : ℝ) / a ^ (d + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (d : ℝ) + 1) (r := a) (by positivity) ha
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [show (d : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast, one_div_pow] at h
  simpa only [one_div, inv_mul_eq_div] using h

theorem integrableOn_pow_mul_exp (d : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => y ^ d * Real.exp (-(a * y))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_pow_mul_exp d ha]
  positivity

def momentTerm (k e n : ℕ) (y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 * k) *
    (y ^ (2 * k + 2 * e + 1) *
      Real.exp (-((2 * Real.pi * ((n + 1 : ℕ) : ℝ)) * y)))

def momentCoefficient (k e : ℕ) : ℝ :=
  (Nat.factorial (2 * k + 2 * e + 1) : ℝ) /
    (2 * Real.pi) ^ (2 * k + 2 * e + 2)

theorem momentTerm_integrable (k e n : ℕ) :
    IntegrableOn (momentTerm k e n) (Ioi 0) := by
  unfold momentTerm
  exact (integrableOn_pow_mul_exp _ (by positivity)).const_mul _

theorem integral_momentTerm (k e n : ℕ) :
    (∫ y : ℝ in Ioi 0, momentTerm k e n y) =
      momentCoefficient k e * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * e + 2)) := by
  unfold momentTerm momentCoefficient
  rw [integral_const_mul, integral_pow_mul_exp _ (by positivity)]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have he : 2 * k + 2 * e + 1 + 1 = 2 * k + (2 * e + 2) := by omega
  rw [he, mul_pow, pow_add, pow_add]
  field_simp
  simp only [pow_add]

theorem momentTerm_nonneg (k e n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ momentTerm k e n y := by
  unfold momentTerm
  positivity

theorem summable_integral_norm_momentTerm (k e : ℕ) :
    Summable (fun n => ∫ y : ℝ in Ioi 0, ‖momentTerm k e n y‖) := by
  have h (n : ℕ) : (∫ y : ℝ in Ioi 0, ‖momentTerm k e n y‖) =
      momentCoefficient k e * (1 / ((n + 1 : ℕ) : ℝ) ^ (2 * e + 2)) := by
    rw [← integral_momentTerm]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact Real.norm_of_nonneg (momentTerm_nonneg k e n hy.le)
  simp_rw [h]
  exact (Real.zeta_series_summable (s := 2 * e + 2) (by omega)).mul_left _

theorem integral_tsum_momentTerm (k e : ℕ) :
    (∫ y : ℝ in Ioi 0, ∑' n, momentTerm k e n y) =
      momentCoefficient k e * Real.zeta (2 * e + 2) := by
  rw [← integral_tsum_of_summable_integral_norm (momentTerm_integrable k e)
    (summable_integral_norm_momentTerm k e)]
  simp_rw [integral_momentTerm]
  rw [tsum_mul_left]
  rfl

theorem integrableOn_tsum_momentTerm (k e : ℕ) :
    IntegrableOn (fun y : ℝ => ∑' n, momentTerm k e n y) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_tsum_momentTerm]
  exact mul_ne_zero (ne_of_gt (by unfold momentCoefficient; positivity))
    (ne_of_gt (Real.zeta_pos (by omega)))


theorem monomial_density_eq_tsum (k e : ℕ) (y : ℝ) :
    y ^ (2 * e) * density k y =
      (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
        ∑' n, momentTerm k e n y := by
  unfold density
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold exponentialTerm momentTerm
  have he : 2 * k + 2 * e + 1 = 2 * e + (2 * k + 1) := by omega
  rw [he, pow_add]
  have hx : -(2 * Real.pi * y) * ((n + 1 : ℕ) : ℝ) =
      -(2 * Real.pi * ((n + 1 : ℕ) : ℝ) * y) := by ring
  rw [hx]
  ring

theorem integrableOn_monomial_density (k e : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (2 * e) * density k y) (Ioi 0) := by
  simp_rw [monomial_density_eq_tsum]
  exact (integrableOn_tsum_momentTerm k e).const_mul _

theorem integral_monomial_density (k e : ℕ) :
    (∫ y : ℝ in Ioi 0, y ^ (2 * e) * density k y) =
      (2 * (Nat.factorial (2 * k + 2 * e + 1) : ℝ) /
        ((Nat.factorial (2 * k) : ℝ) * (2 * Real.pi) ^ (2 * e + 2))) *
          Real.zeta (2 * e + 2) := by
  simp_rw [monomial_density_eq_tsum]
  rw [integral_const_mul, integral_tsum_momentTerm]
  unfold momentCoefficient
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
  rw [show 2 * k + 2 * e + 2 = 2 * k + (2 * e + 2) by omega, pow_add]
  field_simp


theorem zeta_even_bernoulli (e : ℕ) :
    Real.zeta (2 * e + 2) =
      (-1 : ℝ) ^ e * (2 * Real.pi) ^ (2 * e + 2) *
        (bernoulli (2 * e + 2) : ℝ) /
          (2 * (Nat.factorial (2 * e + 2) : ℝ)) := by
  have hs := hasSum_zeta_nat (k := e + 1) (by omega)
  have hz : Real.zeta (2 * e + 2) =
      ∑' n : ℕ, 1 / (n : ℝ) ^ (2 * (e + 1)) := by
    rw [hs.summable.tsum_eq_zero_add]
    simp only [Nat.cast_zero, show 2 * (e + 1) ≠ 0 by omega, ne_eq, not_false_eq_true,
      zero_pow, div_zero, zero_add]
    congr 1
  rw [hz, hs.tsum_eq]
  have h1 : 2 * (e + 1) = 2 * e + 2 := by omega
  have h2 : 2 * (e + 1) - 1 = 2 * e + 1 := by omega
  rw [h2, h1, show e + 1 + 1 = e + 2 by omega,
    pow_add (-1 : ℝ), pow_succ (2 : ℝ) (2 * e), mul_pow]
  norm_num
  rw [show 2 * e + 2 = (2 * e + 1) + 1 by omega, pow_succ, pow_succ]
  ring

theorem integral_monomial_density_eq_monomialMoment (k e : ℕ) :
    (∫ y : ℝ in Ioi 0, y ^ (2 * e) * density k y) =
      (Real.monomialMoment k e : ℝ) := by
  rw [integral_monomial_density, zeta_even_bernoulli]
  unfold Real.monomialMoment
  push_cast
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
  have hg : (Nat.factorial (2 * e + 2) : ℝ) ≠ 0 := by positivity
  rw [show 2 * e + 2 * k + 1 = 2 * k + 2 * e + 1 by omega]
  field_simp

end ManuscriptChain.Hyperbolic

#print axioms ManuscriptChain.Hyperbolic.integral_pow_mul_exp
#print axioms ManuscriptChain.Hyperbolic.integral_tsum_momentTerm
#print axioms ManuscriptChain.Hyperbolic.integrableOn_tsum_momentTerm

#print axioms ManuscriptChain.Hyperbolic.integrableOn_monomial_density
#print axioms ManuscriptChain.Hyperbolic.integral_monomial_density

#print axioms ManuscriptChain.Hyperbolic.integral_monomial_density_eq_monomialMoment
