import Definition_2_1_Order_s_Rational_Moment_Functional
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The explicit positive density in equation (3.1)

This file constructs the manuscript's exponential-series density and proves
its convergence and strict positivity on the positive half-line. These facts
are unconditional. They do not identify its simple-pole integrals with the
manuscript's rational moment functional; that analytic identity is separate.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ManuscriptChain.Hyperbolic

def exponentialTerm (k n : ℕ) (y : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 * k) *
    Real.exp (-(2 * Real.pi * y) * ((n + 1 : ℕ) : ℝ))

def density (k : ℕ) (y : ℝ) : ℝ :=
  (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
    y ^ (2 * k + 1) * ∑' n : ℕ, exponentialTerm k n y

theorem exponentialTerm_pos (k n : ℕ) (y : ℝ) :
    0 < exponentialTerm k n y := by
  unfold exponentialTerm
  positivity

theorem summable_exponentialTerm (k : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => exponentialTerm k n y) := by
  exact (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul (2 * k)
      (show 0 < 2 * Real.pi * y by positivity))

theorem exponentialSeries_pos (k : ℕ) {y : ℝ} (hy : 0 < y) :
    0 < ∑' n : ℕ, exponentialTerm k n y := by
  exact (summable_exponentialTerm k hy).tsum_pos
    (fun n => (exponentialTerm_pos k n y).le) 0 (exponentialTerm_pos k 0 y)

theorem density_pos (k : ℕ) {y : ℝ} (hy : 0 < y) : 0 < density k y := by
  unfold density
  exact mul_pos (by positivity) (exponentialSeries_pos k hy)

theorem density_nonneg (k : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ density k y := by
  rcases eq_or_lt_of_le hy with rfl | hy
  · simp [density]
  · exact (density_pos k hy).le

theorem density_zero (k : ℕ) : density k 0 = 0 := by
  simp [density]

theorem measurable_exponentialTerm (k n : ℕ) : Measurable (exponentialTerm k n) := by
  unfold exponentialTerm
  fun_prop

theorem measurable_density (k : ℕ) : Measurable (density k) := by
  unfold density
  exact (measurable_const.mul (measurable_id.pow_const _)).mul
    (Measurable.tsum (fun n => measurable_exponentialTerm k n))

/-- The measure with the paper's density on the positive `y` half-line.
This is a constructed measure, not an assumed moment realization. -/
def baseMeasure (k : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun y => ENNReal.ofReal (density k y))

instance baseMeasure_nullSingleton (k : ℕ) : NullSingletonClass (baseMeasure k) := by
  unfold baseMeasure
  infer_instance

theorem baseMeasure_nonzero (k : ℕ) : baseMeasure k ≠ 0 := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ baseMeasure k := by
    apply withDensity_absolutelyContinuous'
      (measurable_density k).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (density_pos k hy))
  intro hzero
  rw [hzero] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

end ManuscriptChain.Hyperbolic

#print axioms ManuscriptChain.Hyperbolic.summable_exponentialTerm
#print axioms ManuscriptChain.Hyperbolic.density_pos
#print axioms ManuscriptChain.Hyperbolic.measurable_density
#print axioms ManuscriptChain.Hyperbolic.baseMeasure_nonzero
