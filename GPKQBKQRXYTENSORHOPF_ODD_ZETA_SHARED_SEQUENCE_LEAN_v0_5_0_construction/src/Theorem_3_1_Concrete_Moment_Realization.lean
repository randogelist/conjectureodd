import Theorem_3_1_Hyperbolic_Moments
import Theorem_3_1_Positive_Moment_Realization
import Zetahyperbolic.Section2Checked
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The concrete measure behind the general odd-weight Gram matrix

The measure is constructed from the paper's density and denominator ratio,
then pushed forward by `y ↦ y^2`. Its nonzero and atomless properties are
proved, not assumed. Exact identification with the rational moment functional
remains an explicit input to the final realization constructor.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace ManuscriptChain.ConcreteMoment

def weightedDensity (p : Real.Parameters) (y : ℝ) : ℝ :=
  (Zetahyperbolic.D_real p.N (y ^ 2)) ^ (2 * p.m) /
    Zetahyperbolic.D_real p.K (y ^ 2) * Hyperbolic.density p.k y

theorem weightedDensity_pos (p : Real.Parameters) {y : ℝ} (hy : 0 < y) :
    0 < weightedDensity p y :=
  mul_pos (Zetahyperbolic.D_real_ratio_pos p.N p.K p.m hy)
    (Hyperbolic.density_pos p.k hy)

theorem measurable_weightedDensity (p : Real.Parameters) :
    Measurable (weightedDensity p) := by
  unfold weightedDensity Zetahyperbolic.D_real
  apply Measurable.mul _ (Hyperbolic.measurable_density p.k)
  fun_prop

def weightedMeasure (p : Real.Parameters) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun y => ENNReal.ofReal (weightedDensity p y))

instance weightedMeasure_nullSingleton (p : Real.Parameters) :
    NullSingletonClass (weightedMeasure p) := by
  unfold weightedMeasure
  infer_instance

theorem weightedMeasure_nonzero (p : Real.Parameters) : weightedMeasure p ≠ 0 := by
  have hac : volume.restrict (Ioi (0 : ℝ)) ≪ weightedMeasure p := by
    apply withDensity_absolutelyContinuous'
      (measurable_weightedDensity p).ennreal_ofReal.aemeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (weightedDensity_pos p hy))
  intro hzero
  rw [hzero] at hac
  have h := Measure.absolutelyContinuous_zero_iff.mp hac
  have hu := congrArg (fun μ : Measure ℝ => μ Set.univ) h
  simp at hu

/-- The actual moment measure in the variable `t = y^2`. -/
def momentMeasure (p : Real.Parameters) : Measure ℝ :=
  (weightedMeasure p).map (fun y : ℝ => y ^ 2)

theorem momentMeasure_nonzero (p : Real.Parameters) : momentMeasure p ≠ 0 := by
  exact (Measure.map_ne_zero_iff (by fun_prop)).2 (weightedMeasure_nonzero p)

instance momentMeasure_nullSingleton (p : Real.Parameters) :
    NullSingletonClass (momentMeasure p) := by
  constructor
  intro t
  rw [momentMeasure, Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  have hq : (X ^ 2 - C t : ℝ[X]) ≠ 0 := by
    intro h
    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff 2) h
    norm_num at hcoeff
  have hz := (Polynomial.finite_setOfPred_isRoot hq).measure_zero (weightedMeasure p)
  have hs : (fun y : ℝ => y ^ 2) ⁻¹' {t} =
      {y | Polynomial.IsRoot (X ^ 2 - C t : ℝ[X]) y} := by
    ext y
    simp [Polynomial.IsRoot, sub_eq_zero]
  rw [hs]
  exact hz

/-- The pushforward moment equals the original positive-half-line integral. -/
theorem integral_momentMeasure (p : Real.Parameters) (e : ℕ) :
    (∫ t, t ^ e ∂momentMeasure p) =
      ∫ y in Ioi (0 : ℝ), y ^ (2 * e) * weightedDensity p y := by
  rw [momentMeasure, integral_map (by fun_prop) (by fun_prop), weightedMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_weightedDensity p).ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p hy).le]
  simp only [smul_eq_mul]
  rw [← pow_mul]
  ring

/-- Moment integrability in the two coordinates is equivalent. -/
theorem integrable_momentMeasure_iff (p : Real.Parameters) (e : ℕ) :
    Integrable (fun t : ℝ => t ^ e) (momentMeasure p) ↔
      IntegrableOn (fun y : ℝ => y ^ (2 * e) * weightedDensity p y) (Ioi 0) := by
  rw [momentMeasure, integrable_map_measure (by fun_prop) (by fun_prop),
    weightedMeasure, integrable_withDensity_iff_integrable_smul'
      (measurable_weightedDensity p).ennreal_ofReal (by simp)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [ENNReal.toReal_ofReal (weightedDensity_pos p hy).le]
  simp only [Function.comp_def, smul_eq_mul]
  rw [← pow_mul]
  ring

/-- Every polynomial in `y^2` is integrable against the base density. -/
theorem integrableOn_polynomial_density (k : ℕ) (q : ℝ[X]) :
    IntegrableOn (fun y : ℝ => q.eval (y ^ 2) * Hyperbolic.density k y) (Ioi 0) := by
  have hi := integrable_finsetSum q.support (fun e _ =>
    (Hyperbolic.integrableOn_monomial_density k e).const_mul (q.coeff e))
  apply hi.congr
  filter_upwards [] with y
  symm
  simp only [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [← pow_mul]
  ring

/-- The denominator is at least one, so weighted moments are dominated by
polynomial moments of the already-integrable base density. -/
theorem integrableOn_weightedDensity_moment (p : Real.Parameters) (e : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ (2 * e) * weightedDensity p y) (Ioi 0) := by
  let q : ℝ[X] :=
    (∏ j ∈ Finset.Icc 1 p.N, (X + C ((j : ℝ) ^ 2))) ^ (2 * p.m) * X ^ e
  have heval (y : ℝ) : q.eval (y ^ 2) =
      (Zetahyperbolic.D_real p.N (y ^ 2)) ^ (2 * p.m) * y ^ (2 * e) := by
    simp only [q, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_prod,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Zetahyperbolic.D_real, ← pow_mul]
  have hi := integrableOn_polynomial_density p.k q
  apply hi.mono' ((measurable_id.pow_const _).mul
    (measurable_weightedDensity p)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos : 0 < y := hy
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    exact mul_nonneg (pow_nonneg hypos.le _) (weightedDensity_pos p hypos).le)]
  rw [heval]
  have hratio := div_le_self
    (pow_nonneg (Zetahyperbolic.D_real_pos p.N (show 0 < y ^ 2 by positivity)).le (2 * p.m))
    (Zetahyperbolic.D_real_ge_one p.K (show 0 < y ^ 2 by positivity))
  have hmul := mul_le_mul_of_nonneg_right hratio (Hyperbolic.density_pos p.k hypos).le
  have htotal := mul_le_mul_of_nonneg_left hmul (pow_nonneg hypos.le (2 * e))
  simpa [weightedDensity, mul_assoc, mul_left_comm, mul_comm] using htotal

/-- All measure nondegeneracy obligations are constructed here. This version
takes only the exact entry identities as an input. Moment integrability is proved. -/
def realization (p : Real.Parameters)
    (hentry : ∀ i j : Fin p.h,
      Real.gram p (Real.zeta p.weight) i j =
        ∫ y in Ioi (0 : ℝ), y ^ (2 * (i.val + j.val)) * weightedDensity p y) :
    Real.PositiveMomentRealization p where
  measure := momentMeasure p
  nullSingleton := inferInstance
  nonzero := momentMeasure_nonzero p
  integrable_moments := fun i j => (integrable_momentMeasure_iff p (i.val + j.val)).2
    (integrableOn_weightedDensity_moment p (i.val + j.val))
  moment_identity := fun i j => (hentry i j).trans (integral_momentMeasure p _).symm

end ManuscriptChain.ConcreteMoment

#print axioms ManuscriptChain.ConcreteMoment.weightedMeasure_nonzero
#print axioms ManuscriptChain.ConcreteMoment.momentMeasure_nullSingleton
#print axioms ManuscriptChain.ConcreteMoment.integral_momentMeasure
#print axioms ManuscriptChain.ConcreteMoment.realization

#print axioms ManuscriptChain.ConcreteMoment.integrableOn_weightedDensity_moment
