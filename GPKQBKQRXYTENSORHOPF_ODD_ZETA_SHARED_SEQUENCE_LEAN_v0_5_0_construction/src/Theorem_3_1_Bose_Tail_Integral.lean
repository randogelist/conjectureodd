import Theorem_3_1_Hyperbolic_Moments
import Theorem_3_1_Zeta_Tail

/-! The positive Bose integral evaluated by geometric expansion and Gamma
integrals.  No Hermite integral formula or integration by parts is assumed. -/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

theorem bose_geometric {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, Real.exp (-x * ((n + 1 : ℕ) : ℝ))) =
      1 / (Real.exp x - 1) := by
  have ht (n : ℕ) : Real.exp (-x * ((n + 1 : ℕ) : ℝ)) =
      Real.exp (-x) * Real.exp (-x) ^ n := by
    rw [show -x * ((n + 1 : ℕ) : ℝ) = -x + (n : ℝ) * (-x) by push_cast; ring,
      Real.exp_add, Real.exp_nat_mul]
  simp_rw [ht]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_lt_one_iff.mpr (by linarith))]
  have he : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
  have he1 : Real.exp x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx))
  rw [Real.exp_neg]
  field_simp

def boseTailTerm (k a n : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * k) * Real.exp (-((2 * Real.pi / (a : ℝ)) * ((n + a + 1 : ℕ) : ℝ) * t))

def boseTailCoefficient (k a : ℕ) : ℝ :=
  (Nat.factorial (2 * k) : ℝ) / (2 * Real.pi / (a : ℝ)) ^ (2 * k + 1)

theorem boseTailTerm_integrable (k a n : ℕ) (ha : 0 < a) :
    IntegrableOn (boseTailTerm k a n) (Ioi 0) := by
  unfold boseTailTerm
  exact integrableOn_pow_mul_exp _ (by positivity)

theorem integral_boseTailTerm (k a n : ℕ) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, boseTailTerm k a n t) =
      boseTailCoefficient k a * (1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1)) := by
  unfold boseTailTerm boseTailCoefficient
  rw [integral_pow_mul_exp _ (by positivity), mul_pow]
  ring

theorem boseTailTerm_nonneg (k a n : ℕ) (t : ℝ) : 0 ≤ boseTailTerm k a n t := by
  unfold boseTailTerm
  exact mul_nonneg (by simpa only [pow_mul] using pow_nonneg (sq_nonneg t) k)
    (Real.exp_nonneg _)

theorem summable_boseTail (k a : ℕ) (hk : 0 < k) :
    Summable (fun n : ℕ => 1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1)) := by
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff a).mpr (Real.zeta_series_summable (s := 2 * k + 1) (by omega))

theorem summable_integral_norm_boseTailTerm (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    Summable (fun n => ∫ t : ℝ in Ioi 0, ‖boseTailTerm k a n t‖) := by
  simp_rw [Real.norm_of_nonneg (boseTailTerm_nonneg k a _ _), integral_boseTailTerm k a _ ha]
  exact (summable_boseTail k a hk).mul_left _

theorem integral_tsum_boseTailTerm (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, ∑' n, boseTailTerm k a n t) =
      boseTailCoefficient k a *
        ∑' n : ℕ, 1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1) := by
  rw [← integral_tsum_of_summable_integral_norm (fun n => boseTailTerm_integrable k a n ha)
    (summable_integral_norm_boseTailTerm k a hk ha)]
  simp_rw [integral_boseTailTerm k a _ ha]
  rw [tsum_mul_left]

theorem integrableOn_tsum_boseTailTerm (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => ∑' n, boseTailTerm k a n t) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_tsum_boseTailTerm k a hk ha]
  apply ne_of_gt
  apply mul_pos
  · unfold boseTailCoefficient
    positivity
  · exact (summable_boseTail k a hk).tsum_pos (fun n => by positivity) 0 (by positivity)

theorem bose_tail_eq_tsum (k a : ℕ) (ha : 0 < a) {t : ℝ} (ht : 0 < t) :
    t ^ (2 * k) * Real.exp (-(2 * Real.pi) * t) /
      (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1) =
        ∑' n, boseTailTerm k a n t := by
  have ha' : (a : ℝ) ≠ 0 := by positivity
  rw [div_eq_mul_inv, ← one_div, ← bose_geometric (by positivity)]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold boseTailTerm
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  field_simp
  ring

theorem integrableOn_bose_tail (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (2 * k) * Real.exp (-(2 * Real.pi) * t) /
      (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) (Ioi 0) := by
  exact (integrableOn_tsum_boseTailTerm k a hk ha).congr_fun
    (fun t ht => (bose_tail_eq_tsum k a ha ht).symm) measurableSet_Ioi

theorem integral_bose_tail_tsum (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t ^ (2 * k) * Real.exp (-(2 * Real.pi) * t) /
      (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) =
        (Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1) *
          (a : ℝ) ^ (2 * k + 1) *
            ∑' n : ℕ, 1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => bose_tail_eq_tsum k a ha ht),
    integral_tsum_boseTailTerm k a hk ha]
  unfold boseTailCoefficient
  rw [div_pow]
  congr 1
  field_simp


theorem integral_bose_tail (k a : ℕ) (hk : 0 < k) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, t ^ (2 * k) * Real.exp (-(2 * Real.pi) * t) /
      (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) =
        (Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1) *
          (a : ℝ) ^ (2 * k + 1) *
            (Real.zeta (2 * k + 1) - (Real.harmonic (2 * k + 1) a : ℝ)) := by
  rw [integral_bose_tail_tsum k a hk ha]
  have htail : (∑' n : ℕ, 1 / ((n + a + 1 : ℕ) : ℝ) ^ (2 * k + 1)) =
      Real.zeta (2 * k + 1) - (Real.harmonic (2 * k + 1) a : ℝ) := by
    simpa only [Nat.add_comm a] using Real.zeta_tail_sum (s := 2 * k + 1) (by omega) a
  rw [htail]

end ManuscriptChain.Hyperbolic

#print axioms ManuscriptChain.Hyperbolic.bose_geometric
#print axioms ManuscriptChain.Hyperbolic.integrableOn_bose_tail
#print axioms ManuscriptChain.Hyperbolic.integral_bose_tail_tsum

#print axioms ManuscriptChain.Hyperbolic.integral_bose_tail
