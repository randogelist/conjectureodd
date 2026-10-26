import Theorem_3_1_Rational_Integral_Bridge
import Theorem_3_1_Pole_Scaling
import Theorem_3_1_Coth_Partial_Fractions
import Theorem_3_1_Bose_Tail_Integral

/-!
The final simple-pole evaluation is assembled from the cotangent partial
fraction expansion, positive changes of variables, and exponential moments.
-/

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace ManuscriptChain.Hyperbolic

theorem pole_scaled_kernel_split_algebra (k : ℕ) (hk : 0 < k)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t)) *
        (Real.pi / (a * t) * (1 / 2 + 1 / (Real.exp (2 * Real.pi * t / a) - 1)) -
          1 / (2 * t ^ 2)) =
      (Real.pi / a) *
        (t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
          (Real.exp (2 * Real.pi * t / a) - 1)) +
      (Real.pi / (2 * a)) * (t ^ (2 * k) * Real.exp (-(2 * Real.pi * t))) -
      (1 / 2) * (t ^ (2 * k - 1) * Real.exp (-(2 * Real.pi * t))) := by
  have he : Real.exp (2 * Real.pi * t / a) - 1 ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hpow2 : t ^ (2 * k) = t ^ (2 * k - 1) * t := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow3 : t ^ (2 * k + 1) = t ^ (2 * k - 1) * t ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow3, hpow2]
  field_simp
  ring

theorem pole_integral_constants (k a : ℕ) (hk : 0 < k) (ha : 0 < a) (tail : ℝ) :
    (2 * (2 * Real.pi) ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) *
      ((Real.pi / (a : ℝ)) *
        ((Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1) *
          (a : ℝ) ^ (2 * k + 1) * tail) +
       (Real.pi / (2 * (a : ℝ))) *
         ((Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1)) -
       (1 / 2) *
         ((Nat.factorial (2 * k - 1) : ℝ) / (2 * Real.pi) ^ (2 * k))) =
      (a : ℝ) ^ (2 * k) * tail + 1 / (2 * (a : ℝ)) - 1 / (2 * (k : ℝ)) := by
  have hf : (Nat.factorial (2 * k) : ℝ) =
      (2 * (k : ℝ)) * (Nat.factorial (2 * k - 1) : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (show 2 * k ≠ 0 by omega)).symm
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hp0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hf0 : (Nat.factorial (2 * k - 1) : ℝ) ≠ 0 := by positivity
  rw [hf, pow_succ (2 * Real.pi), pow_succ (a : ℝ)]
  field_simp

/-- The actual simple-pole moment identity, with no analytic assumption. -/
theorem poleIntegralIdentity (k : ℕ) (hk : 0 < k) : PoleIntegralIdentity k := by
  intro a ha
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < 2 * Real.pi := by positivity
  have hBint : IntegrableOn
      (fun t : ℝ => t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
        (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) (Ioi 0) := by
    simpa only [neg_mul] using integrableOn_bose_tail k a hk ha
  have hGint := integrableOn_pow_mul_exp (2 * k) hbR
  have hHint := integrableOn_pow_mul_exp (2 * k - 1) hbR
  have hB : (∫ t : ℝ in Ioi 0,
      t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
        (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) =
      (Nat.factorial (2 * k) : ℝ) / (2 * Real.pi) ^ (2 * k + 1) *
        (a : ℝ) ^ (2 * k + 1) *
          (Real.zeta (2 * k + 1) - (Real.harmonic (2 * k + 1) a : ℝ)) := by
    simpa only [neg_mul] using integral_bose_tail k a hk ha
  have hsplit :
      (∫ t : ℝ in Ioi 0, t ^ (2 * k + 1) * Real.exp (-(2 * Real.pi * t)) *
        (∑' n : ℕ, 1 / (t ^ 2 + ((a : ℝ) * ((n + 1 : ℕ) : ℝ)) ^ 2))) =
      (Real.pi / (a : ℝ)) *
        (∫ t : ℝ in Ioi 0, t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
          (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) +
      (Real.pi / (2 * (a : ℝ))) *
        (∫ t : ℝ in Ioi 0, t ^ (2 * k) * Real.exp (-(2 * Real.pi * t))) -
      (1 / 2) *
        (∫ t : ℝ in Ioi 0, t ^ (2 * k - 1) * Real.exp (-(2 * Real.pi * t))) := by
    calc
      _ = ∫ t : ℝ in Ioi 0,
          (Real.pi / (a : ℝ)) *
            (t ^ (2 * k) * Real.exp (-(2 * Real.pi * t)) /
              (Real.exp (2 * Real.pi * t / (a : ℝ)) - 1)) +
          (Real.pi / (2 * (a : ℝ))) *
            (t ^ (2 * k) * Real.exp (-(2 * Real.pi * t))) -
          (1 / 2) *
            (t ^ (2 * k - 1) * Real.exp (-(2 * Real.pi * t))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [coth_partial_fractions ht haR]
        exact pole_scaled_kernel_split_algebra k hk haR ht
      _ = _ := by
        have hBmul := hBint.const_mul (Real.pi / (a : ℝ))
        have hGmul := hGint.const_mul (Real.pi / (2 * (a : ℝ)))
        have hHmul := hHint.const_mul (1 / 2 : ℝ)
        have hs0 := integral_sub (hBmul.add hGmul) hHmul
        have hs1 := integral_add hBmul hGmul
        simp only [Pi.add_apply] at hs0 hs1
        rw [hs0, hs1]
        simp only [integral_const_mul]
  rw [integral_density_div_quadratic k haR, hsplit, hB,
    integral_pow_mul_exp (2 * k) hbR,
    integral_pow_mul_exp (2 * k - 1) hbR,
    show 2 * k - 1 + 1 = 2 * k by omega,
    pole_integral_constants k a hk ha]
  unfold Real.poleConstant
  push_cast
  ring

end ManuscriptChain.Hyperbolic

#print axioms ManuscriptChain.Hyperbolic.poleIntegralIdentity
