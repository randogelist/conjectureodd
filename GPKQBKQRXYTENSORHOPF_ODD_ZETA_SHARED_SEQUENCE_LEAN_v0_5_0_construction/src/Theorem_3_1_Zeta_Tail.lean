import Definition_2_1_Order_s_Rational_Moment_Functional
import Mathlib.Tactic

/-!
# Shifted positive zeta series

Removing the first `a` summands from the convergent positive zeta series
gives exactly the rational harmonic correction used in `poleConstant`.
All assertions in this module are unconditional series identities.
-/

noncomputable section
open scoped BigOperators

namespace ManuscriptChain.Real

theorem harmonic_cast_eq_sum (s a : ℕ) :
    (harmonic s a : ℝ) =
      ∑ n ∈ Finset.range a, 1 / ((n + 1 : ℕ) : ℝ) ^ s := by
  simp [harmonic]

theorem zeta_tail_summable {s : ℕ} (hs : 1 < s) (a : ℕ) :
    Summable (fun n : ℕ => 1 / ((a + n + 1 : ℕ) : ℝ) ^ s) := by
  have h := (summable_nat_add_iff a).mpr (zeta_series_summable hs)
  simpa only [Nat.add_comm a] using h

theorem zeta_tail_sum {s : ℕ} (hs : 1 < s) (a : ℕ) :
    (∑' n : ℕ, 1 / ((a + n + 1 : ℕ) : ℝ) ^ s) =
      zeta s - (harmonic s a : ℝ) := by
  have h := (zeta_series_summable hs).sum_add_tsum_nat_add a
  change (∑ n ∈ Finset.range a, 1 / ((n + 1 : ℕ) : ℝ) ^ s) +
    (∑' n : ℕ, 1 / ((n + a + 1 : ℕ) : ℝ) ^ s) = zeta s at h
  rw [← harmonic_cast_eq_sum] at h
  have ht : (∑' n : ℕ, 1 / ((a + n + 1 : ℕ) : ℝ) ^ s) =
      ∑' n : ℕ, 1 / ((n + a + 1 : ℕ) : ℝ) ^ s := by
    apply tsum_congr
    intro n
    rw [Nat.add_comm a n]
  rw [ht]
  linarith

theorem zeta_odd_tail_sum (k a : ℕ) (hk : 1 ≤ k) :
    (∑' n : ℕ, 1 / ((a + n + 1 : ℕ) : ℝ) ^ (2 * k + 1)) =
      zeta (2 * k + 1) - (harmonic (2 * k + 1) a : ℝ) :=
  zeta_tail_sum (by omega) a

/-- The shifted series and elementary corrections have exactly the pole
value required by the rational moment functional. -/
theorem zeta_tail_pole_value (k a : ℕ) (hk : 1 ≤ k) :
    (a : ℝ) ^ (2 * k) *
        (∑' n : ℕ, 1 / ((a + n + 1 : ℕ) : ℝ) ^ (2 * k + 1)) +
      1 / (2 * (a : ℝ)) - 1 / (2 * (k : ℝ)) =
      (a : ℝ) ^ (2 * k) * zeta (2 * k + 1) + (poleConstant k a : ℝ) := by
  rw [zeta_odd_tail_sum k a hk]
  unfold poleConstant
  push_cast
  ring

end ManuscriptChain.Real

#print axioms ManuscriptChain.Real.zeta_tail_summable
#print axioms ManuscriptChain.Real.zeta_tail_sum
#print axioms ManuscriptChain.Real.zeta_odd_tail_sum
#print axioms ManuscriptChain.Real.zeta_tail_pole_value
