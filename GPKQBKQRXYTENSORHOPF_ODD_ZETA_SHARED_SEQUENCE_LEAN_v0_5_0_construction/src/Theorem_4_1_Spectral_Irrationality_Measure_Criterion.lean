import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk
import Mathlib.Algebra.Polynomial.DenomsClearable
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Complex.Exponential

/-!
# Theorem 4.1 (Spectral irrationality measure criterion)

PDF pp. 14-15. Conditional transfer with explicit LocalComparison, Decay,
and IndexBudget inputs. The integer-denominator squeeze and the implication
from a rational measure to irrationality are proved. The final part derives
local comparison from the supplied spectral factorization. Index selection
and a denominator threshold remain inputs.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.RealTransfer

noncomputable def evalReal (P : Polynomial ℤ) (x : ℝ) : ℝ :=
  (P.map (algebraMap ℤ ℝ)).eval x

theorem cleared_eval_is_integer (P : Polynomial ℤ) (a : ℤ) (b : ℕ)
    (hb : 0 < b) :
    ∃ z : ℤ, (z : ℝ) = (b : ℝ) ^ P.natDegree * evalReal P ((a : ℝ) / b) := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  obtain ⟨z, bi, hbi, hz⟩ :=
    denomsClearable_natDegree
      (b := (b : ℤ)) (bi := (b : ℝ)⁻¹) (algebraMap ℤ ℝ) P a
      (by simpa using inv_mul_cancel₀ hbR)
  refine ⟨z, ?_⟩
  rw [eq_one_div_of_mul_eq_one_left hbi] at hz
  simpa [evalReal, div_eq_mul_inv] using hz

theorem polynomial_integer_squeeze (P : Polynomial ℤ) (a : ℤ) (b : ℕ)
    (hb : 0 < b)
    (hne : evalReal P ((a : ℝ) / b) ≠ 0)
    (hsmall : (b : ℝ) ^ P.natDegree * |evalReal P ((a : ℝ) / b)| < 1) :
    False := by
  have hlow := one_le_pow_mul_abs_eval_div
    (K := ℝ) (f := P) (a := a) (b := (b : ℤ))
    (by exact_mod_cast hb) (by simpa [evalReal] using hne)
  have hlow' : (1 : ℝ) ≤ (b : ℝ) ^ P.natDegree *
      |evalReal P ((a : ℝ) / b)| := by
    simpa [evalReal] using hlow
  exact (not_lt_of_ge hlow') hsmall

structure LocalComparison (Q : ℕ → Polynomial ℤ) (ξ : ℝ)
    (radius : ℕ → ℝ) (n₀ : ℕ) : Prop where
  compare : ∀ n, n₀ ≤ n → ∀ x : ℝ,
    |x - ξ| ≤ radius n → evalReal (Q n) ξ ≠ 0 →
    evalReal (Q n) x ≠ 0 ∧
      |evalReal (Q n) x| ≤ 2 * |evalReal (Q n) ξ|

structure Decay (Q : ℕ → Polynomial ℤ) (ξ : ℝ)
    (budget : ℕ → ℝ) (n₀ : ℕ) : Prop where
  nonzero : ∀ n, n₀ ≤ n → evalReal (Q n) ξ ≠ 0
  upper : ∀ n, n₀ ≤ n → |evalReal (Q n) ξ| ≤ budget n

structure IndexBudget (Q : ℕ → Polynomial ℤ) (radius budget : ℕ → ℝ)
    (n₀ μ b₀ : ℕ) : Prop where
  choose : ∀ b : ℕ, 0 < b → b₀ ≤ b →
    ∃ n : ℕ, n₀ ≤ n ∧
      1 / (b : ℝ) ^ μ ≤ radius n ∧
      2 * (b : ℝ) ^ (Q n).natDegree * budget n < 1

def RationalMeasure (ξ : ℝ) (μ b₀ : ℕ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → b₀ ≤ b →
    1 / (b : ℝ) ^ μ < |ξ - (a : ℝ) / b|

theorem conditional_measure
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {radius budget : ℕ → ℝ}
    {n₀ μ b₀ : ℕ}
    (comparison : LocalComparison Q ξ radius n₀)
    (decay : Decay Q ξ budget n₀)
    (index : IndexBudget Q radius budget n₀ μ b₀) :
    RationalMeasure ξ μ b₀ := by
  intro a b hb hbb
  by_contra hnot
  have hclose : |ξ - (a : ℝ) / b| ≤ 1 / (b : ℝ) ^ μ := le_of_not_gt hnot
  obtain ⟨n, hn, hradius, hbudget⟩ := index.choose b hb hbb
  have hclose' : |(a : ℝ) / b - ξ| ≤ radius n := by
    rw [abs_sub_comm]
    exact hclose.trans hradius
  obtain ⟨hne, hcomp⟩ := comparison.compare n hn ((a : ℝ) / b) hclose'
    (decay.nonzero n hn)
  have hbpow : 0 ≤ (b : ℝ) ^ (Q n).natDegree := by positivity
  apply polynomial_integer_squeeze (Q n) a b hb hne
  calc
    (b : ℝ) ^ (Q n).natDegree * |evalReal (Q n) ((a : ℝ) / b)|
        ≤ (b : ℝ) ^ (Q n).natDegree * (2 * |evalReal (Q n) ξ|) :=
      mul_le_mul_of_nonneg_left hcomp hbpow
    _ ≤ (b : ℝ) ^ (Q n).natDegree * (2 * budget n) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (decay.upper n hn) (by norm_num)) hbpow
    _ = 2 * (b : ℝ) ^ (Q n).natDegree * budget n := by ring
    _ < 1 := hbudget

theorem RationalMeasure.irrational {ξ : ℝ} {μ b₀ : ℕ}
    (h : RationalMeasure ξ μ b₀) : Irrational ξ := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  let t : ℕ := b₀ + 1
  let b : ℕ := r.den * t
  let a : ℤ := r.num * (t : ℤ)
  have ht : 0 < t := by dsimp [t]; omega
  have hd : 0 < r.den := r.pos
  have hb : 0 < b := Nat.mul_pos hd ht
  have hbb : b₀ ≤ b := by
    dsimp [b, t]
    nlinarith
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hdR : (r.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hab : (a : ℝ) / (b : ℝ) = ξ := by
    calc
      (a : ℝ) / (b : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
        dsimp [a, b]
        push_cast
        field_simp
      _ = (r : ℝ) := (Rat.cast_def r).symm
      _ = ξ := hr
  have hmeasure := h a b hb hbb
  rw [hab, sub_self, abs_zero] at hmeasure
  have hpositive : (0 : ℝ) < 1 / (b : ℝ) ^ μ := by positivity
  exact (not_lt_of_ge (le_of_lt hpositive)) hmeasure

theorem conditional_irrational
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {radius budget : ℕ → ℝ}
    {n₀ μ b₀ : ℕ}
    (comparison : LocalComparison Q ξ radius n₀)
    (decay : Decay Q ξ budget n₀)
    (index : IndexBudget Q radius budget n₀ μ b₀) :
    Irrational ξ :=
  (conditional_measure comparison decay index).irrational

theorem paper_parameter_inequalities :
    (9 / 10 : ℚ) / (1 / 2500) < 2251 ∧
    (11411 / 1000 : ℚ) * 2251 < 25687 := by
  norm_num

theorem paper_transfer_threshold :
    (9 / 10 : ℚ) * (11411 / 1000) / (1 / 2500) = 102699 / 4 := by
  norm_num

theorem paper_decay_margin :
    (-232425 / 100000 : ℚ) + 1 / 100000 +
      (232380 / 100000 + 1 / 100000) < -(1 / 2500) := by
  norm_num

end ManuscriptChain.RealTransfer

namespace ManuscriptChain.Spectral

theorem product_comparison_of_sum_abs_le {n : ℕ} (u : Fin n → ℝ)
    (hsum : ∑ i, |u i| ≤ (1 / 4 : ℝ)) :
    (∏ i, (1 + u i)) ≠ 0 ∧ |∏ i, (1 + u i)| ≤ 2 := by
  have hfactor : ∀ i, 0 < 1 + u i := by
    intro i
    have hi : |u i| ≤ (1 / 4 : ℝ) :=
      (Finset.single_le_sum (fun j _ => abs_nonneg (u j)) (Finset.mem_univ i)).trans hsum
    have hlow := neg_abs_le (u i)
    linarith
  have hprodpos : 0 < ∏ i, (1 + u i) :=
    Finset.prod_pos (fun i _ => hfactor i)
  refine ⟨ne_of_gt hprodpos, ?_⟩
  calc
    |∏ i, (1 + u i)| = ∏ i, |1 + u i| := Finset.abs_prod _ _
    _ ≤ ∏ i, (1 + |u i|) := by
      apply Finset.prod_le_prod
      · intro i _
        exact abs_nonneg _
      · intro i _
        simpa using abs_add_le (1 : ℝ) (u i)
    _ ≤ Real.exp (∑ i, |u i|) :=
      Real.prod_one_add_le_exp_sum _ (fun i => abs_nonneg (u i))
    _ ≤ Real.exp (1 / 4 : ℝ) := Real.exp_le_exp.mpr hsum
    _ ≤ 1 / (1 - (1 / 4 : ℝ)) :=
      Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    _ ≤ 2 := by norm_num

def comparisonRadius (n : ℕ) (bound : ℝ) : ℝ :=
  1 / (8 * ((n : ℝ) + 1) * bound)

theorem comparisonRadius_pos (n : ℕ) (bound : ℝ) (hbound : 0 < bound) :
    0 < comparisonRadius n bound := by
  unfold comparisonRadius
  positivity

namespace RootFactorization

variable {n : ℕ} {p : SymmetricAffinePencil n} (c : RootFactorization p)

theorem comparison_of_sum_le (x : ℝ)
    (hsum : ∑ i, |(x - p.center) * c.beta i| ≤ (1 / 4 : ℝ)) :
    p.detPolynomial.eval x ≠ 0 ∧
      |p.detPolynomial.eval x| ≤ 2 * |p.detPolynomial.eval p.center| := by
  obtain ⟨hne, hupper⟩ := product_comparison_of_sum_abs_le
    (fun i => (x - p.center) * c.beta i) hsum
  constructor
  · rw [c.eval_eq]
    exact mul_ne_zero c.base_det_ne_zero hne
  · rw [p.eval_detPolynomial_center, c.eval_eq, abs_mul]
    calc
      |p.base.det| * |∏ i, (1 + (x - p.center) * c.beta i)|
          ≤ |p.base.det| * 2 :=
        mul_le_mul_of_nonneg_left hupper (abs_nonneg _)
      _ = 2 * |p.base.det| := by ring

theorem perturbation_sum_le_of_radius (bound x : ℝ) (hbound : 0 < bound)
    (hbeta : ∀ i, |c.beta i| ≤ bound)
    (hx : |x - p.center| ≤ comparisonRadius n bound) :
    ∑ i, |(x - p.center) * c.beta i| ≤ (1 / 4 : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 0 < 8 * ((n : ℝ) + 1) := by positivity
  have hpoint : |x - p.center| * bound ≤ 1 / (8 * ((n : ℝ) + 1)) := by
    calc
      |x - p.center| * bound ≤ comparisonRadius n bound * bound :=
        mul_le_mul_of_nonneg_right hx hbound.le
      _ = 1 / (8 * ((n : ℝ) + 1)) := by
        unfold comparisonRadius
        field_simp
  calc
    ∑ i, |(x - p.center) * c.beta i|
        ≤ ∑ _i : Fin n, |x - p.center| * bound := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hbeta i) (abs_nonneg _)
    _ = (n : ℝ) * (|x - p.center| * bound) := by simp
    _ ≤ (n : ℝ) * (1 / (8 * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hpoint hn
    _ ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ hden]
      nlinarith

theorem comparison_of_radius (bound x : ℝ) (hbound : 0 < bound)
    (hbeta : ∀ i, |c.beta i| ≤ bound)
    (hx : |x - p.center| ≤ comparisonRadius n bound) :
    p.detPolynomial.eval x ≠ 0 ∧
      |p.detPolynomial.eval x| ≤ 2 * |p.detPolynomial.eval p.center| :=
  c.comparison_of_sum_le x (c.perturbation_sum_le_of_radius bound x hbound hbeta hx)

theorem normalized_comparison_of_radius (P : Polynomial ℤ) (scale bound x : ℝ)
    (hscale : scale ≠ 0)
    (hnormalize : p.detPolynomial = C scale * P.map (algebraMap ℤ ℝ))
    (hbound : 0 < bound) (hbeta : ∀ i, |c.beta i| ≤ bound)
    (hx : |x - p.center| ≤ comparisonRadius n bound) :
    RealTransfer.evalReal P x ≠ 0 ∧
      |RealTransfer.evalReal P x| ≤ 2 * |RealTransfer.evalReal P p.center| := by
  obtain ⟨hne, hupper⟩ := c.comparison_of_radius bound x hbound hbeta hx
  have heval : ∀ y : ℝ, p.detPolynomial.eval y = scale * RealTransfer.evalReal P y := by
    intro y
    rw [hnormalize]
    simp [RealTransfer.evalReal]
  constructor
  · intro hzero
    apply hne
    rw [heval, hzero, mul_zero]
  · rw [heval, heval, abs_mul, abs_mul] at hupper
    have hscaled : |scale| * |RealTransfer.evalReal P x| ≤
        |scale| * (2 * |RealTransfer.evalReal P p.center|) := by
      nlinarith [hupper]
    exact le_of_mul_le_mul_left hscaled (abs_pos.mpr hscale)

end RootFactorization

theorem localComparison_of_spectral
    (Q : ℕ → Polynomial ℤ) (center : ℝ) (dimension : ℕ → ℕ)
    (pencil : ∀ j, SymmetricAffinePencil (dimension j))
    (bound scale : ℕ → ℝ) (onset : ℕ)
    (cert : ∀ j, onset ≤ j → RootFactorization (pencil j))
    (hcenter : ∀ j, onset ≤ j → (pencil j).center = center)
    (hbound : ∀ j, onset ≤ j → 0 < bound j)
    (hbeta : ∀ j (hj : onset ≤ j) i, |(cert j hj).beta i| ≤ bound j)
    (hscale : ∀ j, onset ≤ j → scale j ≠ 0)
    (hnormalize : ∀ j, onset ≤ j → (pencil j).detPolynomial =
      C (scale j) * (Q j).map (algebraMap ℤ ℝ)) :
    RealTransfer.LocalComparison Q center
      (fun j => comparisonRadius (dimension j) (bound j)) onset := by
  constructor
  intro j hj x hx _hcenter_nonzero
  have hx' : |x - (pencil j).center| ≤ comparisonRadius (dimension j) (bound j) := by
    simpa [hcenter j hj] using hx
  have h := (cert j hj).normalized_comparison_of_radius (Q j) (scale j) (bound j) x
    (hscale j hj) (hnormalize j hj) (hbound j hj) (hbeta j hj) hx'
  simpa [hcenter j hj] using h

end ManuscriptChain.Spectral
