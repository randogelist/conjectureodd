import Definition_2_1_Order_s_Rational_Moment_Functional
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Positive moment realizations of the general odd-weight pencil

A nonzero measure on the real line that gives zero mass to each point makes
the square of every nonzero polynomial have strictly positive integral,
provided that square is integrable. Consequently its finite monomial moment
matrices are positive definite.

The last theorem transfers this analytic fact to the manuscript's arbitrary
odd-weight pencil, conditional on its entrywise moment representation. That
representation, including the construction and estimates for the proposed
hyperbolic density, is an explicit input; it is not proved in this file.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Matrix Polynomial

namespace ManuscriptChain.Moments

/-- The finite Hankel matrix of moments of a real measure. -/
def momentMatrix (μ : Measure ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ x, x ^ (i.val + j.val) ∂μ

theorem eval_ofFn_eq_sum {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    (Polynomial.ofFn n c).eval x = ∑ i, c i * x ^ i.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem eval_ofFn_sq_eq_sum {n : ℕ} (c : Fin n → ℝ) (x : ℝ) :
    ((Polynomial.ofFn n c).eval x) ^ 2 =
      ∑ i, ∑ j, (c i * c j) * x ^ (i.val + j.val) := by
  rw [eval_ofFn_eq_sum, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

/-- Finitely many integrable moments suffice for every polynomial square of
the corresponding degree; square integrability is not a separate premise. -/
theorem integrable_eval_ofFn_sq {μ : Measure ℝ} {n : ℕ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ)
    (c : Fin n → ℝ) :
    Integrable (fun x => ((Polynomial.ofFn n c).eval x) ^ 2) μ := by
  simp_rw [eval_ofFn_sq_eq_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact (hm i j).const_mul (c i * c j)

/-- The quadratic form of the moment matrix is the integral of a square. -/
theorem quadratic_eq_integral_sq {μ : Measure ℝ} {n : ℕ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ)
    (c : Fin n → ℝ) :
    star c ⬝ᵥ (momentMatrix μ n *ᵥ c) =
      ∫ x, ((Polynomial.ofFn n c).eval x) ^ 2 ∂μ := by
  simp_rw [eval_ofFn_sq_eq_sum]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => (hm i j).const_mul (c i * c j)))]
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hm i j).const_mul (c i * c j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul]
  simp only [momentMatrix]
  ring

/-- A nonzero polynomial has only finitely many zeros, hence its square has
strictly positive integral for any nonzero measure with no point masses. -/
theorem integral_polynomial_sq_pos {μ : Measure ℝ} [NullSingletonClass μ]
    (hμ : μ ≠ 0) {q : ℝ[X]} (hq : q ≠ 0)
    (hqi : Integrable (fun x => (q.eval x) ^ 2) μ) :
    0 < ∫ x, (q.eval x) ^ 2 ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg (q.eval x)) hqi).2
  have hnull : μ (Function.support (fun x => (q.eval x) ^ 2))ᶜ = 0 := by
    have hset : (Function.support (fun x => (q.eval x) ^ 2))ᶜ =
        {x | Polynomial.IsRoot q x} := by
      ext x
      simp [Function.mem_support, Polynomial.IsRoot]
    rw [hset]
    exact (Polynomial.finite_setOfPred_isRoot hq).measure_zero μ
  rw [measure_of_measure_compl_eq_zero hnull]
  exact Measure.measure_univ_pos.mpr hμ

/-- Genuine analytic positivity of finite monomial moment matrices. -/
theorem momentMatrix_posDef {μ : Measure ℝ} [NullSingletonClass μ]
    (hμ : μ ≠ 0) {n : ℕ}
    (hm : ∀ i j : Fin n, Integrable (fun x : ℝ => x ^ (i.val + j.val)) μ) :
    (momentMatrix μ n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [momentMatrix, Nat.add_comm]
  · intro c hc
    rw [quadratic_eq_integral_sq hm c]
    apply integral_polynomial_sq_pos hμ _ (integrable_eval_ofFn_sq hm c)
    intro h
    apply hc
    apply Polynomial.injective_ofFn n
    simpa using h

end ManuscriptChain.Moments

namespace ManuscriptChain.Real

/-- Analytic inputs that remain to be established for the manuscript's
hyperbolic weight. The structure asserts moment identities and measure
nondegeneracy, rather than assuming the desired matrix positivity. -/
structure PositiveMomentRealization (p : Parameters) where
  measure : Measure ℝ
  nullSingleton : NullSingletonClass measure
  nonzero : measure ≠ 0
  integrable_moments : ∀ i j : Fin p.h,
    Integrable (fun x : ℝ => x ^ (i.val + j.val)) measure
  moment_identity : ∀ i j : Fin p.h,
    gram p (zeta p.weight) i j = ∫ x, x ^ (i.val + j.val) ∂measure

/-- For every odd weight `2*k+1`, a positive moment realization supplies
the strict Gram positivity needed by the general algebraic chain. -/
theorem PositiveMomentRealization.gram_posDef {p : Parameters}
    (r : PositiveMomentRealization p) : (gram p (zeta p.weight)).PosDef := by
  let : NullSingletonClass r.measure := r.nullSingleton
  have hmatrix : gram p (zeta p.weight) = Moments.momentMatrix r.measure p.h := by
    ext i j
    exact r.moment_identity i j
  rw [hmatrix]
  exact Moments.momentMatrix_posDef r.nonzero r.integrable_moments

end ManuscriptChain.Real
