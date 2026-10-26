import Theorem_3_1_Hyperbolic_Moments
import Mathlib.Tactic
import Zetahyperbolic.ManuscriptCompatibility
import Theorem_3_1_Concrete_Moment_Realization

/-!
# From generator integrals to the actual affine Gram entries

Polynomial moments and all needed pole-integrability statements are proved.
The simple-pole evaluation remains the explicit analytic input. The finite
partial-fraction expression uses exactly the quotient and residues appearing
in the manuscript's definition of its matrix pencil.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set Polynomial

namespace ManuscriptChain.Hyperbolic

/-- The remaining special-function identity, with the exact paper constants. -/
def PoleIntegralIdentity (k : ℕ) : Prop :=
  ∀ a : ℕ, 0 < a →
    (∫ y : ℝ in Ioi 0, density k y / (y ^ 2 + (a : ℝ) ^ 2)) =
      (a : ℝ) ^ (2 * k) * Real.zeta (2 * k + 1) + (Real.poleConstant k a : ℝ)

theorem evalQ_sq_eq_sum (q : ℚ[X]) (y : ℝ) :
    Real.evalQ q (y ^ 2) = ∑ e ∈ q.support, (q.coeff e : ℝ) * y ^ (2 * e) := by
  rw [Real.evalQ, Real.realPolynomial, Polynomial.eval_map]
  change Polynomial.eval₂ (Rat.castHom ℝ) (y ^ 2) q = _
  rw [Polynomial.eval₂_eq_sum]
  simp only [Polynomial.sum, pow_mul]
  rfl

theorem integrableOn_polynomial_density (k : ℕ) (q : ℚ[X]) :
    IntegrableOn (fun y => Real.evalQ q (y ^ 2) * density k y) (Ioi 0) := by
  simp_rw [evalQ_sq_eq_sum, Finset.sum_mul, mul_assoc]
  apply integrable_finsetSum
  intro e he
  exact (integrableOn_monomial_density k e).const_mul _

theorem integral_polynomial_density (k : ℕ) (q : ℚ[X]) :
    (∫ y : ℝ in Ioi 0, Real.evalQ q (y ^ 2) * density k y) =
      (Real.polynomialMoment k q : ℝ) := by
  simp_rw [evalQ_sq_eq_sum, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun e _ =>
    (integrableOn_monomial_density k e).const_mul (q.coeff e : ℝ))]
  simp_rw [integral_const_mul, integral_monomial_density_eq_monomialMoment]
  simp [Real.polynomialMoment]

theorem integrableOn_pole_density (k a : ℕ) (ha : 0 < a) :
    IntegrableOn (fun y => density k y / (y ^ 2 + (a : ℝ) ^ 2)) (Ioi 0) := by
  have hw : IntegrableOn (density k) (Ioi 0) := by
    simpa using integrableOn_monomial_density k 0
  apply (hw.div_const ((a : ℝ) ^ 2)).mono'
  · exact ((measurable_density k).div
      ((measurable_id.pow_const 2).add measurable_const)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hw0 := (density_pos k hy).le
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hw0 (by positivity))]
    exact div_le_div_of_nonneg_left hw0 (by positivity) (by nlinarith [sq_nonneg y])

/-- The finite partial-fraction expression defining an actual Gram entry. -/
def resolvedKernel (p : Real.Parameters) (i j : ℕ) (y : ℝ) : ℝ :=
  Real.evalQ (Real.quotient p i j) (y ^ 2) +
    ∑ a ∈ Finset.Icc (p.N + 1) p.K,
      (Real.residue p i j a : ℝ) / (y ^ 2 + (a : ℝ) ^ 2)

theorem integrableOn_resolvedKernel_density (p : Real.Parameters) (i j : ℕ) :
    IntegrableOn (fun y => resolvedKernel p i j y * density p.k y) (Ioi 0) := by
  unfold resolvedKernel
  simp_rw [add_mul, Finset.sum_mul]
  apply (integrableOn_polynomial_density p.k _).add
  apply integrable_finsetSum
  intro a ha
  have hapos : 0 < a := by have h := (Finset.mem_Icc.mp ha).1; omega
  have h := (integrableOn_pole_density p.k a hapos).const_mul
    (Real.residue p i j a : ℝ)
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

theorem gram_eq_resolvedKernel_integral (p : Real.Parameters)
    (hpole : PoleIntegralIdentity p.k) (i j : Fin p.h) :
    Real.gram p (Real.zeta p.weight) i j =
      ∫ y : ℝ in Ioi 0, resolvedKernel p i.val j.val y * density p.k y := by
  have hsplit (y : ℝ) : resolvedKernel p i.val j.val y * density p.k y =
      Real.evalQ (Real.quotient p i.val j.val) (y ^ 2) * density p.k y +
        ∑ a ∈ Finset.Icc (p.N + 1) p.K,
          (Real.residue p i.val j.val a : ℝ) *
            (density p.k y / (y ^ 2 + (a : ℝ) ^ 2)) := by
    unfold resolvedKernel
    rw [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hi (a : ℕ) (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
      IntegrableOn (fun y => (Real.residue p i.val j.val a : ℝ) *
        (density p.k y / (y ^ 2 + (a : ℝ) ^ 2))) (Ioi 0) := by
    apply (integrableOn_pole_density p.k a _).const_mul
    have h := (Finset.mem_Icc.mp ha).1
    omega
  simp_rw [hsplit]
  rw [integral_add (integrableOn_polynomial_density p.k _) (integrable_finsetSum _ hi),
    integral_polynomial_density, integral_finsetSum _ hi]
  simp_rw [integral_const_mul]
  have he (a : ℕ) (ha : a ∈ Finset.Icc (p.N + 1) p.K) :=
    hpole a (by have h := (Finset.mem_Icc.mp ha).1; omega)
  simp only [Real.gram, Real.pencil, Real.evalQ, Real.realPolynomial,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  change (Real.entryA p i.val j.val : ℝ) +
    (Real.entryM p i.val j.val : ℝ) * Real.zeta p.weight = _
  unfold Real.entryA Real.entryM
  push_cast
  rw [Finset.sum_mul]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [he a ha]
  dsimp [Real.Parameters.weight]
  ring


open Zetahyperbolic Zetahyperbolic.ManuscriptCompatibility in
theorem resolvedKernel_eq_fraction (p : HankelParams) (k i j : ℕ) {y : ℝ}
    (hy : 0 < y) :
    resolvedKernel (toParameters p k) i j y =
      (kernelNumerator p (i+j)).eval₂ (algebraMap ℚ ℝ) (y^2) /
        (tailPolynomial p.N p.K).eval₂ (algebraMap ℚ ℝ) (y^2) := by
  let s := Finset.Icc (p.N + 1) p.K
  let T : ℝ := ∏ a ∈ s, (y^2 + (a:ℝ)^2)
  have hT : T ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro a ha
    positivity
  have hev : (tailPolynomial p.N p.K).eval₂ (algebraMap ℚ ℝ) (y^2) = T := by
    simp only [tailPolynomial, Polynomial.eval₂_finsetProd, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_pow,
      Polynomial.eval₂_natCast, map_pow, map_natCast]
    rfl
  rw [hev]
  apply (eq_div_iff hT).2
  have hf := congrArg (fun q : ℚ[X] => q.eval₂ (algebraMap ℚ ℝ) (y^2))
    (kernelNumerator_partial_fraction p (i+j))
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_finsetProd, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_pow, Polynomial.eval₂_natCast,
    map_pow, map_natCast] at hf
  rw [hev, kernelRatElem_polyPart_eq_quotient p k i j] at hf
  rw [hf]
  unfold resolvedKernel
  rw [add_mul, Finset.sum_mul]
  have heq (q : ℚ[X]) : Real.evalQ q (y^2) =
      q.eval₂ (algebraMap ℚ ℝ) (y^2) := by
    simp [Real.evalQ, Real.realPolynomial, Polynomial.eval_map]
    rfl
  rw [heq]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a ∈ s := ha
  have hd : y^2 + (a:ℝ)^2 ≠ 0 := by positivity
  rw [kernelRatElem_residue_eq p k i j a ha]
  change (↑(Real.residue (toParameters p k) i j a) / (y^2+(a:ℝ)^2)) * T =
    ↑(Real.residue (toParameters p k) i j a) * ∏ b ∈ s.erase a, (y^2+(b:ℝ)^2)
  rw [show T = (y^2+(a:ℝ)^2) * ∏ b ∈ s.erase a, (y^2+(b:ℝ)^2) from
    (Finset.mul_prod_erase s _ ha').symm]
  field_simp

open Zetahyperbolic Zetahyperbolic.ManuscriptCompatibility in
theorem resolvedKernel_eq_weighted (p : HankelParams) (k i j : ℕ) {y : ℝ}
    (hy : 0 < y) :
    resolvedKernel (toParameters p k) i j y * density k y =
      y^(2*(i+j)) * ConcreteMoment.weightedDensity (toParameters p k) y := by
  rw [resolvedKernel_eq_fraction p k i j hy]
  have hfac := congrArg (fun q : ℚ[X] => q.eval₂ (algebraMap ℚ ℝ) (y^2))
    (D_poly_factorization p)
  simp only [Polynomial.eval₂_mul] at hfac
  rw [← D_real_eq_eval₂, ← D_real_eq_eval₂, D_tail_eq_tailPolynomial] at hfac
  have hN : D_real p.N (y^2) ≠ 0 := D_real_ne_zero _ (by positivity)
  have hK : D_real p.K (y^2) ≠ 0 := D_real_ne_zero _ (by positivity)
  have htail : (tailPolynomial p.N p.K).eval₂ (algebraMap ℚ ℝ) (y^2) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hfac
    exact hK hfac
  simp only [kernelNumerator, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, ← D_real_eq_eval₂]
  unfold ConcreteMoment.weightedDensity
  simp only [toParameters]
  rw [hfac]
  have hexp : 2*p.m = (2*p.m-1)+1 := by have h := p.hm; omega
  conv_rhs => rw [hexp, pow_succ]
  rw [pow_mul]
  field_simp

open Zetahyperbolic Zetahyperbolic.ManuscriptCompatibility in
theorem gram_eq_weighted_integral_original (p : HankelParams) (k : ℕ)
    (hpole : PoleIntegralIdentity k) (i j : Fin p.h) :
    Real.gram (toParameters p k) (Real.zeta (2*k+1)) i j =
      ∫ y : ℝ in Ioi 0, y^(2*(i.val+j.val)) *
        ConcreteMoment.weightedDensity (toParameters p k) y := by
  change Real.gram (toParameters p k) (Real.zeta (toParameters p k).weight) i j = _
  rw [gram_eq_resolvedKernel_integral (toParameters p k) hpole i j]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  exact resolvedKernel_eq_weighted p k i.val j.val hy

theorem gram_eq_weighted_integral (p : Real.Parameters) (hp : Real.Admissible p)
    (hpole : PoleIntegralIdentity p.k) (i j : Fin p.h) :
    Real.gram p (Real.zeta p.weight) i j =
      ∫ y : ℝ in Ioi 0, y^(2*(i.val+j.val)) * ConcreteMoment.weightedDensity p y := by
  cases p with
  | mk k m N K =>
    let op : Zetahyperbolic.HankelParams := ⟨N, K, m, hp.N_pos, hp.N_lt_K, hp.m_pos⟩
    exact gram_eq_weighted_integral_original op k hpole i j

end ManuscriptChain.Hyperbolic

#print axioms ManuscriptChain.Hyperbolic.integral_polynomial_density
#print axioms ManuscriptChain.Hyperbolic.integrableOn_pole_density
#print axioms ManuscriptChain.Hyperbolic.gram_eq_resolvedKernel_integral

#print axioms ManuscriptChain.Hyperbolic.gram_eq_weighted_integral
