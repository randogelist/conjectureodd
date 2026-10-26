import Theorem_2_4_Canonical_Basis_Invariance
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Theorem 2.5 (Lagrange pole diagonalization)

PDF pp. 6-7. For the actual residue-defined pencil, this file proves distinct
pole nodes, nonzero pole weights, the exact Vandermonde factorization of its
slope matrix, and nonsingularity of the rational and real slope matrices.
The transformed pencil has constant rational off-diagonal entries and diagonal
entries gamma_a * (X - H_a) + r_a with nonzero gamma_a. The separate Lagrange
interpolation polynomials and their functional representation are not constructed.
It also proves that the determinant polynomial is nonzero and has degree h,
with leading coefficient equal to the slope determinant. These algebraic
results hold for every Parameters value, including the empty-matrix case.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.PoleDiagonalization

def poleIndex (p : Real.Parameters) (a : Fin p.h) : ℕ := p.N + 1 + a.val

def poleNode (p : Real.Parameters) (a : Fin p.h) : ℚ := -(poleIndex p a : ℚ) ^ 2

def poleWeight (p : Real.Parameters) (a : Fin p.h) : ℚ :=
  (Real.D p.N).eval (poleNode p a) ^ (2 * p.m - 1) /
    (derivative (Real.tailD p)).eval (poleNode p a) * (poleIndex p a : ℚ) ^ (2 * p.k)

def poleVandermonde (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℚ :=
  fun i a => poleNode p a ^ i.val

theorem poleIndex_mem (p : Real.Parameters) (a : Fin p.h) :
    poleIndex p a ∈ Finset.Icc (p.N + 1) p.K := by
  have ha := a.isLt
  dsimp [Real.Parameters.h] at ha
  simp only [Finset.mem_Icc, poleIndex]
  omega

theorem poleIndex_pos (p : Real.Parameters) (a : Fin p.h) : 0 < poleIndex p a := by
  simp only [poleIndex]
  omega

theorem poleNode_injective (p : Real.Parameters) : Function.Injective (poleNode p) := by
  intro a b hab
  have hsq : (poleIndex p a : ℚ) ^ 2 = (poleIndex p b : ℚ) ^ 2 := by
    simpa only [poleNode, neg_inj] using hab
  have heq := (sq_eq_sq₀ (show (0 : ℚ) ≤ poleIndex p a by positivity)
    (show (0 : ℚ) ≤ poleIndex p b by positivity)).mp hsq
  have hi : poleIndex p a = poleIndex p b := by exact_mod_cast heq
  apply Fin.ext
  dsimp [poleIndex] at hi
  omega

theorem D_eval_ne_zero_of_lt (N a : ℕ) (ha : N < a) :
    (Real.D N).eval (-(a : ℚ) ^ 2) ≠ 0 := by
  simp only [Real.D, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjN : j < N := Finset.mem_range.mp hj
  have hja : ((j + 1 : ℕ) : ℚ) < (a : ℚ) := by exact_mod_cast (show j + 1 < a by omega)
  have hj0 : (0 : ℚ) ≤ ((j + 1 : ℕ) : ℚ) := by positivity
  have ha0 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast (show 0 < a by omega)
  nlinarith

theorem tailD_derivative_eval (p : Real.Parameters) (a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    (derivative (Real.tailD p)).eval (-(a : ℚ) ^ 2) =
      ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a, ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
  have hfactor : Real.tailD p = (X + C ((a : ℚ) ^ 2)) *
      ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a, (X + C ((b : ℚ) ^ 2)) := by
    exact (Finset.mul_prod_erase (Finset.Icc (p.N + 1) p.K)
      (fun b => (X + C ((b : ℚ) ^ 2) : ℚ[X])) ha).symm
  rw [hfactor, derivative_mul, derivative_add, derivative_X, derivative_C]
  simp [Polynomial.eval_prod, sub_eq_add_neg, add_comm]

theorem tailD_derivative_eval_ne_zero (p : Real.Parameters) (a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    (derivative (Real.tailD p)).eval (-(a : ℚ) ^ 2) ≠ 0 := by
  rw [tailD_derivative_eval p a ha]
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  intro heq
  have hsq : (b : ℚ) ^ 2 = (a : ℚ) ^ 2 := sub_eq_zero.mp heq
  have heq := (sq_eq_sq₀ (show (0 : ℚ) ≤ b by positivity)
    (show (0 : ℚ) ≤ a by positivity)).mp hsq
  exact hba (by exact_mod_cast heq)

theorem poleWeight_ne_zero (p : Real.Parameters) (a : Fin p.h) : poleWeight p a ≠ 0 := by
  have hmem := poleIndex_mem p a
  have hD : (Real.D p.N).eval (poleNode p a) ≠ 0 :=
    D_eval_ne_zero_of_lt p.N (poleIndex p a) (by have h := (Finset.mem_Icc.mp hmem).1; omega)
  have ht : (derivative (Real.tailD p)).eval (poleNode p a) ≠ 0 :=
    tailD_derivative_eval_ne_zero p (poleIndex p a) hmem
  have ha : (poleIndex p a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (poleIndex_pos p a))
  exact mul_ne_zero (div_ne_zero (pow_ne_zero _ hD) ht) (pow_ne_zero _ ha)

theorem sum_tail_eq_fin (p : Real.Parameters) (f : ℕ → ℚ) :
    (∑ a ∈ Finset.Icc (p.N + 1) p.K, f a) =
      ∑ a : Fin p.h, f (poleIndex p a) := by
  have hi : Finset.Icc (p.N + 1) p.K = Finset.Ico (p.N + 1) (p.K + 1) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hi, Finset.sum_Ico_eq_sum_range]
  simpa [poleIndex, Real.Parameters.h] using
    (Fin.sum_univ_eq_sum_range (fun a => f (p.N + 1 + a)) p.h).symm

def rationalDerivativeMatrix (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℚ :=
  fun i j => Real.entryM p i.val j.val

theorem entryM_eq_sum_poleWeight (p : Real.Parameters) (i j : Fin p.h) :
    Real.entryM p i.val j.val =
      ∑ a : Fin p.h, poleVandermonde p i a * poleWeight p a * poleVandermonde p j a := by
  rw [Real.entryM, sum_tail_eq_fin]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Real.residue, Real.numerator, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, poleVandermonde, poleWeight, poleNode, pow_add]
  ring

theorem rationalDerivativeMatrix_factorization (p : Real.Parameters) :
    rationalDerivativeMatrix p =
      poleVandermonde p * Matrix.diagonal (poleWeight p) * (poleVandermonde p).transpose := by
  ext i j
  rw [rationalDerivativeMatrix, entryM_eq_sum_poleWeight]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

theorem rationalDerivativeMatrix_det (p : Real.Parameters) :
    (rationalDerivativeMatrix p).det =
      (poleVandermonde p).det ^ 2 * ∏ a : Fin p.h, poleWeight p a := by
  rw [rationalDerivativeMatrix_factorization, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_transpose]
  ring

theorem poleVandermonde_eq (p : Real.Parameters) :
    poleVandermonde p = (Matrix.vandermonde (poleNode p)).transpose := rfl

theorem rationalDerivativeMatrix_det_product (p : Real.Parameters) :
    (rationalDerivativeMatrix p).det =
      (∏ a : Fin p.h, ∏ b ∈ Finset.Ioi a, (poleNode p b - poleNode p a)) ^ 2 *
        ∏ a : Fin p.h, poleWeight p a := by
  rw [rationalDerivativeMatrix_det, poleVandermonde_eq, Matrix.det_transpose,
    Matrix.det_vandermonde]

theorem poleVandermonde_det_ne_zero (p : Real.Parameters) :
    (poleVandermonde p).det ≠ 0 := by
  rw [poleVandermonde_eq, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr (poleNode_injective p)

theorem rationalDerivativeMatrix_det_ne_zero (p : Real.Parameters) :
    (rationalDerivativeMatrix p).det ≠ 0 := by
  rw [rationalDerivativeMatrix_det]
  exact mul_ne_zero (pow_ne_zero _ (poleVandermonde_det_ne_zero p))
    (Finset.prod_ne_zero_iff.mpr fun a _ => poleWeight_ne_zero p a)

theorem derivativeMatrix_det_ne_zero (p : Real.Parameters) :
    (Real.derivativeMatrix p).det ≠ 0 := by
  have h : ((rationalDerivativeMatrix p).det : ℝ) ≠ 0 := by
    exact_mod_cast rationalDerivativeMatrix_det_ne_zero p
  rw [Rat.cast_det] at h
  exact h

def rationalConstantMatrix (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℚ :=
  fun i j => Real.entryA p i.val j.val

theorem pencil_eq_X_smul_add (p : Real.Parameters) :
    Real.pencil p = (X : ℚ[X]) • (rationalDerivativeMatrix p).map C +
      (rationalConstantMatrix p).map C := by
  ext i j
  simp only [Real.pencil, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    rationalDerivativeMatrix, rationalConstantMatrix, smul_eq_mul]
  simp only [add_comm, mul_comm]

theorem delta_coeff_dimension (p : Real.Parameters) :
    (Real.delta p).coeff p.h = (rationalDerivativeMatrix p).det := by
  rw [Real.delta, pencil_eq_X_smul_add]
  simpa using Polynomial.coeff_det_X_add_C_card
    (rationalDerivativeMatrix p) (rationalConstantMatrix p)

theorem delta_ne_zero (p : Real.Parameters) : Real.delta p ≠ 0 := by
  intro hzero
  have h := delta_coeff_dimension p
  rw [hzero, Polynomial.coeff_zero] at h
  exact rationalDerivativeMatrix_det_ne_zero p h.symm

theorem delta_natDegree (p : Real.Parameters) : (Real.delta p).natDegree = p.h := by
  apply Nat.le_antisymm
  · rw [Real.delta, pencil_eq_X_smul_add]
    simpa using Polynomial.natDegree_det_X_add_C_le
      (rationalDerivativeMatrix p) (rationalConstantMatrix p)
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [delta_coeff_dimension]
    exact rationalDerivativeMatrix_det_ne_zero p

theorem delta_leadingCoeff (p : Real.Parameters) :
    (Real.delta p).leadingCoeff = (rationalDerivativeMatrix p).det := by
  rw [Polynomial.leadingCoeff, delta_natDegree, delta_coeff_dimension]


def poleDiagonalPencil (p : Real.Parameters) :
    Matrix (Fin p.h) (Fin p.h) ℚ[X] :=
  BasisInvariance.changeBasisPencil (Real.pencil p)
    (poleVandermonde p)⁻¹ (poleVandermonde p)⁻¹

def poleConstantMatrix (p : Real.Parameters) : Matrix (Fin p.h) (Fin p.h) ℚ :=
  (poleVandermonde p)⁻¹ * rationalConstantMatrix p * ((poleVandermonde p)⁻¹).transpose

theorem pole_slope_diagonal (p : Real.Parameters) :
    (poleVandermonde p)⁻¹ * rationalDerivativeMatrix p *
      ((poleVandermonde p)⁻¹).transpose = Matrix.diagonal (poleWeight p) := by
  let V := poleVandermonde p
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.mpr (poleVandermonde_det_ne_zero p)
  have hright : V.transpose * (V⁻¹).transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul V hunit, Matrix.transpose_one]
  rw [rationalDerivativeMatrix_factorization]
  change V⁻¹ * (V * Matrix.diagonal (poleWeight p) * V.transpose) * (V⁻¹).transpose = _
  calc
    V⁻¹ * (V * Matrix.diagonal (poleWeight p) * V.transpose) * (V⁻¹).transpose =
        (V⁻¹ * V) * Matrix.diagonal (poleWeight p) * (V.transpose * (V⁻¹).transpose) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal (poleWeight p) := by
      rw [Matrix.nonsing_inv_mul V hunit, hright]
      simp

theorem poleDiagonalPencil_eq (p : Real.Parameters) :
    poleDiagonalPencil p = (poleConstantMatrix p).map C +
      Matrix.diagonal (fun a => C (poleWeight p a) * X) := by
  have hconstant :
      ((poleVandermonde p)⁻¹).map C * (rationalConstantMatrix p).map C *
          (((poleVandermonde p)⁻¹).map C).transpose = (poleConstantMatrix p).map C := by
    simp only [poleConstantMatrix, Matrix.map_mul, Matrix.transpose_map]
  have hslope :
      ((poleVandermonde p)⁻¹).map C * (rationalDerivativeMatrix p).map C *
          (((poleVandermonde p)⁻¹).map C).transpose =
        (Matrix.diagonal (poleWeight p)).map C := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
      pole_slope_diagonal]
  rw [poleDiagonalPencil, BasisInvariance.changeBasisPencil, pencil_eq_X_smul_add]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconstant, hslope, add_comm]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases h : i = j
  · simp only [h, ite_true]
    rw [mul_comm (X : ℚ[X])]
  · simp only [h, ite_false, map_zero, mul_zero]

theorem poleDiagonalPencil_off_diagonal (p : Real.Parameters) (a b : Fin p.h)
    (hab : a ≠ b) :
    poleDiagonalPencil p a b = C (poleConstantMatrix p a b) := by
  rw [poleDiagonalPencil_eq]
  simp [hab, Matrix.diagonal]

theorem poleDiagonalPencil_diagonal (p : Real.Parameters) (a : Fin p.h) :
    poleDiagonalPencil p a a = C (poleConstantMatrix p a a) + C (poleWeight p a) * X := by
  rw [poleDiagonalPencil_eq]
  simp

def poleDiagonalRemainder (p : Real.Parameters) (a : Fin p.h) : ℚ :=
  poleConstantMatrix p a a + poleWeight p a * Real.harmonic p.weight (poleIndex p a)

theorem poleDiagonalPencil_diagonal_harmonic (p : Real.Parameters) (a : Fin p.h) :
    poleDiagonalPencil p a a =
      C (poleWeight p a) * (X - C (Real.harmonic p.weight (poleIndex p a))) +
        C (poleDiagonalRemainder p a) := by
  rw [poleDiagonalPencil_diagonal]
  simp only [poleDiagonalRemainder, map_add, map_mul]
  ring

theorem theorem_2_5_lagrange_pole_diagonalization (p : Real.Parameters) :
    (∀ a b : Fin p.h, a ≠ b →
      poleDiagonalPencil p a b = C (poleConstantMatrix p a b)) ∧
    (∀ a : Fin p.h,
      poleDiagonalPencil p a a =
        C (poleWeight p a) * (X - C (Real.harmonic p.weight (poleIndex p a))) +
          C (poleDiagonalRemainder p a) ∧ poleWeight p a ≠ 0) := by
  exact ⟨poleDiagonalPencil_off_diagonal p,
    fun a => ⟨poleDiagonalPencil_diagonal_harmonic p a, poleWeight_ne_zero p a⟩⟩

end ManuscriptChain.PoleDiagonalization

namespace ManuscriptChain.BasisInvariance

/-- The manuscript pencil is nonzero by Theorem 2.5, so only invertibility of
both changes of basis is required for the constructed primitive invariance. -/
theorem theorem_2_4_constructed_for_manuscript (p : Real.Parameters)
    (A B : Matrix (Fin p.h) (Fin p.h) ℚ)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) :
    let n₀ := primitiveNormalization (Real.delta p) (PoleDiagonalization.delta_ne_zero p)
    let nAB := primitiveNormalization
      (Matrix.det (changeBasisPencil (Real.pencil p) A B))
      ((det_changeBasisPencil_ne_zero_iff (Real.pencil p) A B hA hB).mpr
        (PoleDiagonalization.delta_ne_zero p))
    nAB.polynomial = n₀.polynomial ∨ nAB.polynomial = -n₀.polynomial :=
  theorem_2_4_constructed_canonical_basis_invariance p A B hA hB
    (PoleDiagonalization.delta_ne_zero p)

end ManuscriptChain.BasisInvariance
