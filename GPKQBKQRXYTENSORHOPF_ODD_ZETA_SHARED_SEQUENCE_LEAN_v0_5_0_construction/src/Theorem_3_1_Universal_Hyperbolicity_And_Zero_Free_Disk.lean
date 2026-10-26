import Mathlib.Analysis.Matrix.Order
import Theorem_2_4_Canonical_Basis_Invariance
import Definition_2_1_Order_s_Rational_Moment_Functional
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring

/-!
# Theorem 3.1 (Universal hyperbolicity and zero-free disk)

PDF pp. 7-8. The pencil construction and its algebraic identification are proved.
RootFactorization is now constructed from positive definiteness of the base
Gram matrix and nonvanishing of the derivative determinant, using the positive
matrix square root and the Hermitian spectral theorem. Degree, real-rootedness,
and root-separation consequences are proved. Theorem 2.5 proves derivative
nonsingularity for the manuscript family. Its integral identity and Gram
positivity remain open; the quantitative spectral bound is a separate input.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Spectral

structure SymmetricAffinePencil (n : ℕ) where
  center : ℝ
  base : Matrix (Fin n) (Fin n) ℝ
  direction : Matrix (Fin n) (Fin n) ℝ
  base_symmetric : base.IsSymm
  direction_symmetric : direction.IsSymm

namespace SymmetricAffinePencil

variable {n : ℕ} (p : SymmetricAffinePencil n)

def matrixAt (x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  p.base + (x - p.center) • p.direction

def polynomialMatrix : Matrix (Fin n) (Fin n) ℝ[X] :=
  fun i j => C (p.base i j) + (X - C p.center) * C (p.direction i j)

def detPolynomial : ℝ[X] := Matrix.det p.polynomialMatrix

def detValue (x : ℝ) : ℝ := Matrix.det (p.matrixAt x)

def BasePositive : Prop := p.base.PosDef

@[simp] theorem matrixAt_center : p.matrixAt p.center = p.base := by
  simp [matrixAt]

theorem eval_detPolynomial (x : ℝ) : p.detPolynomial.eval x = p.detValue x := by
  unfold detPolynomial detValue
  change (Polynomial.evalRingHom x) (Matrix.det p.polynomialMatrix) = _
  rw [(Polynomial.evalRingHom x).map_det]
  congr 1
  ext i j
  simp [polynomialMatrix, matrixAt]

@[simp] theorem eval_detPolynomial_center :
    p.detPolynomial.eval p.center = Matrix.det p.base := by
  rw [p.eval_detPolynomial]
  simp [detValue]

theorem base_det_ne_zero_of_positive (h : p.BasePositive) : Matrix.det p.base ≠ 0 := by
  exact ((Matrix.isUnit_iff_isUnit_det p.base).mp
    (show p.base.PosDef from h).isUnit).ne_zero

theorem center_nonvanishing_of_positive (h : p.BasePositive) :
    p.detPolynomial.eval p.center ≠ 0 := by
  rw [p.eval_detPolynomial_center]
  exact p.base_det_ne_zero_of_positive h

end SymmetricAffinePencil

end ManuscriptChain.Spectral

namespace ManuscriptChain.Real

theorem numerator_symmetric (p : Parameters) (i j : ℕ) :
    numerator p i j = numerator p j i := by
  simp only [numerator, Nat.add_comm]

theorem entryA_symmetric (p : Parameters) (i j : ℕ) :
    entryA p i j = entryA p j i := by
  simp only [entryA, quotient, residue, numerator_symmetric p i j]

theorem entryM_symmetric (p : Parameters) (i j : ℕ) :
    entryM p i j = entryM p j i := by
  simp only [entryM, residue, numerator_symmetric p i j]

@[simp] theorem evalQ_pencil (p : Parameters) (i j : Fin p.h) (x : ℝ) :
    evalQ (pencil p i j) x =
      (entryA p i.val j.val : ℝ) + (entryM p i.val j.val : ℝ) * x := by
  simp [evalQ, realPolynomial, pencil]

theorem gram_symmetric (p : Parameters) (x : ℝ) : (gram p x).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, gram, evalQ_pencil,
    entryA_symmetric p j.val i.val, entryM_symmetric p j.val i.val]

theorem derivativeMatrix_symmetric (p : Parameters) : (derivativeMatrix p).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, derivativeMatrix, entryM_symmetric p j.val i.val]

def manuscriptPencil (p : Parameters) : Spectral.SymmetricAffinePencil p.h where
  center := zeta p.weight
  base := gram p (zeta p.weight)
  direction := derivativeMatrix p
  base_symmetric := gram_symmetric p _
  direction_symmetric := derivativeMatrix_symmetric p

@[simp] theorem manuscriptPencil_center (p : Parameters) :
    (manuscriptPencil p).center = zeta p.weight := rfl

theorem manuscriptPencil_matrixAt (p : Parameters) (x : ℝ) :
    (manuscriptPencil p).matrixAt x = gram p x := by
  ext i j
  simp only [Spectral.SymmetricAffinePencil.matrixAt, manuscriptPencil,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, gram, evalQ_pencil,
    derivativeMatrix]
  ring

theorem manuscriptPencil_polynomialMatrix (p : Parameters) :
    (manuscriptPencil p).polynomialMatrix =
      (pencil p).map (Polynomial.mapRingHom (Rat.castHom ℝ)) := by
  apply Matrix.ext
  intro i j
  simp [Spectral.SymmetricAffinePencil.polynomialMatrix, manuscriptPencil,
    gram, evalQ, realPolynomial, derivativeMatrix, pencil, Polynomial.mapRingHom]
  ring

theorem manuscriptPencil_detPolynomial (p : Parameters) :
    (manuscriptPencil p).detPolynomial = realPolynomial (delta p) := by
  unfold Spectral.SymmetricAffinePencil.detPolynomial
  rw [manuscriptPencil_polynomialMatrix]
  exact ((Polynomial.mapRingHom (Rat.castHom ℝ)).map_det (pencil p)).symm

theorem delta_eval_eq_det_gram (p : Parameters) (x : ℝ) :
    evalQ (delta p) x = Matrix.det (gram p x) := by
  rw [evalQ, ← manuscriptPencil_detPolynomial,
    Spectral.SymmetricAffinePencil.eval_detPolynomial]
  simp only [Spectral.SymmetricAffinePencil.detValue, manuscriptPencil_matrixAt]

theorem delta_nonzero_of_positive (p : Parameters)
    (h : (gram p (zeta p.weight)).PosDef) :
    evalQ (delta p) (zeta p.weight) ≠ 0 := by
  have hc := (manuscriptPencil p).center_nonvanishing_of_positive h
  simpa only [manuscriptPencil_detPolynomial, manuscriptPencil_center, evalQ] using hc

end ManuscriptChain.Real

namespace ManuscriptChain.Spectral

def spectralFactor (center beta : ℝ) : ℝ[X] :=
  1 + (X - C center) * C beta

structure RootFactorization {n : ℕ} (p : SymmetricAffinePencil n) where
  beta : Fin n → ℝ
  beta_ne_zero : ∀ i, beta i ≠ 0
  base_det_ne_zero : Matrix.det p.base ≠ 0
  factorization : p.detPolynomial =
    C (Matrix.det p.base) * ∏ i, spectralFactor p.center (beta i)

theorem linear_factor_eq_zero_iff {K : Type*} [Field K]
    (center beta x : K) (hb : beta ≠ 0) :
    1 + (x - center) * beta = 0 ↔ x = center - beta⁻¹ := by
  constructor
  · intro h
    have hmul : (x - center) * beta = -1 := by
      calc
        (x - center) * beta = (1 + (x - center) * beta) - 1 := by ring
        _ = -1 := by rw [h]; ring
    have hdiff : x - center = -(beta⁻¹) := by
      calc
        x - center = ((x - center) * beta) * beta⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hb, mul_one]
        _ = -(beta⁻¹) := by rw [hmul]; ring
    calc
      x = (x - center) + center := by ring
      _ = -(beta⁻¹) + center := by rw [hdiff]
      _ = center - beta⁻¹ := by ring
  · intro h
    rw [h]
    calc
      1 + (center - beta⁻¹ - center) * beta = 1 - beta⁻¹ * beta := by ring
      _ = 0 := by rw [inv_mul_cancel₀ hb]; ring

@[simp] theorem eval_spectralFactor (center beta x : ℝ) :
    (spectralFactor center beta).eval x = 1 + (x - center) * beta := by
  simp [spectralFactor]

theorem spectralFactor_ne_zero (center beta : ℝ) : spectralFactor center beta ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval center) h
  simp at he

theorem natDegree_spectralFactor (center beta : ℝ) (hb : beta ≠ 0) :
    (spectralFactor center beta).natDegree = 1 := by
  have heq : spectralFactor center beta = C beta * X + C (1 - center * beta) := by
    simp only [spectralFactor, map_sub, map_one, map_mul]
    ring
  rw [heq]
  exact Polynomial.natDegree_linear hb

namespace RootFactorization

variable {n : ℕ} {p : SymmetricAffinePencil n} (c : RootFactorization p)

include c

def root (i : Fin n) : ℝ := p.center - (c.beta i)⁻¹

theorem eval_eq (x : ℝ) :
    p.detPolynomial.eval x = Matrix.det p.base *
      ∏ i, (1 + (x - p.center) * c.beta i) := by
  rw [c.factorization]
  simp [Polynomial.eval_prod]

theorem center_nonvanishing : p.detPolynomial.eval p.center ≠ 0 := by
  simpa using c.base_det_ne_zero

theorem determinant_center_nonvanishing : p.detValue p.center ≠ 0 := by
  simpa [SymmetricAffinePencil.detValue] using c.base_det_ne_zero

theorem polynomial_ne_zero : p.detPolynomial ≠ 0 := by
  intro h
  apply c.center_nonvanishing
  rw [h]
  simp

theorem natDegree_eq : p.detPolynomial.natDegree = n := by
  rw [c.factorization, Polynomial.natDegree_C_mul c.base_det_ne_zero]
  have hprod := Polynomial.natDegree_prod (s := Finset.univ)
    (fun i : Fin n => spectralFactor p.center (c.beta i))
    (fun i _ => spectralFactor_ne_zero p.center (c.beta i))
  simpa [natDegree_spectralFactor, c.beta_ne_zero] using hprod

theorem eval_eq_zero_iff (x : ℝ) :
    p.detPolynomial.eval x = 0 ↔ ∃ i, x = c.root i := by
  rw [c.eval_eq, mul_eq_zero]
  simp only [c.base_det_ne_zero, false_or, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (linear_factor_eq_zero_iff p.center (c.beta i) x (c.beta_ne_zero i)).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (linear_factor_eq_zero_iff p.center (c.beta i) x (c.beta_ne_zero i)).mpr hi⟩

theorem eval_root (i : Fin n) : p.detPolynomial.eval (c.root i) = 0 :=
  (c.eval_eq_zero_iff _).mpr ⟨i, rfl⟩

theorem root_ne_center (i : Fin n) : c.root i ≠ p.center := by
  intro h
  exact c.center_nonvanishing (h ▸ c.eval_root i)

theorem complex_root_location (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    ∃ i, z = (c.root i : ℂ) := by
  have heval : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial =
      ((Matrix.det p.base : ℝ) : ℂ) * ∏ i, (1 + (z - (p.center : ℂ)) * (c.beta i : ℂ)) := by
    rw [c.factorization]
    simp [spectralFactor, Polynomial.eval₂_finsetProd]
  rw [heval] at hz
  have hd : ((Matrix.det p.base : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr c.base_det_ne_zero
  have hp := (mul_eq_zero.mp hz).resolve_left hd
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
  refine ⟨i, ?_⟩
  have hb : (c.beta i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (c.beta_ne_zero i)
  have hx := (linear_factor_eq_zero_iff (p.center : ℂ) (c.beta i : ℂ) z hb).mp hi
  simpa [root] using hx

theorem complex_root_im_zero (z : ℂ)
    (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) : z.im = 0 := by
  obtain ⟨i, rfl⟩ := c.complex_root_location z hz
  simp

theorem root_distance (i : Fin n) : |c.root i - p.center| = 1 / |c.beta i| := by
  have heq : c.root i - p.center = -((c.beta i)⁻¹) := by
    simp only [root]
    ring
  rw [heq, abs_neg, abs_inv, one_div]

theorem root_distance_lower_bound (bound : ℝ)
    (hbound : ∀ i, |c.beta i| ≤ bound) (i : Fin n) :
    1 / bound ≤ |c.root i - p.center| := by
  rw [c.root_distance]
  exact one_div_le_one_div_of_le (abs_pos.mpr (c.beta_ne_zero i)) (hbound i)

theorem eval_ne_zero_of_distance_lt (bound x : ℝ)
    (hbound : ∀ i, |c.beta i| ≤ bound)
    (hx : |x - p.center| < 1 / bound) : p.detPolynomial.eval x ≠ 0 := by
  intro hz
  obtain ⟨i, rfl⟩ := (c.eval_eq_zero_iff x).mp hz
  exact (not_lt_of_ge (c.root_distance_lower_bound bound hbound i)) hx

end RootFactorization

end ManuscriptChain.Spectral

namespace ManuscriptChain.Real

theorem delta_real_natDegree (p : Parameters)
    (c : Spectral.RootFactorization (manuscriptPencil p)) :
    (realPolynomial (delta p)).natDegree = p.h := by
  rw [← manuscriptPencil_detPolynomial]
  exact c.natDegree_eq

end ManuscriptChain.Real

open scoped BigOperators MatrixOrder
open Matrix Polynomial

namespace ManuscriptChain.Spectral

theorem det_one_add_smul_of_hermitian {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsHermitian) (t : ℝ) :
    Matrix.det (1 + t • B) = ∏ i, (1 + t * hB.eigenvalues i) := by
  let e := Unitary.conjStarAlgAut ℝ _ hB.eigenvectorUnitary
  have he : B = e (diagonal hB.eigenvalues) := by
    simpa [e, Function.comp_def] using hB.spectral_theorem
  have hmap : 1 + t • B = e (1 + t • diagonal hB.eigenvalues) := by
    simp only [map_add, map_one, map_smul, ← he]
  rw [hmap]
  change Matrix.det (e (1 + t • diagonal hB.eigenvalues)) = _
  dsimp only [e]
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_comm, ← Matrix.mul_assoc]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul]
  have hd : (1 : Matrix (Fin n) (Fin n) ℝ) + t • diagonal hB.eigenvalues =
      diagonal (fun i => 1 + t * hB.eigenvalues i) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.diagonal]
  rw [hd, Matrix.det_diagonal]

theorem rootFactorization_nonempty_of_posDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0) :
    Nonempty (RootFactorization p) := by
  let S := CFC.sqrt p.base
  have hSsq : S * S = p.base := by
    simpa [S, sq] using CFC.sq_sqrt p.base positive.posSemidef.nonneg
  have hSsymm : S.IsHermitian :=
    (CFC.sqrt_nonneg p.base).posSemidef.isHermitian
  have hbase : Matrix.det p.base ≠ 0 := ne_of_gt positive.det_pos
  have hSdet : Matrix.det S ≠ 0 := by
    have h := congrArg Matrix.det hSsq
    rw [Matrix.det_mul] at h
    intro hz
    simp [hz] at h
    exact hbase h.symm
  have hSunit : IsUnit (Matrix.det S) := isUnit_iff_ne_zero.mpr hSdet
  have hSinvdet : Matrix.det (S⁻¹) ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det S hSunit).ne_zero
  let B := S⁻¹ * p.direction * S⁻¹
  have hBsymm : B.IsHermitian := by
    have h := Matrix.isHermitian_conjTranspose_mul_mul (S⁻¹)
      (Matrix.isHermitian_iff_isSymm.mpr p.direction_symmetric)
    simpa only [hSsymm.inv.eq] using h
  have hBdet : Matrix.det B ≠ 0 := by
    dsimp only [B]
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hSinvdet direction_nonzero) hSinvdet
  have hconj : S * B * S = p.direction := by
    dsimp only [B]
    calc
      S * (S⁻¹ * p.direction * S⁻¹) * S =
          (S * S⁻¹) * p.direction * (S⁻¹ * S) := by
            simp only [Matrix.mul_assoc]
      _ = p.direction := by
        rw [Matrix.mul_nonsing_inv S hSunit, Matrix.nonsing_inv_mul S hSunit]
        simp
  have hpencil (x : ℝ) : p.matrixAt x = S * (1 + (x - p.center) • B) * S := by
    calc
      p.matrixAt x = S * S + (x - p.center) • (S * B * S) := by
        rw [hSsq, hconj]
        rfl
      _ = S * (1 + (x - p.center) • B) * S := by
        simp [Matrix.mul_add, Matrix.add_mul]
  refine ⟨{
    beta := hBsymm.eigenvalues
    beta_ne_zero := ?_
    base_det_ne_zero := hbase
    factorization := ?_
  }⟩
  · intro i hi
    apply hBdet
    rw [hBsymm.det_eq_prod_eigenvalues]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa using hi
  · apply Polynomial.funext
    intro x
    rw [p.eval_detPolynomial, SymmetricAffinePencil.detValue, hpencil]
    rw [Matrix.det_mul, Matrix.det_mul]
    have hdetbase : Matrix.det S * Matrix.det S = Matrix.det p.base := by
      rw [← Matrix.det_mul, hSsq]
    rw [det_one_add_smul_of_hermitian B hBsymm]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      eval_spectralFactor]
    calc
      Matrix.det S * (∏ i, (1 + (x - p.center) * hBsymm.eigenvalues i)) *
          Matrix.det S = (Matrix.det S * Matrix.det S) *
            ∏ i, (1 + (x - p.center) * hBsymm.eigenvalues i) := by ring
      _ = _ := by rw [hdetbase]

noncomputable def rootFactorizationOfPosDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0) : RootFactorization p :=
  Classical.choice (rootFactorization_nonempty_of_posDef p positive direction_nonzero)

theorem theorem_3_1_degree_of_posDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0) :
    p.detPolynomial.natDegree = n :=
  (rootFactorizationOfPosDef p positive direction_nonzero).natDegree_eq

theorem theorem_3_1_hyperbolicity_of_posDef {n : ℕ}
    (p : SymmetricAffinePencil n) (positive : p.base.PosDef)
    (direction_nonzero : Matrix.det p.direction ≠ 0)
    (z : ℂ) (hz : Polynomial.eval₂ (algebraMap ℝ ℂ) z p.detPolynomial = 0) :
    z.im = 0 :=
  (rootFactorizationOfPosDef p positive direction_nonzero).complex_root_im_zero z hz

end ManuscriptChain.Spectral
