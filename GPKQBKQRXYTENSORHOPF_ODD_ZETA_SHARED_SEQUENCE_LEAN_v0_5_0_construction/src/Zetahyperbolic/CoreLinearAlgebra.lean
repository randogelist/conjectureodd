import Mathlib

/-!
# Core linear-algebra facts used by the Hankel-pencil argument

This module isolates standard finite-dimensional determinant identities from
the manuscript-specific moment-functional and spectral arguments.
-/

namespace Zetahyperbolic

/--
Determinants change by a scalar under independent changes of row and column
bases. This is the algebraic identity underlying the manuscript's
canonical-basis-invariance theorem.
-/
theorem det_change_of_basis
    {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (A G B : Matrix n n R) :
    Matrix.det (A * G * B.transpose) =
      Matrix.det A * Matrix.det G * Matrix.det B := by
  simp only [Matrix.det_mul, Matrix.det_transpose]

/--
If both change-of-basis matrices are invertible, the determinant is multiplied
by a nonzero constant. This is stated as an identity; the manuscript's
primitive-integer-content conclusion is a separate arithmetic step.
-/
theorem det_change_of_basis_nonzero_factor
    {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (A G B : Matrix n n R)
    (hA : IsUnit (Matrix.det A))
    (hB : IsUnit (Matrix.det B)) :
    IsUnit (Matrix.det A * Matrix.det B) := by
  exact hA.mul hB

/--
Determinant consequence of a diagonal congruence factorization. This is the
finite-dimensional algebraic step used after the Lagrange-basis identity
`M = V * diagonal γ * Vᵀ` has been established.
-/
theorem det_conjugated_diagonal
    {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n R) (γ : n → R) :
    Matrix.det (V * Matrix.diagonal γ * V.transpose) =
      (Matrix.det V) ^ 2 * ∏ i, γ i := by
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring


/--
The determinant of a diagonal matrix is the product of its diagonal weights.
This is the scalar determinant identity used in the manuscript after the
Lagrange pole factorization has been established.
-/
theorem det_diagonal_weights
    {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (γ : n → R) :
    Matrix.det (Matrix.diagonal γ) = ∏ i, γ i := by
  simp [Matrix.det_diagonal]

/--
If one diagonal weight in a congruence factorization vanishes, the resulting
matrix pencil coefficient has zero determinant.
-/
theorem det_conjugated_diagonal_eq_zero_of_weight_zero
    {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n R) (γ : n → R) (i : n) (hi : γ i = 0) :
    Matrix.det (V * Matrix.diagonal γ * V.transpose) = 0 := by
  rw [det_conjugated_diagonal]
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
  simp


/--
Polynomial-coefficient instance of the basis-change determinant identity.
The matrices here are over ℚ[X], so the result follows directly from the
generic determinant identity above without needing a separate scalar-map lemma.
-/
theorem det_change_of_basis_polynomial
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B G : Matrix n n (Polynomial ℚ)) :
    Matrix.det (A * G * B.transpose) =
      Matrix.det A * Matrix.det G * Matrix.det B := by
  exact det_change_of_basis A G B


/--
Canonical-basis determinant identity over ℚ[X].  The two basis-change
matrices have rational entries, embedded as constant polynomials.  This is
the determinant-scaling conclusion in the first part of manuscript Theorem 2.4.
The primitive-content normalization is a separate arithmetic statement.
-/
theorem det_change_of_basis_rational_polynomial
    {h : ℕ} (G : Matrix (Fin h) (Fin h) (Polynomial ℚ))
    (A B : Matrix (Fin h) (Fin h) ℚ) :
    Matrix.det (A.map Polynomial.C * G * B.transpose.map Polynomial.C) =
      Polynomial.C (A.det * B.det) * Matrix.det G := by
  rw [Matrix.det_mul, Matrix.det_mul]
  have hA : Matrix.det (A.map Polynomial.C) = Polynomial.C A.det := by
    simpa using (RingHom.map_det Polynomial.C A).symm
  have hB : Matrix.det (B.transpose.map Polynomial.C) = Polynomial.C B.det := by
    calc
      Matrix.det (B.transpose.map Polynomial.C) =
          Polynomial.C (Matrix.det B.transpose) := by
            simpa using (RingHom.map_det Polynomial.C B.transpose).symm
      _ = Polynomial.C B.det := by simp
  rw [hA, hB]
  calc
    Polynomial.C A.det * Matrix.det G * Polynomial.C B.det =
        Polynomial.C A.det * Polynomial.C B.det * Matrix.det G := by ac_rfl
    _ = Polynomial.C (A.det * B.det) * Matrix.det G := by
      rw [← Polynomial.C_mul]



/--
A congruence of a diagonal matrix with nonzero diagonal weights has nonzero
determinant whenever the change-of-basis matrix is invertible. This is the
finite-dimensional nonvanishing step used in the leading-coefficient part of
manuscript Theorem 3.1.
-/
theorem det_conjugated_diagonal_ne_zero
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R] {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n R) (γ : n → R)
    (hV : IsUnit V.det) (hγ : ∀ i, γ i ≠ 0) :
    Matrix.det (V * Matrix.diagonal γ * V.transpose) ≠ 0 := by
  rw [det_conjugated_diagonal]
  apply mul_ne_zero
  · exact pow_ne_zero 2 (IsUnit.ne_zero hV)
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact hγ i

end Zetahyperbolic
