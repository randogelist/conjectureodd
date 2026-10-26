import Mathlib

/-!
# Foundational finite objects

These definitions mirror the elementary arithmetic objects used in the
manuscript. They are deliberately separated from the analytic and spectral
claims so that each layer can be compiled and audited independently.
-/

namespace Zetahyperbolic

/-- The generalized harmonic number H_n^(s), represented exactly in ℚ. -/
def harmonicNumber (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 n, (((j : ℚ) ^ s)⁻¹)

/-- D_m(t) = ∏_{j=1}^m (t + j²), as a polynomial over ℚ. -/
noncomputable def denominatorPolynomial (m : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.Icc 1 m,
    (Polynomial.X + Polynomial.C ((j : ℚ) ^ 2))

/-- The tail product ∏_{N<j≤K}(t+j²), used for the Lagrange pole basis. -/
noncomputable def tailPolynomial (N K : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.Icc (N + 1) K,
    (Polynomial.X + Polynomial.C ((j : ℚ) ^ 2))

/--
The pole value in the order-(2k+1) functional. The intended use has k ≥ 1
and j ≥ 1; the total definition is convenient for Lean's term language.
-/
def oddZetaPoleMoment (k j : ℕ) (X : ℚ) : ℚ :=
  (j : ℚ) ^ (2 * k) * (X - harmonicNumber (2 * k + 1) j)
    + (1 : ℚ) / (2 * j) - (1 : ℚ) / (2 * k)

/-- Difference of pole moments cancels all X-independent terms. -/
theorem oddZetaPoleMoment_sub (k j : ℕ) (X Y : ℚ) :
    oddZetaPoleMoment k j X - oddZetaPoleMoment k j Y =
      (j : ℚ) ^ (2 * k) * (X - Y) := by
  unfold oddZetaPoleMoment
  ring

/-- Translation in X changes the pole moment by its constant slope. -/
theorem oddZetaPoleMoment_add (k j : ℕ) (X d : ℚ) :
    oddZetaPoleMoment k j (X + d) =
      oddZetaPoleMoment k j X + (j : ℚ) ^ (2 * k) * d := by
  unfold oddZetaPoleMoment
  ring


/-- The denominator polynomial vanishes at every negative-square pole it contains. -/
theorem denominatorPolynomial_eval_pole (m a : ℕ)
    (ha : a ∈ Finset.Icc 1 m) :
    Polynomial.eval (-((a : ℚ) ^ 2)) (denominatorPolynomial m) = 0 := by
  classical
  unfold denominatorPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero ha
  simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]

/-- The tail denominator vanishes at each pole in its index interval. -/
theorem tailPolynomial_eval_pole (N K a : ℕ)
    (ha : a ∈ Finset.Icc (N + 1) K) :
    Polynomial.eval (-((a : ℚ) ^ 2)) (tailPolynomial N K) = 0 := by
  classical
  unfold tailPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero ha
  simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]


/--
Product-rule evaluation for the derivative of the tail denominator at a pole.
This is the standard derivative-of-a-finite-product identity used to turn
Lagrange interpolation into the explicit pole-weight formula.
-/
theorem tailPolynomial_derivative_eval_pole (N K a : ℕ)
    (ha : a ∈ Finset.Icc (N + 1) K) :
    Polynomial.eval (-((a : ℚ) ^ 2))
      (Polynomial.derivative (tailPolynomial N K)) =
      ∏ b ∈ (Finset.Icc (N + 1) K).erase a,
        ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
  classical
  unfold tailPolynomial
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single a]
  · simp only [Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.derivative_add, Polynomial.derivative_X,
      Polynomial.derivative_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C]
    simp
    apply Finset.prod_congr rfl
    intro b hb
    ring
  · intro b hb hba
    have hamem : a ∈ (Finset.Icc (N + 1) K).erase b :=
      Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩
    simp only [Polynomial.derivative_add, Polynomial.derivative_X,
      Polynomial.derivative_C, add_zero, one_mul]
    rw [Polynomial.eval_mul]
    rw [Polynomial.eval_prod]
    simp only [Polynomial.eval_one, mul_one]
    apply Finset.prod_eq_zero hamem
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring
  · intro hnot
    exact (hnot ha).elim

/--
The derivative at a pole is nonzero because all the other pole nodes are
distinct. This is the denominator-nonvanishing fact needed to define the
Lagrange basis in the manuscript.
-/
theorem lagrangePoleDenominator_ne_zero (N K a : ℕ)
    (ha : a ∈ Finset.Icc (N + 1) K) :
    Polynomial.eval (-((a : ℚ) ^ 2))
      (Polynomial.derivative (tailPolynomial N K)) ≠ 0 := by
  rw [tailPolynomial_derivative_eval_pole N K a ha]
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hdiff : (b : ℚ) ^ 2 - (a : ℚ) ^ 2 ≠ 0 := by
    intro h
    have hs : (b : ℚ) ^ 2 = (a : ℚ) ^ 2 := sub_eq_zero.mp h
    have hcast : (b : ℚ) = (a : ℚ) := by
      nlinarith [sq_nonneg ((b : ℚ) - (a : ℚ))]
    exact hba (by exact_mod_cast hcast)
  exact hdiff


end Zetahyperbolic
