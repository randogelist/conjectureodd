import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Bernoulli
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Definition 2.1 (Order-s rational moment functional)

PDF pp. 3-6. Definitions from Definition 2.1 and the surrounding Section 2
construction: rational moments, residues, the matrix pencil, and its determinant.
This file does not prove the integral identification, Theorem 2.4 (Canonical
basis invariance), or Theorem 2.5 (Lagrange pole diagonalization).
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.Real

structure Parameters where
  k : ℕ
  m : ℕ
  N : ℕ
  K : ℕ
  deriving DecidableEq, Repr

def Parameters.h (p : Parameters) : ℕ := p.K - p.N
def Parameters.weight (p : Parameters) : ℕ := 2 * p.k + 1

structure Admissible (p : Parameters) : Prop where
  k_pos : 0 < p.k
  m_pos : 0 < p.m
  N_pos : 0 < p.N
  N_lt_K : p.N < p.K

def zeta (s : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℝ) ^ s

def harmonic (s n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, 1 / ((j + 1 : ℕ) : ℚ) ^ s

def D (n : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.range n, (X + C (((j + 1 : ℕ) : ℚ) ^ 2))

def tailD (p : Parameters) : ℚ[X] :=
  ∏ a ∈ Finset.Icc (p.N + 1) p.K, (X + C ((a : ℚ) ^ 2))

def numerator (p : Parameters) (i j : ℕ) : ℚ[X] :=
  D p.N ^ (2 * p.m - 1) * X ^ (i + j)

def quotient (p : Parameters) (i j : ℕ) : ℚ[X] :=
  numerator p i j / tailD p

def monomialMoment (k e : ℕ) : ℚ :=
  (-1 : ℚ) ^ e * bernoulli (2 * e + 2) * (Nat.factorial (2 * e + 2 * k + 1) : ℚ) /
    ((Nat.factorial (2 * k) : ℚ) * (Nat.factorial (2 * e + 2) : ℚ))

def polynomialMoment (k : ℕ) (q : ℚ[X]) : ℚ :=
  ∑ e ∈ q.support, q.coeff e * monomialMoment k e

def residue (p : Parameters) (i j a : ℕ) : ℚ :=
  (numerator p i j).eval (-(a : ℚ) ^ 2) /
    (derivative (tailD p)).eval (-(a : ℚ) ^ 2)

def poleConstant (k a : ℕ) : ℚ :=
  -(a : ℚ) ^ (2 * k) * harmonic (2 * k + 1) a +
    1 / (2 * (a : ℚ)) - 1 / (2 * (k : ℚ))

def entryA (p : Parameters) (i j : ℕ) : ℚ :=
  polynomialMoment p.k (quotient p i j) +
    ∑ a ∈ Finset.Icc (p.N + 1) p.K, residue p i j a * poleConstant p.k a

def entryM (p : Parameters) (i j : ℕ) : ℚ :=
  ∑ a ∈ Finset.Icc (p.N + 1) p.K, residue p i j a * (a : ℚ) ^ (2 * p.k)

def pencil (p : Parameters) : Matrix (Fin p.h) (Fin p.h) ℚ[X] :=
  fun i j => C (entryA p i.val j.val) + C (entryM p i.val j.val) * X

def delta (p : Parameters) : ℚ[X] := Matrix.det (pencil p)

def realPolynomial (q : ℚ[X]) : ℝ[X] := q.map (Rat.castHom ℝ)
def evalQ (q : ℚ[X]) (x : ℝ) : ℝ := (realPolynomial q).eval x
def gram (p : Parameters) (x : ℝ) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  fun i j => evalQ (pencil p i j) x
def derivativeMatrix (p : Parameters) : Matrix (Fin p.h) (Fin p.h) ℝ :=
  fun i j => (entryM p i.val j.val : ℝ)

end ManuscriptChain.Real

/-! Convergence and identification of the paper's defining zeta series. -/

namespace ManuscriptChain.Real

theorem zeta_series_summable {s : ℕ} (hs : 1 < s) :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ s) := by
  exact (summable_nat_add_iff 1).mpr (_root_.Real.summable_one_div_nat_pow.mpr hs)

theorem zeta_series_hasSum {s : ℕ} (hs : 1 < s) :
    HasSum (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ s) (zeta s) :=
  (zeta_series_summable hs).hasSum

theorem zeta_eq_riemannZeta {s : ℕ} (hs : 1 < s) :
    (zeta s : ℂ) = riemannZeta (s : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs : 1 < (s : ℂ).re)]
  simp only [zeta, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp [Complex.cpow_natCast]

theorem zeta_eq_riemannZeta_re {s : ℕ} (hs : 1 < s) :
    zeta s = (riemannZeta (s : ℂ)).re := by
  have h := congrArg Complex.re (zeta_eq_riemannZeta hs)
  simpa using h

theorem riemannZeta_nat_im_zero {s : ℕ} (hs : 1 < s) :
    (riemannZeta (s : ℂ)).im = 0 := by
  rw [← zeta_eq_riemannZeta hs]
  rfl

theorem zeta_pos {s : ℕ} (hs : 1 < s) : 0 < zeta s := by
  exact (zeta_series_summable hs).tsum_pos (fun n => by positivity) 0 (by norm_num)

theorem zeta_five_eq_riemannZeta_re :
    zeta 5 = (riemannZeta 5).re :=
  zeta_eq_riemannZeta_re (by norm_num)

end ManuscriptChain.Real

