/-
Copyright (c) 2026 Prince Anand. All rights reserved.

Checked finite algebra preserved from the uploaded manuscript blueprint.
This module contains Section 2's definitions and proof terms, followed by
Vandermonde and derivative-determinant consequences from Section 3.
It does not assert the manuscript's analytic realization, hyperbolicity,
quantitative decay, or irrationality conclusions.
-/

import Mathlib
import Zetahyperbolic.CoreLinearAlgebra
import Zetahyperbolic.Section3Elementary

open scoped BigOperators Matrix Polynomial

namespace Zetahyperbolic

noncomputable section

/-!
# Section 2: Algebraic Structure and Canonical Basis Invariance

This section formalizes the parameters `K > N ≥ 1`, `h = K - N`, the denominator
polynomials `D_m(t)`, generalized harmonic numbers `H_j^{(s)}`, the order-`s`
rational moment functional `μ_X^{(s)}`, the pullback functional `τ_X^{(s)}`,
the Hankel matrix pencil `G_K^{(s)}(X)`, canonical basis invariance (Theorem 2.4),
and the Lagrange pole diagonalization (Theorem 2.5).
-/

/-- Structural parameters `K > N ≥ 1` with `h = K - N`, `α = N / K`, `λ = h / K`. -/
structure HankelParams where
  N : ℕ
  K : ℕ
  m : ℕ
  hN : 1 ≤ N
  hK : N < K
  hm : 1 ≤ m

namespace HankelParams

/-- Dimension `h := K - N` of the Hankel matrix pencil. -/
def h (p : HankelParams) : ℕ := p.K - p.N

/-- Ratio `α := N / K ∈ (0, 1)`. -/
def alpha (p : HankelParams) : ℚ := (p.N : ℚ) / (p.K : ℚ)

/-- Ratio `λ := h / K = 1 - α ∈ (0, 1)`. -/
def lam (p : HankelParams) : ℚ := (p.h : ℚ) / (p.K : ℚ)

lemma h_pos (p : HankelParams) : 0 < p.h :=
  Nat.sub_pos_of_lt p.hK

lemma alpha_add_lam (p : HankelParams) : p.alpha + p.lam = 1 := by
  unfold alpha lam h
  rw [Nat.cast_sub (Nat.le_of_lt p.hK)]
  have hNpos : 0 < p.N := lt_of_lt_of_le (by decide : 0 < 1) p.hN
  have hKpos : 0 < p.K := lt_trans hNpos p.hK
  have hKne : (p.K : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hKpos)
  field_simp [hKne]
  ring

end HankelParams

/-- Equation (2.1): `D_m(t) := ∏_{j=1}^m (t + j^2)` as a polynomial over `ℚ`,
with `D_0(t) = 1`. -/
noncomputable def D_poly (m : ℕ) : ℚ[X] :=
  ∏ j ∈ Finset.Icc 1 m, (Polynomial.X + Polynomial.C ((j : ℚ) ^ 2))

@[simp]
lemma D_poly_zero : D_poly 0 = 1 := by
  simp [D_poly]

/-- Real evaluation of `D_m(t)` at `t : ℝ`. -/
noncomputable def D_real (m : ℕ) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 m, (t + (j : ℝ) ^ 2)

/-- Real denominator evaluation agrees with evaluation of the rational
polynomial over the real numbers. This is the bridge between Section 2's
polynomial products and Section 3's real Gram integrals. -/
lemma D_real_eq_eval₂ (m : ℕ) (t : ℝ) :
    D_real m t = Polynomial.eval₂ (algebraMap ℚ ℝ) t (D_poly m) := by
  classical
  unfold D_real D_poly
  rw [Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp

/-- Positivity of the real denominator product on the positive axis.
This is the denominator-sign input used in the Section 3 Gram integral. -/
lemma D_real_pos (m : ℕ) {t : ℝ} (ht : 0 < t) : 0 < D_real m t := by
  unfold D_real
  apply Finset.prod_pos
  intro j hj
  positivity

/-- The denominator ratio in the Section 3 Gram integrand is positive
for every positive integration variable. -/
lemma D_real_ratio_pos (N K m : ℕ) {y : ℝ} (hy : 0 < y) :
    0 < (D_real N (y ^ 2)) ^ (2 * m) / D_real K (y ^ 2) := by
  have hy2 : 0 < y ^ 2 := by positivity
  apply div_pos
  · exact pow_pos (D_real_pos N hy2) _
  · exact D_real_pos K hy2

/-- The real denominator product never vanishes on the positive axis. -/
lemma D_real_ne_zero (m : ℕ) {t : ℝ} (ht : 0 < t) : D_real m t ≠ 0 :=
  ne_of_gt (D_real_pos m ht)

/-- One-step growth of the real denominator product. -/
lemma D_real_succ (m : ℕ) (t : ℝ) :
    D_real (m + 1) t =
      D_real m t * (t + ((m + 1 : ℕ) : ℝ) ^ 2) := by
  unfold D_real
  rw [Finset.prod_Icc_succ_top (by omega)]

/-- For positive arguments, the denominator product is nondecreasing in its
index. This is a reusable order estimate for Section 3 denominator ratios. -/
lemma D_real_mono (N K : ℕ) (hNK : N ≤ K) {t : ℝ} (ht : 0 < t) :
    D_real N t ≤ D_real K t := by
  induction hNK with
  | refl => rfl
  | @step K hNK ih =>
      rw [D_real_succ]
      have hK : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
      have hKsq : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((K + 1 : ℕ) : ℝ) - 1)]
      have hfactor : (1 : ℝ) ≤ t + ((K + 1 : ℕ) : ℝ) ^ 2 := by
        linarith
      have hD : 0 ≤ D_real K t := le_of_lt (D_real_pos K ht)
      calc
        D_real N t ≤ D_real K t := ih
        _ ≤ D_real K t * (t + ((K + 1 : ℕ) : ℝ) ^ 2) := by
          have hm := mul_le_mul_of_nonneg_left hfactor hD
          simpa using hm

/-- The real denominator product is at least one for positive arguments. -/
lemma D_real_ge_one (m : ℕ) {t : ℝ} (ht : 0 < t) :
    1 ≤ D_real m t := by
  have h := D_real_mono 0 m (Nat.zero_le m) ht
  simpa [D_real] using h

/-- Generalized harmonic number of weight `s`: `H_j^{(s)} := ∑_{ν=1}^j ν^{-s}` (`H_0^{(s)} = 0`). -/
def harmonicWeight (s : ℕ) (j : ℕ) : ℚ :=
  ∑ ν ∈ Finset.Icc 1 j, ((ν : ℚ) ^ s)⁻¹

@[simp]
lemma harmonicWeight_zero (s : ℕ) : harmonicWeight s 0 = 0 := by
  simp [harmonicWeight]

lemma harmonicWeight_succ (s j : ℕ) :
    harmonicWeight s (j + 1) = harmonicWeight s j + (((j + 1 : ℕ) : ℚ) ^ s)⁻¹ := by
  simp [harmonicWeight, Finset.sum_Icc_succ_top]

/-- Definition 2.1, Equation (2.2): Monomial value of the order-`s` (`s = 2k + 1`)
rational moment functional `μ_X^{(s)}(t^e)`.
Note: independent of `X`. -/
def muMonomial (k e : ℕ) : ℚ :=
  ((-1 : ℚ) ^ e * bernoulli (2 * e + 2) * (Nat.factorial (2 * e + 2 * k + 1) : ℚ)) /
    ((Nat.factorial (2 * k) : ℚ) * (Nat.factorial (2 * e + 2) : ℚ))

/-- Definition 2.1, Equation (2.3): Simple pole value `μ_X^{(2k+1)}((t + j^2)^{-1})`
as a degree-1 polynomial in `ℚ[X]`. -/
noncomputable def muPolePoly (k j : ℕ) : ℚ[X] :=
  Polynomial.C ((j : ℚ) ^ (2 * k)) *
      (Polynomial.X - Polynomial.C (harmonicWeight (2 * k + 1) j)) +
    Polynomial.C (1 / (2 * (j : ℚ)) - 1 / (2 * (k : ℚ)))

/-- Evaluation of `μ_X^{(2k+1)}((t + j^2)^{-1})` at a scalar `X : ℝ`. -/
noncomputable def muPoleEval (k j : ℕ) (X : ℝ) : ℝ :=
  (j : ℝ) ^ (2 * k) * (X - (harmonicWeight (2 * k + 1) j : ℝ)) +
    1 / (2 * (j : ℝ)) - 1 / (2 * (k : ℝ))

/-- Representation of rational functions in the domain of `μ_X^{(s)}`:
a polynomial part `P(t) ∈ ℚ[t]` together with finite simple-pole residues `c_j` at `t = -j^2`. -/
structure RatMomentElem where
  polyPart : ℚ[X]
  maxPole : ℕ
  poleRes : ℕ → ℚ

/-- Action of `μ_X^{(2k+1)}` on a decomposed rational function `R(t)`, taking values in `ℚ[X]`. -/
noncomputable def muFunctionalPoly (k : ℕ) (R : RatMomentElem) : ℚ[X] :=
  (∑ e ∈ Finset.range (R.polyPart.natDegree + 1),
      Polynomial.C (R.polyPart.coeff e * muMonomial k e)) +
    ∑ j ∈ Finset.Icc 1 R.maxPole,
      Polynomial.C (R.poleRes j) * muPolePoly k j

/-- The coefficient of X in a simple-pole polynomial is its monomial slope. -/
lemma coeff_C_mul_X_sub_C (a b : ℚ) :
    (Polynomial.C a * (Polynomial.X - Polynomial.C b)).coeff 1 = a := by
  rw [Polynomial.coeff_C_mul]
  simp

/-- The degree-one coefficient of the simple-pole moment polynomial. -/
lemma muPolePoly_coeff_one (k j : ℕ) :
    (muPolePoly k j).coeff 1 = (j : ℚ) ^ (2 * k) := by
  unfold muPolePoly
  rw [Polynomial.coeff_add, coeff_C_mul_X_sub_C]
  simp

/-- The degree-one coefficient of the moment functional is the weighted
sum of simple-pole residues; the polynomial part contributes only constants. -/
lemma muFunctionalPoly_coeff_one (k : ℕ) (R : RatMomentElem) :
    (muFunctionalPoly k R).coeff 1 =
      ∑ j ∈ Finset.Icc 1 R.maxPole, R.poleRes j * (j : ℚ) ^ (2 * k) := by
  simp [muFunctionalPoly, Polynomial.coeff_C_mul, muPolePoly_coeff_one]

/-- Auxiliary index map `d(r)` for `r ∈ ℤ`: `d(r) = r` if `r ≥ 0`, and `-r - 1` if `r < 0`. -/
def dIndex (r : ℤ) : ℕ :=
  if 0 ≤ r then r.toNat else (-r - 1).toNat

/-- Reflection invariance of `d(r)`: `d(-1 - r) = d(r)` for all `r ∈ ℤ` (used in Lemma 2.3). -/
lemma dIndex_reflect (r : ℤ) : dIndex (-1 - r) = dIndex r := by
  unfold dIndex
  split_ifs with h1 h2 h2
  · omega
  · rcases le_iff_eq_or_lt.mp h1 with h1eq | h1lt
    · omega
    · omega
  · omega
  · omega

/-- Full binomial convolution of Bernoulli numbers. The exceptional index
n = 1 is handled explicitly because bernoulli 1 = -1/2 while
bernoulli' 1 = 1/2. -/
lemma bernoulli_binomial_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℚ) * bernoulli i) = bernoulli' n := by
  rw [Finset.sum_range_succ, sum_bernoulli]
  by_cases hn : n = 1
  · subst n
    norm_num [bernoulli_one, bernoulli'_one]
  · simp [hn, bernoulli_eq_bernoulli'_of_ne_one hn]

/-- Equation (2.4): Monomial action of the one-variable pullback functional `τ_X^{(2k+1)}(x^d)`. -/
def tauMonomial (k d : ℕ) : ℚ :=
  if 2 * k - 1 ≤ d then
    ((Nat.factorial d : ℚ) /
      ((Nat.factorial (d - (2 * k - 1)) : ℚ) * (Nat.factorial (2 * k) : ℚ))) *
        bernoulli (d - (2 * k - 1))
  else 0

/-- Factorial form of the Bernoulli monomial weight, rewritten using a
binomial coefficient. This is the convolution-ready form of equation (2.4). -/
lemma tauMonomial_eq_choose (k d : ℕ) (hk : 1 ≤ k) :
    tauMonomial k d =
      if 2 * k - 1 ≤ d then
        ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
          bernoulli (d - (2 * k - 1))
      else 0 := by
  unfold tauMonomial
  split_ifs with hd
  · have hfacNat : Nat.factorial (2 * k) =
        (2 * k) * Nat.factorial (2 * k - 1) := by
      rw [show 2 * k = (2 * k - 1) + 1 by omega, Nat.factorial_succ]
      simp
    have hfac : (Nat.factorial (2 * k) : ℚ) =
        (2 * k : ℚ) * (Nat.factorial (2 * k - 1) : ℚ) := by
      exact_mod_cast hfacNat
    have hchoose :
        (Nat.choose d (2 * k - 1) : ℚ) *
            (Nat.factorial (2 * k - 1) : ℚ) *
            (Nat.factorial (d - (2 * k - 1)) : ℚ) =
          (Nat.factorial d : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hd
    rw [hfac, ← hchoose]
    have h2k : (2 * k : ℚ) ≠ 0 := by positivity
    have hfr : (Nat.factorial (2 * k - 1) : ℚ) ≠ 0 := by positivity
    have hfd : (Nat.factorial (d - (2 * k - 1)) : ℚ) ≠ 0 := by positivity
    field_simp [h2k, hfr, hfd] <;> ring
  · rfl

/-- Binomial convolution of the monomial weights reduces to a single
Bernoulli number at the shifted index. This is the main algebraic reduction
needed for the monomial reflection identity. -/
lemma tauMonomial_binomial_convolution (k d : ℕ) (hk : 1 ≤ k)
    (hd : 2 * k - 1 ≤ d) :
    (∑ i ∈ Finset.range (d + 1),
      (Nat.choose d i : ℚ) * tauMonomial k i) =
      ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
        bernoulli' (d - (2 * k - 1)) := by
  have hsubset : Finset.Ico (2 * k - 1) (d + 1) ⊆ Finset.range (d + 1) := by
    intro i hi
    simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
    omega
  have hzero : ∀ i ∈ Finset.range (d + 1),
      i ∉ Finset.Ico (2 * k - 1) (d + 1) →
      (Nat.choose d i : ℚ) * tauMonomial k i = 0 := by
    intro i hi hnot
    have hiLt : i < 2 * k - 1 := by
      have hiBound : i < d + 1 := Finset.mem_range.mp hi
      by_contra h
      have hir : 2 * k - 1 ≤ i := by omega
      exact hnot (Finset.mem_Ico.mpr ⟨hir, hiBound⟩)
    simp [tauMonomial, Nat.not_le_of_gt hiLt]
  rw [← Finset.sum_subset hsubset hzero]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : d + 1 - (2 * k - 1) = d - (2 * k - 1) + 1 := by omega
  rw [hlen]
  calc
    (∑ i ∈ Finset.range (d - (2 * k - 1) + 1),
        (Nat.choose d ((2 * k - 1) + i) : ℚ) *
          tauMonomial k ((2 * k - 1) + i)) =
      ∑ i ∈ Finset.range (d - (2 * k - 1) + 1),
        ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
          ((Nat.choose (d - (2 * k - 1)) i : ℚ) * bernoulli i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hwt := tauMonomial_eq_choose k ((2 * k - 1) + i) hk
      have hbound : 2 * k - 1 ≤ (2 * k - 1) + i := by omega
      rw [hwt, if_pos hbound]
      have hidx : (2 * k - 1) + i - (2 * k - 1) = i := by omega
      rw [hidx]
      have hchoose :
          Nat.choose d ((2 * k - 1) + i) *
              Nat.choose ((2 * k - 1) + i) (2 * k - 1) =
            Nat.choose d (2 * k - 1) *
              Nat.choose (d - (2 * k - 1)) i := by
        have h := Nat.choose_mul (n := d) (k := (2 * k - 1) + i)
          (s := 2 * k - 1) (by omega)
        rw [hidx] at h
        exact h
      have hchooseQ :
          (Nat.choose d ((2 * k - 1) + i) : ℚ) *
              (Nat.choose ((2 * k - 1) + i) (2 * k - 1) : ℚ) =
            (Nat.choose d (2 * k - 1) : ℚ) *
              (Nat.choose (d - (2 * k - 1)) i : ℚ) := by
        exact_mod_cast hchoose
      calc
        (Nat.choose d ((2 * k - 1) + i) : ℚ) *
            ((Nat.choose ((2 * k - 1) + i) (2 * k - 1) : ℚ) /
              (2 * k : ℚ) * bernoulli i) =
          (((Nat.choose d ((2 * k - 1) + i) : ℚ) *
            (Nat.choose ((2 * k - 1) + i) (2 * k - 1) : ℚ)) /
              (2 * k : ℚ)) * bernoulli i := by ring
        _ = (((Nat.choose d (2 * k - 1) : ℚ) *
            (Nat.choose (d - (2 * k - 1)) i : ℚ)) /
              (2 * k : ℚ)) * bernoulli i := by rw [hchooseQ]
        _ = ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
            ((Nat.choose (d - (2 * k - 1)) i : ℚ) * bernoulli i) := by ring
    _ = ((Nat.choose d (2 * k - 1) : ℚ) / (2 * k : ℚ)) *
        bernoulli' (d - (2 * k - 1)) := by
      rw [← Finset.mul_sum, bernoulli_binomial_sum]

/-- Simple-pole action of `τ_X^{(2k+1)}((x - r)^{-1}) = H_{d(r)}^{(2k+1)} - X` in `ℚ[X]`. -/
noncomputable def tauPolePoly (k : ℕ) (r : ℤ) : ℚ[X] :=
  Polynomial.C (harmonicWeight (2 * k + 1) (dIndex r)) - Polynomial.X

/-- The simple-pole values are invariant under the reflected integer index.
Together with the sign from substituting x ↦ -1-x, this supplies the pole part
of the Section 2 reflection identity. -/
lemma tauPolePoly_reflect (k : ℕ) (r : ℤ) :
    tauPolePoly k (-1 - r) = tauPolePoly k r := by
  simp [tauPolePoly, dIndex_reflect]

/-- Lemma 2.2 (Pullback identity) on monomials `R(t) = t^e`:
`μ_X^{(s)}(t^e) = τ_X^{(s)}((-1)^e x^{2e + 2k + 1})`. -/
theorem pullback_identity_monomial (k e : ℕ) (hk : 1 ≤ k) :
    muMonomial k e = (-1 : ℚ) ^ e * tauMonomial k (2 * e + 2 * k + 1) := by
  unfold muMonomial tauMonomial
  have hcut : 2 * k - 1 ≤ 2 * e + 2 * k + 1 := by omega
  rw [if_pos hcut]
  have hsub : 2 * e + 2 * k + 1 - (2 * k - 1) = 2 * e + 2 := by omega
  rw [hsub]
  ring

lemma affinePoleLeft (a b c : ℚ) :
    Polynomial.C a * (Polynomial.X - Polynomial.C b) + Polynomial.C c =
      Polynomial.C a * Polynomial.X + Polynomial.C (c - a * b) := by
  calc
    _ = Polynomial.C a * Polynomial.X - Polynomial.C (a * b) + Polynomial.C c := by
      rw [mul_sub, Polynomial.C_mul]
    _ = Polynomial.C a * Polynomial.X + (Polynomial.C c - Polynomial.C (a * b)) := by ring
    _ = Polynomial.C a * Polynomial.X + Polynomial.C (c - a * b) := by
      rw [Polynomial.C_sub]

lemma affinePoleRight (a b c : ℚ) :
    Polynomial.C a - Polynomial.C b *
      (Polynomial.C c - Polynomial.X - Polynomial.X) =
      Polynomial.C (2 * b) * Polynomial.X + Polynomial.C (a - b * c) := by
  calc
    _ = Polynomial.C a -
        (Polynomial.C (b * c) - Polynomial.C b * Polynomial.X -
          Polynomial.C b * Polynomial.X) := by
            rw [mul_sub, mul_sub, Polynomial.C_mul]
    _ = Polynomial.C a - Polynomial.C (b * c) +
        Polynomial.C b * Polynomial.X + Polynomial.C b * Polynomial.X := by ring
    _ = Polynomial.C (a - b * c) +
        Polynomial.C b * Polynomial.X + Polynomial.C b * Polynomial.X := by
          rw [Polynomial.C_sub]
    _ = (Polynomial.C b + Polynomial.C b) * Polynomial.X +
        Polynomial.C (a - b * c) := by ring
    _ = Polynomial.C (b + b) * Polynomial.X +
        Polynomial.C (a - b * c) := by rw [Polynomial.C_add]
    _ = Polynomial.C (2 * b) * Polynomial.X +
        Polynomial.C (a - b * c) := by congr 1 <;> ring

/-- Lemma 2.2 (Pullback identity) on simple poles `R(t) = (t + j^2)^{-1}` (`j ≥ 1`):
`μ_X^{(2k+1)}((t + j^2)^{-1}) = -τ_X^{(2k+1)}(x^{2k-1}) - (j^{2k}/2)(τ_X((x-j)^{-1}) + τ_X((x+j)^{-1}))`. -/
theorem pullback_identity_pole (k j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    muPolePoly k j =
      Polynomial.C (-tauMonomial k (2 * k - 1)) -
        Polynomial.C ((j : ℚ) ^ (2 * k) / 2) *
          (tauPolePoly k (j : ℤ) + tauPolePoly k (-(j : ℤ))) := by
  have hjq : (j : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 1) hj))
  have h2kq : (2 * (k : ℚ)) ≠ 0 := by positivity
  have hdpos : dIndex (j : ℤ) = j := by
    simp [dIndex, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (j : ℤ))]
  have hdneg : dIndex (-(j : ℤ)) = j - 1 := by
    have hneg : ¬ (0 : ℤ) ≤ -(j : ℤ) := by omega
    unfold dIndex
    rw [if_neg hneg]
    have hcast : -(-(j : ℤ)) - 1 = ((j - 1 : ℕ) : ℤ) := by omega
    rw [hcast]
    simp
  have hidx : j - 1 + 1 = j := by omega
  have hrec : harmonicWeight (2 * k + 1) j =
      harmonicWeight (2 * k + 1) (j - 1) + (((j : ℚ) ^ (2 * k + 1))⁻¹) := by
    have hs := harmonicWeight_succ (2 * k + 1) (j - 1)
    rw [hidx] at hs
    exact hs
  have htm : tauMonomial k (2 * k - 1) = (1 : ℚ) / (2 * k) := by
    rw [tauMonomial_eq_choose k (2 * k - 1) hk]
    simp
  have hpow : (j : ℚ) ^ (2 * k + 1) =
      (j : ℚ) ^ (2 * k) * (j : ℚ) := by
    rw [show 2 * k + 1 = (2 * k) + 1 by omega, pow_succ]
  have hsum :
      tauPolePoly k (j : ℤ) + tauPolePoly k (-(j : ℤ)) =
        Polynomial.C (harmonicWeight (2 * k + 1) j +
          harmonicWeight (2 * k + 1) (j - 1)) -
          Polynomial.X - Polynomial.X := by
    unfold tauPolePoly
    rw [hdpos, hdneg]
    calc
      (Polynomial.C (harmonicWeight (2 * k + 1) j) - Polynomial.X) +
          (Polynomial.C (harmonicWeight (2 * k + 1) (j - 1)) - Polynomial.X) =
        (Polynomial.C (harmonicWeight (2 * k + 1) j) +
          Polynomial.C (harmonicWeight (2 * k + 1) (j - 1))) -
          Polynomial.X - Polynomial.X := by ring
      _ = _ := by rw [Polynomial.C_add]
  have hIntercept :
      1 / (2 * (j : ℚ)) - 1 / (2 * (k : ℚ)) -
          (j : ℚ) ^ (2 * k) * harmonicWeight (2 * k + 1) j =
        -1 / (2 * (k : ℚ)) -
          ((j : ℚ) ^ (2 * k) / 2) *
            (harmonicWeight (2 * k + 1) j +
              harmonicWeight (2 * k + 1) (j - 1)) := by
    rw [hrec, hpow]
    field_simp [hjq, h2kq, pow_ne_zero _ hjq] <;> ring
  unfold muPolePoly
  rw [hsum, htm, affinePoleLeft, affinePoleRight]
  have hslope : 2 * ((j : ℚ) ^ (2 * k) / 2) = (j : ℚ) ^ (2 * k) := by
    field_simp
  rw [hslope, hIntercept]
  congr 1 <;> ring

/-- Lemma 2.3 (1) (Reflection identity for `τ_X^{(s)}` on simple poles):
`τ_X^{(s)}((-1 - x - r)^{-1}) = -τ_X^{(s)}((x - r)^{-1})`. -/
theorem tau_reflection_pole (k : ℕ) (r : ℤ) :
    -tauPolePoly k (-1 - r) = -tauPolePoly k r := by
  unfold tauPolePoly
  rw [dIndex_reflect]

/-- Lemma 2.3 (1) (Reflection identity for `τ_X^{(s)}` on monomials):
For `s = 2k + 1 ≥ 3`, `∑_{i=0}^d C(d,i) (-1)^d τ_X^{(s)}(x^i) = -τ_X^{(s)}(x^d)`. -/
theorem tau_reflection_monomial (k d : ℕ) (hk : 1 ≤ k) :
    (-1 : ℚ) ^ d * (∑ i ∈ Finset.range (d + 1), (Nat.choose d i : ℚ) * tauMonomial k i) =
      -tauMonomial k d := by
  by_cases hd : 2 * k - 1 ≤ d
  · rw [tauMonomial_binomial_convolution k d hk hd]
    rw [tauMonomial_eq_choose k d hk, if_pos hd]
    let n := d - (2 * k - 1)
    have hdn : d - (2 * k - 1) = n := rfl
    rw [hdn]
    by_cases hn0 : n = 0
    · have hdEq : d = 2 * k - 1 := by dsimp [n] at hn0; omega
      rw [hdEq, hn0]
      have hodd : Odd (2 * k - 1) := by
        refine ⟨k - 1, ?_⟩
        omega
      have hpow : (-1 : ℚ) ^ (2 * k - 1) = -1 := hodd.neg_one_pow
      simp [hpow, bernoulli_zero, bernoulli'_zero] <;> ring
    · by_cases hn1 : n = 1
      · have hdEq : d = 2 * k := by dsimp [n] at hn1; omega
        rw [hdEq, hn1]
        have heven : Even (2 * k) := ⟨k, by omega⟩
        have hpow : (-1 : ℚ) ^ (2 * k) = 1 := heven.neg_one_pow
        simp [hpow, bernoulli_one, bernoulli'_one] <;> ring
      · have hBern : bernoulli' n = bernoulli n :=
          (bernoulli_eq_bernoulli'_of_ne_one hn1).symm
        by_cases hodd : Odd n
        · have hB : bernoulli n = 0 :=
            bernoulli_eq_zero_of_odd hodd (by omega)
          have hBp : bernoulli' n = 0 :=
            bernoulli'_eq_zero_of_odd hodd (by omega)
          simp [hB, hBp]
        · have heven : Even n := Nat.not_odd_iff_even.mp hodd
          have hpow : (-1 : ℚ) ^ d = -1 := by
            have hdOdd : Odd d := by
              have hrOdd : Odd (2 * k - 1) := by
                refine ⟨k - 1, ?_⟩
                omega
              have hsum : Odd ((2 * k - 1) + n) := by
                rcases hrOdd with ⟨a, ha⟩
                rcases heven with ⟨b, hb⟩
                refine ⟨a + b, ?_⟩
                omega
              have hdEq : d = (2 * k - 1) + n := by dsimp [n]; omega
              rw [hdEq]
              exact hsum
            exact hdOdd.neg_one_pow
          rw [hBern, hpow]
          ring
  · have hzero : ∀ i ∈ Finset.range (d + 1), tauMonomial k i = 0 := by
      intro i hi
      have hiLt : i < 2 * k - 1 := by
        have hiLe : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        omega
      simp [tauMonomial, Nat.not_le_of_gt hiLt]
    have hsum :
        (∑ i ∈ Finset.range (d + 1),
          (Nat.choose d i : ℚ) * tauMonomial k i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hzero i hi]
    have hweight : tauMonomial k d = 0 := by
      simp [tauMonomial, hd]
    simp [hsum, hweight]

/-- Lemma 2.3 (2) (Difference identity for `τ_X^{(s)}`):
For `h(x) = (x - r)^{-1}` with `r ∈ ℤ \ {0, 1}`,
`τ_X^{(2k+1)}((x - (r - 1))^{-1}) - τ_X^{(2k+1)}((x - r)^{-1}) = -(r : ℚ)^{-(2k+1)}`. -/
theorem tau_difference_pole (k : ℕ) (r : ℤ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    tauPolePoly k (r - 1) - tauPolePoly k r =
      Polynomial.C (-((r : ℚ) ^ (2 * k + 1))⁻¹) := by
  have hcases : r ≤ -1 ∨ 2 ≤ r := by omega
  rcases hcases with hneg | hpos
  · have hidx : dIndex (r - 1) = dIndex r + 1 := by
      have hnot1 : ¬ (0 : ℤ) ≤ r - 1 := by omega
      have hnot : ¬ (0 : ℤ) ≤ r := by omega
      have hidxInt : ((dIndex (r - 1) : ℕ) : ℤ) =
          (dIndex r : ℕ) + 1 := by
        unfold dIndex
        simp only [if_neg hnot1, if_neg hnot]
        have harg : -(r - 1) - 1 = -r := by omega
        rw [harg]
        have hneg0 : (0 : ℤ) ≤ -r := by omega
        have hneg1 : (0 : ℤ) ≤ -r - 1 := by omega
        rw [Int.toNat_of_nonneg hneg0, Int.toNat_of_nonneg hneg1]
        omega
      exact_mod_cast hidxInt
    have hrec := harmonicWeight_succ (2 * k + 1) (dIndex r)
    unfold tauPolePoly
    rw [hidx]
    have hrec' : harmonicWeight (2 * k + 1) (dIndex r + 1) =
        harmonicWeight (2 * k + 1) (dIndex r) +
          (((dIndex r + 1 : ℕ) : ℚ) ^ (2 * k + 1))⁻¹ := hrec
    rw [hrec']
    have hdm : dIndex (r - 1) = (-r).toNat := by
      unfold dIndex
      rw [if_neg (by omega : ¬ (0 : ℤ) ≤ r - 1)]
      have harg : -(r - 1) - 1 = -r := by omega
      rw [harg]
    have hidxNat : dIndex r + 1 = (-r).toNat := by
      rw [← hidx, hdm]
    have hcastInt : ((dIndex r + 1 : ℕ) : ℤ) = -r := by
      rw [hidxNat]
      exact Int.toNat_of_nonneg (by omega)
    have hcast : ((dIndex r + 1 : ℕ) : ℚ) = -(r : ℚ) := by
      exact_mod_cast hcastInt
    rw [hcast]
    rw [neg_pow]
    have hpow : (-1 : ℚ) ^ (2 * k + 1) = -1 := by
      have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
      exact hodd.neg_one_pow
    rw [hpow]
    simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg, neg_one_mul, inv_neg]
    ring
  · have hidx : dIndex (r - 1) + 1 = dIndex r := by
      have hrnonneg : (0 : ℤ) ≤ r := by omega
      have hrprev : (0 : ℤ) ≤ r - 1 := by omega
      have hidxInt : ((dIndex (r - 1) : ℕ) : ℤ) + 1 =
          (dIndex r : ℕ) := by
        unfold dIndex
        simp only [if_pos hrprev, if_pos hrnonneg]
        rw [Int.toNat_of_nonneg hrprev, Int.toNat_of_nonneg hrnonneg]
        omega
      exact_mod_cast hidxInt
    unfold tauPolePoly
    rw [← hidx]
    have hrec := harmonicWeight_succ (2 * k + 1) (dIndex (r - 1))
    rw [hrec]
    have hcastInt : ((dIndex (r - 1) + 1 : ℕ) : ℤ) = r := by
      rw [hidx]
      unfold dIndex
      simp only [if_pos (by omega : (0 : ℤ) ≤ r)]
      exact Int.toNat_of_nonneg (by omega)
    have hcast : ((dIndex (r - 1) + 1 : ℕ) : ℚ) = (r : ℚ) := by
      exact_mod_cast hcastInt
    rw [hcast]
    simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg]
    ring

/-- After cancelling the common factor (D_N), the kernel numerator is
(D_N(t)^{2m-1} t^d). -/
noncomputable def kernelNumerator (p : HankelParams) (d : ℕ) : ℚ[X] :=
  D_poly p.N ^ (2 * p.m - 1) * Polynomial.X ^ d

/-- At a tail pole, the kernel numerator evaluates to the initial-pole product
raised to the odd exponent, times the pole node to the monomial degree. -/
lemma kernelNumerator_eval_tail_pole (p : HankelParams) (d a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    Polynomial.eval (-((a : ℚ) ^ 2)) (kernelNumerator p d) =
      (∏ ν ∈ Finset.Icc 1 p.N, ((ν : ℚ) ^ 2 - (a : ℚ) ^ 2)) ^ (2 * p.m - 1) *
        (-((a : ℚ) ^ 2)) ^ d := by
  simp [kernelNumerator, D_poly, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_prod, sub_eq_add_neg, add_comm]

/-- Data selected from Mathlib's partial-fraction theorem: a polynomial part
and one degree-zero remainder for each simple tail factor. -/
structure KernelPartialFractionData (p : HankelParams) (d : ℕ) where
  quotient : ℚ[X]
  remainder : ℕ → ℚ[X]
  remainder_degree : ∀ a ∈ Finset.Icc (p.N + 1) p.K,
    (remainder a).degree <
      (Polynomial.X + Polynomial.C ((a : ℚ) ^ 2)).degree
  numerator_eq :
    kernelNumerator p d =
      quotient * tailPolynomial p.N p.K +
        ∑ a ∈ Finset.Icc (p.N + 1) p.K,
          remainder a * ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2))

/-- Distinct negative-square tail factors are pairwise coprime over ℚ. -/
lemma tailPoleFactors_pairwise_coprime (p : HankelParams) :
    Set.Pairwise (↑(Finset.Icc (p.N + 1) p.K) : Set ℕ)
      (fun a b : ℕ =>
        IsCoprime
          (Polynomial.X + Polynomial.C ((a : ℚ) ^ 2))
          (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2))) := by
  intro a ha b hb hab
  have habq : (a : ℚ) ≠ b := by exact_mod_cast hab
  have hdiff : (a : ℚ) ^ 2 - (b : ℚ) ^ 2 ≠ 0 := by
    intro h
    have hsq : (a : ℚ) ^ 2 = (b : ℚ) ^ 2 := sub_eq_zero.mp h
    have ha0 : (0 : ℚ) ≤ (a : ℚ) := by positivity
    have hb0 : (0 : ℚ) ≤ (b : ℚ) := by positivity
    have heq : (a : ℚ) = (b : ℚ) := by
      nlinarith [sq_nonneg ((a : ℚ) - (b : ℚ))]
    exact habq heq
  let c : ℚ := ((a : ℚ) ^ 2 - (b : ℚ) ^ 2)⁻¹
  refine ⟨Polynomial.C c, -Polynomial.C c, ?_⟩
  have hsub :
      (Polynomial.X + Polynomial.C ((a : ℚ) ^ 2)) -
        (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2)) =
      Polynomial.C ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) := by
    rw [Polynomial.C_sub]
    ring
  calc
    Polynomial.C c * (Polynomial.X + Polynomial.C ((a : ℚ) ^ 2)) +
        (-Polynomial.C c) * (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2)) =
      Polynomial.C c *
        ((Polynomial.X + Polynomial.C ((a : ℚ) ^ 2)) -
          (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2))) := by ring
    _ = Polynomial.C c * Polynomial.C ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) := by rw [hsub]
    _ = 1 := by
      rw [← Polynomial.C_mul]
      simp [c, hdiff]

/-- Existence of a polynomial quotient and bounded remainders at the distinct
tail poles. This is the general partial-fraction decomposition supplied by
Mathlib; identifying each remainder with the explicit derivative-form residue
is isolated in kernelRatElem_poleRes_eq_prod. -/
theorem kernelNumerator_partial_fraction_exists (p : HankelParams) (d : ℕ) :
    Nonempty (KernelPartialFractionData p d) := by
  classical
  obtain ⟨q, r, hr, hf⟩ :=
    Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod
      (f := kernelNumerator p d)
      (s := Finset.Icc (p.N + 1) p.K)
      (g := fun a : ℕ => Polynomial.X + Polynomial.C ((a : ℚ) ^ 2))
      (hg := by
        intro a ha
        exact Polynomial.monic_X_add_C _)
      (hgg := by simpa using tailPoleFactors_pairwise_coprime p)
  refine ⟨⟨q, r, hr, ?_⟩⟩
  simpa [tailPolynomial] using hf


/-- A polynomial of degree less than one is constant. -/
lemma polynomial_eq_C_of_degree_lt_one {f : ℚ[X]} (hf : f.degree < 1) :
    f = Polynomial.C (f.coeff 0) := by
  have hnat : f.natDegree < 1 := by
    by_cases hzero : f = 0
    · simp [hzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2 hf
  ext n
  cases n with
  | zero => simp
  | succ n =>
      have hcoeff : f.coeff (n + 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < n + 1)
      simp [hcoeff]

/-- Choose the quotient and bounded remainders provided by the proved
pairwise-coprime partial-fraction existence theorem. -/
noncomputable def kernelPartialFractionData (p : HankelParams) (d : ℕ) :
    KernelPartialFractionData p d :=
  Classical.choice (kernelNumerator_partial_fraction_exists p d)

/-- Kernel quotient and simple-pole residue data. Each remainder has degree
less than one, so its constant coefficient is the corresponding pole weight.
The derivative formula for that coefficient is stated separately. -/
noncomputable def kernelRatElem (p : HankelParams) (d : ℕ) : RatMomentElem :=
  { polyPart := (kernelPartialFractionData p d).quotient
    maxPole := p.K
    poleRes := fun j =>
      if hj : j ∈ Finset.Icc (p.N + 1) p.K then
        ((kernelPartialFractionData p d).remainder j).coeff 0
      else 0 }

/-- At a tail pole, the stored residue is the constant coefficient of the
corresponding bounded remainder. -/
@[simp] theorem kernelRatElem_poleRes (p : HankelParams) (d a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    (kernelRatElem p d).poleRes a =
      ((kernelPartialFractionData p d).remainder a).coeff 0 := by
  dsimp [kernelRatElem]
  rw [if_pos ha]

/-- Polynomial form of the partial-fraction identity for the kernel.
The identity is proved from the pairwise-coprime decomposition supplied by
Mathlib, after showing each degree-bounded remainder is constant. -/
theorem kernelNumerator_partial_fraction (p : HankelParams) (d : ℕ) :
    kernelNumerator p d =
      (kernelRatElem p d).polyPart * tailPolynomial p.N p.K +
        ∑ a ∈ Finset.Icc (p.N + 1) p.K,
          Polynomial.C ((kernelRatElem p d).poleRes a) *
            ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
              (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2)) := by
  let data := kernelPartialFractionData p d
  have hconst (a : ℕ) (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
      data.remainder a = Polynomial.C ((data.remainder a).coeff 0) := by
    apply polynomial_eq_C_of_degree_lt_one
    have hdeg := data.remainder_degree a ha
    simpa only [Polynomial.degree_X_add_C] using hdeg
  calc
    kernelNumerator p d =
        data.quotient * tailPolynomial p.N p.K +
          ∑ a ∈ Finset.Icc (p.N + 1) p.K,
            data.remainder a *
              ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
                (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2)) := data.numerator_eq
    _ = (kernelRatElem p d).polyPart * tailPolynomial p.N p.K +
          ∑ a ∈ Finset.Icc (p.N + 1) p.K,
            Polynomial.C ((kernelRatElem p d).poleRes a) *
              ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
                (Polynomial.X + Polynomial.C ((b : ℚ) ^ 2)) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro a ha
        rw [hconst a ha, kernelRatElem_poleRes p d a ha]

/-- Equation (2.8): The `h × h` Hankel matrix pencil `G_K^{(2k+1)}(X)` over `ℚ[X]`. -/
noncomputable def G_pencil (p : HankelParams) (k : ℕ) :
    Matrix (Fin p.h) (Fin p.h) ℚ[X] :=
  fun i j => muFunctionalPoly k (kernelRatElem p (i.val + j.val))

/-- Equation (2.8): The Hankel determinant polynomial `Δ_K^{(2k+1)}(X) := det G_K^{(2k+1)}(X) ∈ ℚ[X]`. -/
noncomputable def Delta_poly (p : HankelParams) (k : ℕ) : ℚ[X] :=
  (G_pencil p k).det

/-- Rational content of a polynomial, obtained by clearing denominators to an
integer polynomial and dividing its integer content by the clearing scalar.
It is positive whenever the polynomial is nonzero. -/
noncomputable def ratContent (A : ℚ[X]) : ℚ :=
  let P : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) A
  let b : ℤ := (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) A).choose
  |(P.content : ℚ) / (b : ℚ)|

/-- The rational content is strictly positive for every nonzero polynomial. -/
lemma ratContent_pos {A : ℚ[X]} (hA : A ≠ 0) : 0 < ratContent A := by
  let P : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) A
  let b : ℤ := (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) A).choose
  have hP : P ≠ 0 := by
    dsimp [P]
    exact IsFractionRing.integerNormalization_eq_zero_iff.not.mpr hA
  have hcontent : P.content ≠ 0 :=
    Polynomial.content_eq_zero_iff.not.mpr hP
  have hb : b ≠ 0 := by
    dsimp [b]
    exact nonZeroDivisors.ne_zero
      (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) A).choose_spec.1
  change 0 < |(P.content : ℚ) / (b : ℚ)|
  exact abs_pos.mpr (div_ne_zero (by exact_mod_cast hcontent) (by exact_mod_cast hb))

/-- The rational content vanishes exactly at the zero polynomial. -/
lemma ratContent_eq_zero_iff (A : ℚ[X]) : ratContent A = 0 ↔ A = 0 := by
  constructor
  · intro h
    by_contra hA
    have hpos := ratContent_pos hA
    linarith
  · intro hA
    subst A
    have hP :
        IsLocalization.integerNormalization (nonZeroDivisors ℤ) (0 : ℚ[X]) = 0 :=
      IsFractionRing.integerNormalization_eq_zero_iff.mpr rfl
    simp [ratContent, hP]

/-- Rational normalization of a nonzero polynomial by its positive rational content. -/
noncomputable def primitiveRationalPolynomial (A : ℚ[X]) : ℚ[X] :=
  Polynomial.C (ratContent A)⁻¹ * A

/-- Equation (2.9): The primitive integer Hankel polynomial P_K^(2k+1)(X),
viewed in ℚ[X]. -/
noncomputable def P_prim (p : HankelParams) (k : ℕ) : ℚ[X] :=
  primitiveRationalPolynomial (Delta_poly p k)

/-- Determinant-scaling component of manuscript Theorem 2.4 (canonical basis invariance).
This theorem establishes the determinant identity only. The manuscript's additional
primitive-content conclusion `P_{A,B} = ± P_K` is not asserted here and remains
an independent arithmetic obligation. -/
theorem canonical_basis_invariance {h : ℕ} (G : Matrix (Fin h) (Fin h) ℚ[X])
    (MA MB : Matrix (Fin h) (Fin h) ℚ) (hMA : IsUnit MA.det) (hMB : IsUnit MB.det) :
    (MA.map Polynomial.C * G * MB.transpose.map Polynomial.C).det =
      Polynomial.C (MA.det * MB.det) * G.det := by
  exact det_change_of_basis_rational_polynomial G MA MB

/-- Tail denominator polynomial `D_tail(t) := ∏_{c = N+1}^K (t + c^2)`. -/
noncomputable def D_tail (p : HankelParams) : ℚ[X] :=
  ∏ c ∈ Finset.Icc (p.N + 1) p.K, (Polynomial.X + Polynomial.C ((c : ℚ) ^ 2))

/-- The blueprint tail denominator is definitionally the foundational tail product. -/
lemma D_tail_eq_tailPolynomial (p : HankelParams) :
    D_tail p = tailPolynomial p.N p.K := by
  rfl

/-- The full denominator factors into the initial and tail products.
This is the polynomial identity D_K = D_N D_tail used to reduce the kernel
rational function to a polynomial quotient plus simple tail-pole residues. -/
lemma D_poly_factorization (p : HankelParams) :
    D_poly p.K = D_poly p.N * D_tail p := by
  classical
  unfold D_poly D_tail
  have hset : Finset.Icc 1 p.K =
      Finset.Icc 1 p.N ∪ Finset.Icc (p.N + 1) p.K := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨hj1, hjK⟩
      by_cases hjN : j ≤ p.N
      · exact Or.inl ⟨hj1, hjN⟩
      · exact Or.inr ⟨by omega, hjK⟩
    · rintro (⟨hj1, hjN⟩ | ⟨hjTail, hjK⟩)
      · exact ⟨hj1, le_trans hjN (Nat.le_of_lt p.hK)⟩
      · exact ⟨by omega, hjK⟩
  have hdisj : Disjoint (Finset.Icc 1 p.N)
      (Finset.Icc (p.N + 1) p.K) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjN hjTail
    simp only [Finset.mem_Icc] at hjN hjTail
    omega
  rw [hset, Finset.prod_union hdisj]

/-- The blueprint denominator is definitionally the foundational denominator product. -/
lemma D_poly_eq_denominatorPolynomial (m : ℕ) :
    D_poly m = denominatorPolynomial m := by
  rfl

/-- The kernel numerator vanishes at every initial pole that is cancelled
by the factor (D_N(t)^{2m-1}). -/
lemma kernelNumerator_eval_old_pole (p : HankelParams) (d a : ℕ)
    (ha : a ∈ Finset.Icc 1 p.N) :
    Polynomial.eval (-((a : ℚ) ^ 2)) (kernelNumerator p d) = 0 := by
  have hm : 1 ≤ p.m := p.hm
  have hexp : 0 < 2 * p.m - 1 := by omega
  have hexp0 : 2 * p.m - 1 ≠ 0 := Nat.ne_of_gt hexp
  unfold kernelNumerator
  rw [D_poly_eq_denominatorPolynomial]
  rw [Polynomial.eval_mul, Polynomial.eval_pow]
  rw [denominatorPolynomial_eval_pole p.N a ha]
  simp [hexp0]

/-- At a genuine tail pole, the stored residue denominator is exactly
the product of the other pole differences. -/
lemma kernelRatElem_poleRes_eq_prod (p : HankelParams) (d a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    (kernelRatElem p d).poleRes a =
      Polynomial.eval (-((a : ℚ) ^ 2)) (kernelNumerator p d) /
        ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
          ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
  classical
  let s := Finset.Icc (p.N + 1) p.K
  let x : ℚ := -((a : ℚ) ^ 2)
  have htail : Polynomial.eval x (tailPolynomial p.N p.K) = 0 := by
    simpa [x] using tailPolynomial_eval_pole p.N p.K a ha
  have hprod (b : ℕ) :
      Polynomial.eval x
          (∏ c ∈ s.erase b,
            (Polynomial.X + Polynomial.C ((c : ℚ) ^ 2))) =
        ∏ c ∈ s.erase b, ((c : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro c hc
    simp [x, sub_eq_add_neg, add_comm]
  have hEval' :
      Polynomial.eval x (kernelNumerator p d) =
        ∑ b ∈ s, Polynomial.eval x
          (Polynomial.C ((kernelRatElem p d).poleRes b) *
            ∏ c ∈ s.erase b,
              (Polynomial.X + Polynomial.C ((c : ℚ) ^ 2))) := by
    have hEval := congrArg (Polynomial.eval x) (kernelNumerator_partial_fraction p d)
    rw [Polynomial.eval_add, Polynomial.eval_mul, htail] at hEval
    simp only [mul_zero, zero_add] at hEval
    rw [Polynomial.eval_finsetSum] at hEval
    simpa [s, Polynomial.eval_mul, Polynomial.eval_C, hprod] using hEval
  have hsum :
      (∑ b ∈ s, Polynomial.eval x
        (Polynomial.C ((kernelRatElem p d).poleRes b) *
          ∏ c ∈ s.erase b,
            (Polynomial.X + Polynomial.C ((c : ℚ) ^ 2)))) =
        (kernelRatElem p d).poleRes a *
          ∏ c ∈ s.erase a, ((c : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
    rw [Finset.sum_eq_single a]
    · rw [Polynomial.eval_mul, Polynomial.eval_C, hprod a]
    · intro b hb hba
      rw [Polynomial.eval_mul, Polynomial.eval_C, hprod b]
      apply mul_eq_zero.mpr
      right
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩)
      simp
    · intro hnot
      exact (hnot ha).elim
  rw [hsum] at hEval'
  have hder : Polynomial.eval x
      (Polynomial.derivative (tailPolynomial p.N p.K)) ≠ 0 := by
    simpa [x] using lagrangePoleDenominator_ne_zero p.N p.K a ha
  have hden : (∏ c ∈ s.erase a,
      ((c : ℚ) ^ 2 - (a : ℚ) ^ 2)) ≠ 0 := by
    rw [← tailPolynomial_derivative_eval_pole p.N p.K a ha]
    simpa [s] using hder
  have hEval'' := hEval'
  simp only [s] at hEval''
  have hEvalExplicit :
      Polynomial.eval (-((a : ℚ) ^ 2)) (kernelNumerator p d) =
        (kernelRatElem p d).poleRes a *
          ∏ c ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            ((c : ℚ) ^ 2 - (a : ℚ) ^ 2) := by
    simpa [x] using hEval''
  calc
    (kernelRatElem p d).poleRes a =
        (kernelRatElem p d).poleRes a *
          (∏ c ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            ((c : ℚ) ^ 2 - (a : ℚ) ^ 2)) /
          (∏ c ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            ((c : ℚ) ^ 2 - (a : ℚ) ^ 2)) := by
      have hprodEq :
          (∏ c ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            (-((a : ℚ) ^ 2) + (c : ℚ) ^ 2)) =
          (∏ c ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            ((c : ℚ) ^ 2 - (a : ℚ) ^ 2)) := by
        apply Finset.prod_congr rfl
        intro c hc
        ring
      have hden' :
          (∏ c ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            (-((a : ℚ) ^ 2) + (c : ℚ) ^ 2)) ≠ 0 := by
        rw [hprodEq]
        exact hden
      rw [← hprodEq]
      field_simp [hden'] <;> ring
    _ = Polynomial.eval (-((a : ℚ) ^ 2)) (kernelNumerator p d) /
          (∏ c ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            ((c : ℚ) ^ 2 - (a : ℚ) ^ 2)) := by
      simpa [Nat.add_comm] using
        congrArg (fun z : ℚ => z /
          (∏ c ∈ (Finset.Icc (p.N + 1) p.K).erase a,
            ((c : ℚ) ^ 2 - (a : ℚ) ^ 2))) hEvalExplicit.symm

/-- Residues at the initial poles vanish because the numerator contains
(D_N(t)^{2m-1}). Thus the only nonzero pole data are in the tail interval. -/
lemma kernelRatElem_poleRes_old_zero (p : HankelParams) (d a : ℕ)
    (ha : a ∈ Finset.Icc 1 p.N) :
    (kernelRatElem p d).poleRes a = 0 := by
  have hnot : a ∉ Finset.Icc (p.N + 1) p.K := by
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  dsimp [kernelRatElem]
  rw [if_neg hnot]

/-- Pole index shifted into `Fin p.h`: `a(idx) = N + 1 + idx.val ∈ (N, K]`. -/
def poleNat (p : HankelParams) (idx : Fin p.h) : ℕ :=
  p.N + 1 + idx.val

/-- The shifted pole index enumerates the full tail interval. -/
lemma poleNat_mem_tail (p : HankelParams) (idx : Fin p.h) :
    poleNat p idx ∈ Finset.Icc (p.N + 1) p.K := by
  simp only [Finset.mem_Icc]
  constructor
  · dsimp [poleNat]
    omega
  · have hi := idx.isLt
    dsimp [HankelParams.h] at hi
    dsimp [poleNat]
    omega

/-- Every tail pole is represented by exactly one Fin h index. -/
lemma exists_poleNat_eq (p : HankelParams) (a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    ∃ idx : Fin p.h, poleNat p idx = a := by
  have ha' := Finset.mem_Icc.mp ha
  refine ⟨⟨a - (p.N + 1), ?_⟩, ?_⟩
  · dsimp [HankelParams.h]
    omega
  · dsimp [poleNat]
    omega

/-- Distinct matrix indices correspond to distinct integer pole indices. -/
lemma poleNat_injective (p : HankelParams) :
    Function.Injective (poleNat p) := by
  intro i j hij
  apply Fin.ext
  dsimp [poleNat] at hij
  omega

/-- The finite pole index is a bijection onto the tail-pole subtype. -/
def poleIndexEquiv (p : HankelParams) :
    Fin p.h ≃ {a : ℕ // a ∈ Finset.Icc (p.N + 1) p.K} := by
  refine Equiv.ofBijective (fun idx : Fin p.h =>
    ⟨poleNat p idx, poleNat_mem_tail p idx⟩) ?_
  constructor
  · intro i j hij
    apply poleNat_injective p
    exact congrArg Subtype.val hij
  · intro a
    obtain ⟨idx, hidx⟩ := exists_poleNat_eq p a.val a.property
    exact ⟨idx, Subtype.ext hidx⟩

/-- Negative square pole node `v_a := -a^2` for `N < a ≤ K`. -/
def poleNode (p : HankelParams) (idx : Fin p.h) : ℚ :=
  -((poleNat p idx : ℚ) ^ 2)

/-- Vandermonde matrix `V = (v_a^i)_{0 ≤ i < h, N < a ≤ K}` at the negative square poles. -/
def V_pole (p : HankelParams) : Matrix (Fin p.h) (Fin p.h) ℚ :=
  fun i idx => (poleNode p idx) ^ i.val

/-- Distinct Lagrange indices give distinct negative-square pole nodes.
This is the separation hypothesis needed for a Vandermonde invertibility proof. -/
lemma poleNode_injective (p : HankelParams) : Function.Injective (poleNode p) := by
  intro i j hij
  have hsquares : (poleNat p i : ℚ) ^ 2 = (poleNat p j : ℚ) ^ 2 := by
    dsimp [poleNode] at hij
    linarith
  have hcast : (poleNat p i : ℚ) = (poleNat p j : ℚ) := by
    have hi : 0 ≤ (poleNat p i : ℚ) := by positivity
    have hj : 0 ≤ (poleNat p j : ℚ) := by positivity
    nlinarith [hsquares]
  apply poleNat_injective p
  exact_mod_cast hcast

/-- The pole Vandermonde matrix is nonsingular: it is the transpose of
Mathlib's Vandermonde matrix at the injective pole-node map. -/
lemma V_pole_det_ne_zero (p : HankelParams) : (V_pole p).det ≠ 0 := by
  have hV : V_pole p = (Matrix.vandermonde (poleNode p)).transpose := by
    ext i idx
    rfl
  rw [hV, Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
  exact poleNode_injective p

/-- Equation (2.11): The Lagrange diagonal residue weight `γ_a^{(2k+1)} ≠ 0`. -/
noncomputable def gammaWeight (p : HankelParams) (k : ℕ) (idx : Fin p.h) : ℚ :=
  let a : ℚ := poleNat p idx
  (a ^ (2 * k) * (∏ ν ∈ Finset.Icc 1 p.N, ((ν : ℚ) ^ 2 - a ^ 2)) ^ (2 * p.m - 1)) /
    ∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase (poleNat p idx), ((b : ℚ) ^ 2 - a ^ 2)

/-- Every Lagrange pole weight is nonzero, as required for the
nonsingularity of the derivative matrix in Theorem 2.5. -/
lemma gammaWeight_ne_zero (p : HankelParams) (k : ℕ) (idx : Fin p.h) :
    gammaWeight p k idx ≠ 0 := by
  classical
  let a := poleNat p idx
  have ha_mem : a ∈ Finset.Icc (p.N + 1) p.K := by
    simpa [a] using poleNat_mem_tail p idx
  have ha_gt : p.N < a := by
    have h := (Finset.mem_Icc.mp ha_mem).1
    omega
  have ha_pos : 0 < a := by omega
  have haq : (a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha_pos)
  have hnumprod :
      (∏ ν ∈ Finset.Icc 1 p.N, ((ν : ℚ) ^ 2 - (a : ℚ) ^ 2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ν hν
    have hνle : ν ≤ p.N := (Finset.mem_Icc.mp hν).2
    have hνlt : ν < a := by omega
    have hcast : (ν : ℚ) < (a : ℚ) := by exact_mod_cast hνlt
    nlinarith
  have hden :
      (∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
        ((b : ℚ) ^ 2 - (a : ℚ) ^ 2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    have hfactor : ((b : ℚ) ^ 2 - (a : ℚ) ^ 2) ≠ 0 := by
      intro heq
      have hs : (b : ℚ) ^ 2 = (a : ℚ) ^ 2 := sub_eq_zero.mp heq
      have hcast : (b : ℚ) = (a : ℚ) := by
        nlinarith [sq_nonneg ((b : ℚ) - (a : ℚ))]
      exact hba (by exact_mod_cast hcast)
    exact hfactor
  unfold gammaWeight
  dsimp
  apply div_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ haq
    · exact pow_ne_zero _ hnumprod
  · exact hden

/-- The residue times its monomial moment is the corresponding diagonal
weight times the pole node raised to the Hankel index. -/
lemma kernelResidue_weighted_eq_gamma (p : HankelParams) (k d : ℕ)
    (idx : Fin p.h) :
    (kernelRatElem p d).poleRes (poleNat p idx) *
        (poleNat p idx : ℚ) ^ (2 * k) =
      gammaWeight p k idx * (poleNode p idx) ^ d := by
  classical
  let a := poleNat p idx
  have ha : a ∈ Finset.Icc (p.N + 1) p.K := by
    simpa [a] using poleNat_mem_tail p idx
  have hden :
      (∏ b ∈ (Finset.Icc (p.N + 1) p.K).erase a,
        ((b : ℚ) ^ 2 - (a : ℚ) ^ 2)) ≠ 0 := by
    rw [← tailPolynomial_derivative_eval_pole p.N p.K a ha]
    exact lagrangePoleDenominator_ne_zero p.N p.K a ha
  rw [kernelRatElem_poleRes_eq_prod p d a ha,
    kernelNumerator_eval_tail_pole p d a ha]
  unfold gammaWeight poleNode
  dsimp [a]
  field_simp [hden] <;> ring

/-- The `X`-derivative matrix `M_K^{(2k+1)} := [X] G_K^{(2k+1)}(X)`. -/
noncomputable def M_deriv (p : HankelParams) (k : ℕ) : Matrix (Fin p.h) (Fin p.h) ℚ :=
  fun i j => (G_pencil p k i j).coeff 1

/-- Entrywise residue formula for the derivative matrix. The residues at the
initial poles vanish, leaving only the tail-pole sum. -/
lemma M_deriv_entry_eq_tail_residue_sum (p : HankelParams) (k : ℕ)
    (i j : Fin p.h) :
    M_deriv p k i j =
      ∑ a ∈ Finset.Icc (p.N + 1) p.K,
        (kernelRatElem p (i.val + j.val)).poleRes a * (a : ℚ) ^ (2 * k) := by
  classical
  simp only [M_deriv, G_pencil, muFunctionalPoly_coeff_one]
  have hmax : (kernelRatElem p (i.val + j.val)).maxPole = p.K := rfl
  rw [hmax]
  have hNK : p.N < p.K := p.hK
  have hset : Finset.Icc 1 p.K =
      Finset.Icc 1 p.N ∪ Finset.Icc (p.N + 1) p.K := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_union] <;> omega
  have hdisj : Disjoint (Finset.Icc 1 p.N)
      (Finset.Icc (p.N + 1) p.K) := by
    refine Finset.disjoint_left.mpr ?_
    intro a haN haTail
    simp only [Finset.mem_Icc] at haN haTail
    omega
  have hzero :
      (∑ a ∈ Finset.Icc 1 p.N,
        (kernelRatElem p (i.val + j.val)).poleRes a * (a : ℚ) ^ (2 * k)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    simp [kernelRatElem_poleRes_old_zero p (i.val + j.val) a ha]
  rw [hset, Finset.sum_union hdisj, hzero] <;> simp

/-- Reindex the derivative matrix entry by the finite pole indices. -/
lemma M_deriv_entry_eq_gamma_sum (p : HankelParams) (k : ℕ)
    (i j : Fin p.h) :
    M_deriv p k i j =
      ∑ idx : Fin p.h,
        gammaWeight p k idx * (poleNode p idx) ^ (i.val + j.val) := by
  classical
  rw [M_deriv_entry_eq_tail_residue_sum]
  rw [← Finset.sum_attach, Finset.attach_eq_univ]
  rw [← Equiv.sum_comp (poleIndexEquiv p)]
  apply Finset.sum_congr rfl
  intro idx hidx
  change (kernelRatElem p (i.val + j.val)).poleRes (poleNat p idx) *
      (poleNat p idx : ℚ) ^ (2 * k) =
    gammaWeight p k idx * (poleNode p idx) ^ (i.val + j.val)
  exact kernelResidue_weighted_eq_gamma p k (i.val + j.val) idx

/-- The derivative matrix has the Vandermonde diagonal factorization.
This proves the first structural half of Theorem 2.5 independently of the
constant-term remainder in the transformed pencil. -/
theorem M_deriv_factorization (p : HankelParams) (k : ℕ) :
    M_deriv p k =
      V_pole p * Matrix.diagonal (gammaWeight p k) * (V_pole p).transpose := by
  ext i j
  rw [M_deriv_entry_eq_gamma_sum]
  simp [V_pole, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, pow_add, mul_comm, mul_left_comm, mul_assoc]

/-- Rational content scales multiplicatively by `|c|` for any rational scalar `c : ℚ`. -/
lemma ratContent_C_mul (c : ℚ) (A : ℚ[X]) :
    ratContent (Polynomial.C c * A) = |c| * ratContent A := by
  by_cases hc : c = 0
  · subst c
    simp [(ratContent_eq_zero_iff (0 : ℚ[X])).2 rfl]
  · by_cases hA : A = 0
    · subst A
      simp [(ratContent_eq_zero_iff (0 : ℚ[X])).2 rfl]
    · let P1 := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Polynomial.C c * A)
      let b1 : ℤ := (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (Polynomial.C c * A)).choose
      let P2 := IsLocalization.integerNormalization (nonZeroDivisors ℤ) A
      let b2 : ℤ := (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) A).choose
      have hb1 := (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (Polynomial.C c * A)).choose_spec.2
      have hb2 := (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) A).choose_spec.2
      have hP1 : P1.map (algebraMap ℤ ℚ) = Polynomial.C (b1 : ℚ) * (Polynomial.C c * A) := by
        simpa [P1, b1, Algebra.smul_def] using hb1
      have hP2 : P2.map (algebraMap ℤ ℚ) = Polynomial.C (b2 : ℚ) * A := by
        simpa [P2, b2, Algebra.smul_def] using hb2
      have hden0 : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
      have hnum : (c.den : ℚ) * c = (c.num : ℚ) := by
        calc
          (c.den : ℚ) * c = (c.den : ℚ) * ((c.num : ℚ) / (c.den : ℚ)) := by
            rw [Rat.num_div_den c]
          _ = (c.num : ℚ) := by field_simp [hden0]
      have hcross :
          (Polynomial.C (c.den : ℤ) * Polynomial.C b2 * P1).map (algebraMap ℤ ℚ) =
          (Polynomial.C c.num * Polynomial.C b1 * P2).map (algebraMap ℤ ℚ) := by
        simp only [Polynomial.map_mul, Polynomial.map_C, hP1, hP2]
        ext n
        simp only [← Polynomial.C_mul, Polynomial.coeff_C_mul]
        calc
          ((c.den : ℚ) * (b2 : ℚ)) * ((b1 : ℚ) * (c * A.coeff n)) =
              ((c.den : ℚ) * c) * (b1 : ℚ) * ((b2 : ℚ) * A.coeff n) := by ring
          _ = (c.num : ℚ) * (b1 : ℚ) * ((b2 : ℚ) * A.coeff n) := by rw [hnum]
      have hcross_int :
          Polynomial.C (c.den : ℤ) * Polynomial.C b2 * P1 =
          Polynomial.C c.num * Polynomial.C b1 * P2 :=
        Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ) hcross
      have hcont := congrArg Polynomial.content hcross_int
      simp only [Polynomial.content_mul, Polynomial.content_C] at hcont
      have hcont_abs := congrArg abs hcont
      rw [← Int.abs_eq_normalize (c.den : ℤ), ← Int.abs_eq_normalize b2,
        ← Int.abs_eq_normalize c.num, ← Int.abs_eq_normalize b1] at hcont_abs
      have hden_nonneg : 0 ≤ (c.den : ℤ) := by exact_mod_cast Nat.zero_le c.den
      simp only [abs_mul, abs_abs, abs_of_nonneg hden_nonneg] at hcont_abs
      have hcont_q :
          (c.den : ℚ) * |(b2 : ℚ)| * |(P1.content : ℚ)| =
          |(c.num : ℚ)| * |(b1 : ℚ)| * |(P2.content : ℚ)| := by
        exact_mod_cast hcont_abs
      have hb1_ne : (b1 : ℚ) ≠ 0 := by
        exact_mod_cast nonZeroDivisors.ne_zero
          (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (Polynomial.C c * A)).choose_spec.1
      have hb2_ne : (b2 : ℚ) ≠ 0 := by
        exact_mod_cast nonZeroDivisors.ne_zero
          (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) A).choose_spec.1
      have habs_c : |c| = |(c.num : ℚ)| / (c.den : ℚ) := by
        calc
          |c| = |(c.num : ℚ) / (c.den : ℚ)| := congrArg abs (Rat.num_div_den c).symm
          _ = |(c.num : ℚ)| / (c.den : ℚ) := by
            rw [abs_div]
            have hdenposQ : 0 < (c.den : ℚ) := by exact_mod_cast c.den_pos
            simp only [abs_of_pos hdenposQ]
      unfold ratContent
      dsimp [P1, b1, P2, b2]
      rw [abs_div, abs_div, habs_c]
      have hb1abs_ne : |(b1 : ℚ)| ≠ 0 := abs_ne_zero.mpr hb1_ne
      have hb2abs_ne : |(b2 : ℚ)| ≠ 0 := abs_ne_zero.mpr hb2_ne
      calc
        |(P1.content : ℚ)| / |(b1 : ℚ)| =
            (|(P1.content : ℚ)| * (c.den : ℚ) * |(b2 : ℚ)|) /
              (|(b1 : ℚ)| * (c.den : ℚ) * |(b2 : ℚ)|) := by
          field_simp [hb1abs_ne, hb2abs_ne, hden0]
        _ = (|(c.num : ℚ)| * |(b1 : ℚ)| * |(P2.content : ℚ)|) /
              (|(b1 : ℚ)| * (c.den : ℚ) * |(b2 : ℚ)|) := by
          congr 1
          nlinarith [hcont_q]
        _ = (|(c.num : ℚ)| / (c.den : ℚ)) *
              (|(P2.content : ℚ)| / |(b2 : ℚ)|) := by
          field_simp [hb1abs_ne, hb2abs_ne, hden0]

/-- Full primitive-content conclusion of manuscript Theorem 2.4.
For invertible rational basis-change matrices and a nonzero determinant, the
normalized determinant is invariant up to sign. -/
theorem canonical_primitive_content_invariance
    (p : HankelParams) (G : Matrix (Fin p.h) (Fin p.h) ℚ[X])
    (MA MB : Matrix (Fin p.h) (Fin p.h) ℚ)
    (hG : G.det ≠ 0) (hMA : IsUnit MA.det) (hMB : IsUnit MB.det) :
    primitiveRationalPolynomial
        ((MA.map Polynomial.C * G * MB.transpose.map Polynomial.C).det) =
      primitiveRationalPolynomial G.det ∨
    primitiveRationalPolynomial
        ((MA.map Polynomial.C * G * MB.transpose.map Polynomial.C).det) =
      -primitiveRationalPolynomial G.det := by
  rw [canonical_basis_invariance G MA MB hMA hMB]
  let c : ℚ := MA.det * MB.det
  have hc_ne : c ≠ 0 := (hMA.mul hMB).ne_zero
  unfold primitiveRationalPolynomial
  rw [ratContent_C_mul c G.det]
  rcases lt_or_gt_of_ne hc_ne with hneg | hpos
  · right
    rw [abs_of_neg hneg]
    ext n
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_neg]
    field_simp [hc_ne]
    ring
  · left
    rw [abs_of_pos hpos]
    ext n
    simp only [Polynomial.coeff_C_mul]
    field_simp [hc_ne]
    ring

/-- Lagrange-basis transform of the Hankel pencil. -/
noncomputable def G_lagrange (p : HankelParams) (k : ℕ) :
    Matrix (Fin p.h) (Fin p.h) ℚ[X] :=
  (V_pole p)⁻¹.map Polynomial.C * G_pencil p k *
    ((V_pole p).transpose)⁻¹.map Polynomial.C

/-- Extracting the linear coefficient commutes with multiplication by the
constant basis-change matrices. -/
lemma G_lagrange_coeff_one (p : HankelParams) (k : ℕ) :
    (fun i j => (G_lagrange p k i j).coeff 1) =
      (V_pole p)⁻¹ * M_deriv p k * ((V_pole p).transpose)⁻¹ := by
  ext i j
  simp [G_lagrange, M_deriv, G_pencil, Matrix.mul_apply,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_C]

/-- The degree-one coefficient of the Lagrange-transformed pencil is diagonal.
The determinant nonvanishing of V_pole permits cancellation of the two inverse
basis changes. -/
lemma G_lagrange_coeff_one_diagonal (p : HankelParams) (k : ℕ) :
    (fun i j => (G_lagrange p k i j).coeff 1) =
      Matrix.diagonal (gammaWeight p k) := by
  have hunit : IsUnit (V_pole p).det :=
    isUnit_iff_ne_zero.mpr (V_pole_det_ne_zero p)
  have hunitT : IsUnit ((V_pole p).transpose).det := by
    simpa [Matrix.det_transpose] using hunit
  rw [G_lagrange_coeff_one, M_deriv_factorization]
  calc
    (V_pole p)⁻¹ *
        ((V_pole p) * Matrix.diagonal (gammaWeight p k) *
          (V_pole p).transpose) * ((V_pole p).transpose)⁻¹ =
      (((V_pole p)⁻¹ * V_pole p) * Matrix.diagonal (gammaWeight p k)) *
        ((V_pole p).transpose * ((V_pole p).transpose)⁻¹) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal (gammaWeight p k) := by
      rw [Matrix.nonsing_inv_mul (V_pole p) hunit,
        Matrix.mul_nonsing_inv ((V_pole p).transpose) hunitT]
      simp

/-- Coefficients above degree one vanish in a simple-pole affine factor. -/
lemma coeff_C_mul_X_sub_C_zero (a b : ℚ) (n : ℕ) (hn : 1 < n) :
    (Polynomial.C a * (Polynomial.X - Polynomial.C b)).coeff n = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have h1n : 1 ≠ n := by omega
  rw [Polynomial.coeff_C_mul]
  simp [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X, hn0, hn1, h1n]

lemma muPolePoly_coeff_zero_of_one_lt (k j n : ℕ) (hn : 1 < n) :
    (muPolePoly k j).coeff n = 0 := by
  have hn0 : n ≠ 0 := by omega
  unfold muPolePoly
  rw [Polynomial.coeff_add, coeff_C_mul_X_sub_C_zero _ _ n hn]
  simp [Polynomial.coeff_C, hn0]

lemma muFunctionalPoly_coeff_zero_of_one_lt (k : ℕ) (R : RatMomentElem)
    (n : ℕ) (hn : 1 < n) :
    (muFunctionalPoly k R).coeff n = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  simp [muFunctionalPoly, Polynomial.coeff_C_mul, Polynomial.coeff_C,
    muPolePoly_coeff_zero_of_one_lt, hn, hn0, hn1]

lemma G_pencil_coeff_zero_of_one_lt (p : HankelParams) (k : ℕ)
    (i j : Fin p.h) (n : ℕ) (hn : 1 < n) :
    (G_pencil p k i j).coeff n = 0 := by
  simpa [G_pencil] using
    (muFunctionalPoly_coeff_zero_of_one_lt k
      (kernelRatElem p (i.val + j.val)) n hn)

/-- The transformed pencil has degree at most one entrywise. -/
lemma G_lagrange_coeff_zero_of_one_lt (p : HankelParams) (k : ℕ)
    (i j : Fin p.h) (n : ℕ) (hn : 1 < n) :
    (G_lagrange p k i j).coeff n = 0 := by
  classical
  unfold G_lagrange
  simp [Matrix.mul_apply, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
    G_pencil_coeff_zero_of_one_lt p k, hn]

lemma G_lagrange_natDegree_le_one (p : HankelParams) (k : ℕ)
    (i j : Fin p.h) : (G_lagrange p k i j).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact G_lagrange_coeff_zero_of_one_lt p k i j n (by omega)

/-- Off-diagonal transformed entries are constant because their degree-one
coefficient vanishes and every transformed entry has degree at most one. -/
lemma G_lagrange_offdiag_natDegree_zero (p : HankelParams) (k : ℕ)
    (i j : Fin p.h) (hij : i ≠ j) :
    (G_lagrange p k i j).natDegree = 0 := by
  have hcoeff : (G_lagrange p k i j).coeff 1 = 0 := by
    have hdiag := congrFun (congrFun (G_lagrange_coeff_one_diagonal p k) i) j
    simpa [Matrix.diagonal_apply, hij] using hdiag
  have hdegree : (G_lagrange p k i j).natDegree ≤ 0 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    by_cases hn1 : n = 1
    · simpa [hn1] using hcoeff
    · exact G_lagrange_coeff_zero_of_one_lt p k i j n (by omega)
  omega

/-- Every diagonal entry is affine with the prescribed slope; its constant term
is chosen to match the coefficient at zero. -/
lemma G_lagrange_diagonal_affine (p : HankelParams) (k : ℕ)
    (i : Fin p.h) :
    ∃ c : ℚ,
      G_lagrange p k i i =
        Polynomial.C (gammaWeight p k i) *
          (Polynomial.X -
            Polynomial.C (harmonicWeight (2 * k + 1) (poleNat p i))) +
          Polynomial.C c := by
  let g := gammaWeight p k i
  let H := harmonicWeight (2 * k + 1) (poleNat p i)
  let c := (G_lagrange p k i i).coeff 0 + g * H
  refine ⟨c, ?_⟩
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [c, g, H, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_C, Polynomial.coeff_X] <;> ring
  · by_cases hn1 : n = 1
    · subst n
      have hdiag := congrFun (congrFun (G_lagrange_coeff_one_diagonal p k) i) i
      have hcoeff : (G_lagrange p k i i).coeff 1 = g := by
        simpa [g, Matrix.diagonal_apply] using hdiag
      simpa [g, H, coeff_C_mul_X_sub_C] using hcoeff
    · have hn : 1 < n := by omega
      have h1n : 1 ≠ n := by omega
      simp [hn0, hn1, h1n, hn, g, H,
        G_lagrange_coeff_zero_of_one_lt p k i i n hn,
        coeff_C_mul_X_sub_C_zero, Polynomial.coeff_C_mul,
        Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X]

/-- Manuscript Theorem 2.5 (Lagrange pole diagonalization). The statement includes
the derivative-matrix factorization, X-independence of off-diagonal entries, and
the full affine formula on each diagonal entry. -/
theorem lagrange_pole_diagonalization (p : HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    M_deriv p k =
      V_pole p * Matrix.diagonal (gammaWeight p k) * (V_pole p).transpose ∧
    (∀ a b : Fin p.h, a ≠ b → (G_lagrange p k a b).natDegree = 0) ∧
    (∀ a : Fin p.h, ∃ c : ℚ,
      G_lagrange p k a a =
        Polynomial.C (gammaWeight p k a) *
          (Polynomial.X -
            Polynomial.C (harmonicWeight (2 * k + 1) (poleNat p a))) +
          Polynomial.C c) := by
  refine ⟨M_deriv_factorization p k, ?_, ?_⟩
  · intro a b hab
    exact G_lagrange_offdiag_natDegree_zero p k a b hab
  · intro a
    exact G_lagrange_diagonal_affine p k a

/-!
# Consequences of the pole factorization
-/

/-- Exact Vandermonde determinant formula for the ordered negative-square poles. -/
theorem V_pole_det_formula (p : HankelParams) :
    (V_pole p).det =
      ∏ i : Fin p.h, ∏ j ∈ Finset.Ioi i,
        (poleNode p j - poleNode p i) := by
  change (Matrix.vandermonde (poleNode p)).transpose.det = _
  rw [Matrix.det_transpose]
  exact Matrix.det_vandermonde (poleNode p)

/-- Determinant factorization induced by the pole Vandermonde basis. -/
theorem det_M_deriv_factorization (p : HankelParams) (k : ℕ) :
    (M_deriv p k).det =
      (V_pole p).det ^ 2 * ∏ idx : Fin p.h, gammaWeight p k idx := by
  rw [M_deriv_factorization]
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

/-- Nonsingularity of the derivative matrix follows from the Lagrange
factorization and nonzero diagonal weights. This is the key linear-algebra
input for the exact-degree part of Section 3. -/
theorem M_deriv_det_ne_zero (p : HankelParams) (k : ℕ) :
    (M_deriv p k).det ≠ 0 := by
  rw [det_M_deriv_factorization]
  apply mul_ne_zero
  · exact pow_ne_zero 2 (V_pole_det_ne_zero p)
  · apply Finset.prod_ne_zero_iff.mpr
    intro idx hidx
    exact gammaWeight_ne_zero p k idx

end

end Zetahyperbolic
