import ZHPreprint.Algebra
import ZHPreprint.RawGramRate

/-!
# Actual ZH primitive growth: seed-to-all-odd conditional transfer

The family is the actual rational determinant imported from the pinned ZH
repository, not a newly axiomatized polynomial sequence. No custom axiom,
`sorry`, admitted theorem, or assumed irrationality-transfer rule is used.

The adopted conjecture is `PRIMITIVE_GROWTH_CONJECTURE`. The ZH manuscript
weight-five estimate is `WeightFiveIntegralSeed`. The new preprint's analytic
Gram estimate is separately tracked as `FiniteGramUpperBound`: it is a
remaining Lean formalization obligation, NOT a ZH theorem or a second
adopted conjecture. The exported theorem displays that premise explicitly.

Source status: construction candidate; native Windows compiler and independent
transitive axiom walk must run before any compiled-proof claim.
-/

noncomputable section

namespace ZHPreprint

open Polynomial
open ManuscriptChain

/-- The preprint's t is the positive integer n+1. -/
def index (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

def squareIndex (n : ℕ) : ℝ := index n ^ 2

def seedRate : ℝ := 9 / 25

theorem seedRate_pos : 0 < seedRate := by norm_num [seedRate]

theorem squareIndex_nonneg (n : ℕ) : 0 ≤ squareIndex n := by
  exact sq_nonneg _

/-- Exact manuscript seed after primitive normalization. Strict positivity
is already a theorem about the actual ZH family. -/
def WeightFiveSeed : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    value 2 n ≤ _root_.Real.exp (-seedRate * squareIndex n)

/-- ZH (4.3) in its positive rational integral-rescaling form. Quantifiers
are eventual, and the integral polynomial is attached to the actual delta. -/
def WeightFiveIntegralSeed : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ a : ℚ, ∃ Q : ℤ[X], 0 < a ∧
      Q.map (Int.castRingHom ℚ) = C a * Real.delta (parameters 2 n) ∧
      0 < RealTransfer.evalReal Q (Real.zeta 5) ∧
      RealTransfer.evalReal Q (Real.zeta 5) ≤
        _root_.Real.exp (-seedRate * squareIndex n)

/-- Primitive normalization decreases the positive integral seed. -/
theorem weightFiveSeed_of_integralSeed (h : WeightFiveIntegralSeed) :
    WeightFiveSeed := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨a, Q, ha, hQ, hpos, hupper⟩ := hN n hn
  have hminimal : |value 2 n| ≤ |RealTransfer.evalReal Q (Real.zeta 5)| := by
    simpa only [value, primitive, GeneralIrrationality.primitivePolynomial,
      RealTransfer.evalReal, algebraMap_int_eq,
      show (2 : ℕ) * 2 + 1 = 5 from rfl] using
      BasisInvariance.primitiveNormalization_abs_eval_int_le
        (GeneralIrrationality.normalization (parameters 2 n)) ha hQ (Real.zeta 5)
  rw [abs_of_pos (value_pos 2 n (by omega)), abs_of_pos hpos] at hminimal
  exact hminimal.trans hupper

/-- The exact conjecture from the preprint, in eventual exponential form.
The positive margin and threshold may depend on the fixed weight. -/
def PRIMITIVE_GROWTH_CONJECTURE : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      leading k n ≤
        _root_.Real.exp ((seedRate - δ) * squareIndex n) * leading 2 n

/-- Arbitrarily small positive quadratic upper loss at one fixed weight.
This is a target for the new analytic Gram proof, not an automatic consequence
of finite Gram positivity. -/
def RawGramSubquadratic (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    gram k n ≤ _root_.Real.exp (ε * squareIndex n) * gram 2 n

/-- The precise finite bound proved on paper in the preprint, restricted to
the canonical growing family. Its Lean proof from the concrete integrals is
still outstanding. This declaration is a proposition, not an axiom. -/
def FiniteGramUpperBound : Prop :=
  ∀ k n : ℕ, 0 < k →
    gram (k + 1) n ≤ RawGramRate.rawGramBound k (n + 1) * gram k n

/-- An eventual positive quadratic decay rate for the primitive polynomial. -/
def PrimitiveQuadraticDecay (k : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    value k n ≤ _root_.Real.exp (-c * squareIndex n)

/-- The finite analytic estimate implies the precise asymptotic comparison
needed below; this conversion has a proof and introduces no extra premise. -/
theorem rawGramSubquadratic_of_finiteBound
    (hfinite : FiniteGramUpperBound) (k : ℕ) (hk : 2 ≤ k) :
    RawGramSubquadratic k := by
  simpa only [RawGramSubquadratic, RawGramRate.SubquadraticUpperSucc,
    squareIndex, index] using
    RawGramRate.fromTwo_succ_of_finite_bounds gram
      (fun k n hk => (gram_pos k n hk).le) hfinite k hk

/-- Weight five uses its own seed; no growth conjecture is needed at k=2. -/
theorem primitiveQuadraticDecay_two (hseed : WeightFiveSeed) :
    PrimitiveQuadraticDecay 2 := by
  obtain ⟨N, hN⟩ := hseed
  exact ⟨seedRate, seedRate_pos, N, hN⟩

/-- Main arithmetic bridge: relative leading growth strictly below the seed
rate, combined with subquadratic raw Gram loss, gives primitive decay. -/
theorem primitiveQuadraticDecay_of_conjecture
    (hseed : WeightFiveSeed) (hgrowth : PRIMITIVE_GROWTH_CONJECTURE)
    (k : ℕ) (hk : 3 ≤ k) (hgram : RawGramSubquadratic k) :
    PrimitiveQuadraticDecay k := by
  obtain ⟨δ, hδ, NL, hL⟩ := hgrowth k hk
  obtain ⟨NG, hG⟩ := hgram (δ / 2) (half_pos hδ)
  obtain ⟨N0, h0⟩ := hseed
  refine ⟨δ / 2, half_pos hδ, max N0 (max NL NG), ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := (le_max_left _ _).trans hn
  have hnL : NL ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnG : NG ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  calc
    value k n ≤ value 2 n * _root_.Real.exp
        (((seedRate - δ) * squareIndex n) + ((δ / 2) * squareIndex n)) :=
      value_upper_of_leading_gram_bounds k n (by omega)
        ((seedRate - δ) * squareIndex n) ((δ / 2) * squareIndex n)
        (hL n hnL) (hG n hnG)
    _ ≤ _root_.Real.exp (-seedRate * squareIndex n) * _root_.Real.exp
        (((seedRate - δ) * squareIndex n) + ((δ / 2) * squareIndex n)) :=
      mul_le_mul_of_nonneg_right (h0 n hn0) (_root_.Real.exp_pos _).le
    _ = _root_.Real.exp (-(δ / 2) * squareIndex n) := by
      rw [← _root_.Real.exp_add]
      congr 1
      ring

/-- Conversion of t^2 decay to the repository's K^2 convention, K=30t. -/
theorem affineFamilyDecay_of_primitiveQuadraticDecay (k : ℕ)
    (h : PrimitiveQuadraticDecay k) :
    GeneralIrrationality.AffineFamilyDecay k := by
  obtain ⟨c, hc, N, hN⟩ := h
  refine ⟨c / 900, div_pos hc (by norm_num), N, ?_⟩
  intro n hn
  have hK : ((parameters k n).K : ℝ) = 30 * index n := by
    simp [parameters, GeneralIrrationality.affineFamily, index]
  change value k n ≤
    _root_.Real.exp (-(c / 900) * ((parameters k n).K : ℝ) ^ 2)
  calc
    value k n ≤ _root_.Real.exp (-c * squareIndex n) := hN n hn
    _ = _root_.Real.exp (-(c / 900) * ((parameters k n).K : ℝ) ^ 2) := by
      rw [hK]
      congr 1
      unfold squareIndex
      ring

/-- The actual repository theorem discharges the integer-denominator
argument; irrationality transfer is not assumed as a custom ZH axiom. -/
theorem irrational_of_primitiveQuadraticDecay (k : ℕ) (hk : 0 < k)
    (h : PrimitiveQuadraticDecay k) :
    Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  exact GeneralIrrationality.irrational_riemannZeta_of_normalized_decay k hk
    (GeneralIrrationality.affineFamily k)
    (fun n => GeneralIrrationality.affineFamily_admissible k hk n)
    (fun n => GeneralIrrationality.affineFamily_k k n)
    (GeneralIrrationality.affineFamily_unbounded k)
    (affineFamilyDecay_of_primitiveQuadraticDecay k h)

/-- All odd zeta values at least five, conditional on the one adopted
conjecture, the seed, and the explicitly displayed Gram proof frontier. -/
theorem all_odd_ge_five_of_seed_growth_and_gram
    (hseed : WeightFiveSeed) (hgrowth : PRIMITIVE_GROWTH_CONJECTURE)
    (hgram : ∀ k : ℕ, 3 ≤ k → RawGramSubquadratic k) :
    ∀ k : ℕ, 2 ≤ k →
      Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  apply irrational_of_primitiveQuadraticDecay k (by omega)
  by_cases htwo : k = 2
  · subst k
    exact primitiveQuadraticDecay_two hseed
  · have hk3 : 3 ≤ k := by omega
    exact primitiveQuadraticDecay_of_conjecture hseed hgrowth k hk3 (hgram k hk3)

/-- The preprint's final conclusion with its current formal proof frontier
explicit. Apéry is a separate theorem input and no k=1 decay is postulated. -/
theorem all_odd_irrational_of_seed_growth_and_gram
    (hseed : WeightFiveSeed) (hgrowth : PRIMITIVE_GROWTH_CONJECTURE)
    (hgram : ∀ k : ℕ, 3 ≤ k → RawGramSubquadratic k)
    (hapery : Irrational (riemannZeta (3 : ℂ)).re) :
    ∀ k : ℕ, 0 < k →
      Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  by_cases hone : k = 1
  · subst k
    simpa using hapery
  · exact all_odd_ge_five_of_seed_growth_and_gram hseed hgrowth hgram k (by omega)

/-- Final concrete-source endpoint. The four inputs are deliberately visible:
the ZH seed, the adopted leading-growth conjecture, the unformalized finite
Gram estimate, and the independent weight-three result. A successful axiom
audit of this conditional theorem does not discharge any of these inputs. -/
theorem all_odd_irrational_of_integralSeed_growth_and_finiteGram
    (hseed : WeightFiveIntegralSeed)
    (hgrowth : PRIMITIVE_GROWTH_CONJECTURE)
    (hfinite : FiniteGramUpperBound)
    (hapery : Irrational (riemannZeta (3 : ℂ)).re) :
    ∀ k : ℕ, 0 < k →
      Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  exact all_odd_irrational_of_seed_growth_and_gram
    (weightFiveSeed_of_integralSeed hseed) hgrowth
    (fun k hk => rawGramSubquadratic_of_finiteBound hfinite k (by omega)) hapery

end ZHPreprint

#print axioms ZHPreprint.weightFiveSeed_of_integralSeed
#print axioms ZHPreprint.rawGramSubquadratic_of_finiteBound
#print axioms ZHPreprint.primitiveQuadraticDecay_of_conjecture
#print axioms ZHPreprint.affineFamilyDecay_of_primitiveQuadraticDecay
#print axioms ZHPreprint.irrational_of_primitiveQuadraticDecay
#print axioms ZHPreprint.all_odd_irrational_of_seed_growth_and_gram
#print axioms ZHPreprint.all_odd_irrational_of_integralSeed_growth_and_finiteGram
