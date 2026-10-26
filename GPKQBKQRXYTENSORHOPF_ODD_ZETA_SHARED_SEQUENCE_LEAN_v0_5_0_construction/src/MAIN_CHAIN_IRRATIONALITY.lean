import MAIN_CHAIN_ASSEMBLED
import Theorem_4_1_Direct_Irrationality_From_Decay
import Theorem_2_4_Primitive_Normalization_Minimality
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The general odd-weight irrationality bridge for the actual determinant family.
The positive primitive integer normalization, its degree, and its nonzero value
are constructed. The one remaining arithmetic/normalized-value estimate is named
`NormalizedQuadraticDecay`; no such decay estimate is asserted here.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.GeneralIrrationality

/-- The positive primitive integer normalization of the actual determinant. -/
def normalization (p : Real.Parameters) :
    BasisInvariance.PrimitiveNormalization (Real.delta p) :=
  BasisInvariance.primitiveNormalization (Real.delta p)
    (PoleDiagonalization.delta_ne_zero p)

def primitivePolynomial (p : Real.Parameters) : ℤ[X] :=
  (normalization p).polynomial

theorem primitivePolynomial_isPrimitive (p : Real.Parameters) :
    (primitivePolynomial p).IsPrimitive :=
  (normalization p).primitive

theorem primitivePolynomial_eval (p : Real.Parameters) (x : ℝ) :
    RealTransfer.evalReal (primitivePolynomial p) x =
      ((normalization p).scale : ℝ) * Real.evalQ (Real.delta p) x := by
  have hcomp : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext z
    simp
  calc
    RealTransfer.evalReal (primitivePolynomial p) x =
        Real.evalQ ((primitivePolynomial p).map (Int.castRingHom ℚ)) x := by
      simp [RealTransfer.evalReal, Real.evalQ, Real.realPolynomial,
        Polynomial.map_map, hcomp]
    _ = Real.evalQ (C (normalization p).scale * Real.delta p) x := by
      rw [show (primitivePolynomial p).map (Int.castRingHom ℚ) =
        C (normalization p).scale * Real.delta p from (normalization p).identity]
    _ = _ := by simp [Real.evalQ, Real.realPolynomial]

theorem primitivePolynomial_natDegree (p : Real.Parameters) :
    (primitivePolynomial p).natDegree = p.h := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  calc
    (primitivePolynomial p).natDegree =
        ((primitivePolynomial p).map (Int.castRingHom ℚ)).natDegree :=
      (Polynomial.natDegree_map_eq_of_injective hinj _).symm
    _ = (C (normalization p).scale * Real.delta p).natDegree := by
      rw [show (primitivePolynomial p).map (Int.castRingHom ℚ) =
        C (normalization p).scale * Real.delta p from (normalization p).identity]
    _ = (Real.delta p).natDegree :=
      Polynomial.natDegree_C_mul (ne_of_gt (normalization p).scale_pos)
    _ = p.h := General.delta_degree p

theorem primitivePolynomial_natDegree_le_K (p : Real.Parameters) :
    (primitivePolynomial p).natDegree ≤ p.K := by
  rw [primitivePolynomial_natDegree]
  exact Nat.sub_le _ _

/-- Strict positivity is a proved consequence of the analytic assembly. -/
theorem primitivePolynomial_eval_pos (p : Real.Parameters) (hp : Real.Admissible p) :
    0 < RealTransfer.evalReal (primitivePolynomial p) (Real.zeta p.weight) := by
  rw [primitivePolynomial_eval, Real.delta_eval_eq_det_gram]
  exact mul_pos (by exact_mod_cast (normalization p).scale_pos)
    (GRAM_POSITIVE p hp).det_pos

/-- The remaining estimate is on the primitive integer polynomial itself.
The positive quadratic rate may depend on the fixed odd weight and family. -/
def NormalizedQuadraticDecay (p : ℕ → Real.Parameters) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    RealTransfer.evalReal (primitivePolynomial (p n)) (Real.zeta (p n).weight) ≤
      _root_.Real.exp (-c * ((p n).K : ℝ) ^ 2)

/-- Any explicit positive integral rescaling with eventual quadratic decay
establishes the canonical primitive decay estimate. -/
theorem normalizedQuadraticDecay_of_integral_rescalings
    (p : ℕ → Real.Parameters) (g : ℕ → ℤ[X]) (a : ℕ → ℚ)
    (ha : ∀ n, 0 < a n)
    (hg : ∀ n, (g n).map (Int.castRingHom ℚ) = C (a n) * Real.delta (p n))
    (hdecay : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      |RealTransfer.evalReal (g n) (Real.zeta (p n).weight)| ≤
        _root_.Real.exp (-c * ((p n).K : ℝ) ^ 2)) :
    NormalizedQuadraticDecay p := by
  obtain ⟨c, hc, n₀, hupper⟩ := hdecay
  refine ⟨c, hc, n₀, ?_⟩
  intro n hn
  have hminimal :
      |RealTransfer.evalReal (primitivePolynomial (p n)) (Real.zeta (p n).weight)| ≤
        |RealTransfer.evalReal (g n) (Real.zeta (p n).weight)| := by
    simpa only [RealTransfer.evalReal, primitivePolynomial, algebraMap_int_eq] using
      BasisInvariance.primitiveNormalization_abs_eval_int_le
        (normalization (p n)) (ha n) (hg n) (Real.zeta (p n).weight)
  exact (le_abs_self _).trans (hminimal.trans (hupper n hn))

/-- Every tail of the family contains arbitrarily large parameter values. -/
def UnboundedOnTails (p : ℕ → Real.Parameters) : Prop :=
  ∀ n₀ B : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ B ≤ (p n).K

/-- Removing any finite initial segment preserves unbounded natural values. -/
theorem unboundedOnTails_of_unbounded (p : ℕ → Real.Parameters)
    (h : ∀ B : ℕ, ∃ n : ℕ, B ≤ (p n).K) : UnboundedOnTails p := by
  intro n₀ B
  obtain ⟨n, hn⟩ := h (B + (∑ i ∈ Finset.range n₀, (p i).K) + 1)
  refine ⟨n, ?_, by omega⟩
  by_contra hnot
  have hmem : n ∈ Finset.range n₀ := Finset.mem_range.mpr (by omega)
  have hle : (p n).K ≤ ∑ i ∈ Finset.range n₀, (p i).K :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (p i).K) hmem
  omega

private theorem quadratic_denominator_squeeze {b d K : ℕ} {c : ℝ}
    (hb : 0 < b) (hd : d ≤ K) (hK : 0 < (K : ℝ))
    (hlarge : _root_.Real.log (b : ℝ) < c * (K : ℝ)) :
    (b : ℝ) ^ d * _root_.Real.exp (-c * (K : ℝ) ^ 2) < 1 := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  calc
    (b : ℝ) ^ d * _root_.Real.exp (-c * (K : ℝ) ^ 2) ≤
        (b : ℝ) ^ K * _root_.Real.exp (-c * (K : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb1 hd)
        (_root_.Real.exp_pos _).le
    _ = _root_.Real.exp ((K : ℝ) * _root_.Real.log (b : ℝ) - c * (K : ℝ) ^ 2) := by
      rw [sub_eq_add_neg, _root_.Real.exp_add, _root_.Real.exp_nat_mul,
        _root_.Real.exp_log hbR]
      congr 2
      ring
    _ < 1 := _root_.Real.exp_lt_one_iff.mpr (by
      have := mul_lt_mul_of_pos_left hlarge hK
      nlinarith)

/-- Any unbounded admissible family of one odd weight with the stated
normalized decay proves irrationality; positivity and degree are not inputs. -/
theorem irrational_zeta_of_normalized_decay (k : ℕ) (p : ℕ → Real.Parameters)
    (hp : ∀ n, Real.Admissible (p n)) (hweight : ∀ n, (p n).k = k)
    (hunbounded : UnboundedOnTails p)
    (hdecay : NormalizedQuadraticDecay p) : Irrational (Real.zeta (2 * k + 1)) := by
  obtain ⟨c, hc, n₀, hupper⟩ := hdecay
  have hw (n : ℕ) : (p n).weight = 2 * k + 1 := by
    simp [Real.Parameters.weight, hweight n]
  apply RealTransfer.irrational_of_decay_and_denominator_budget
    (Q := fun n => primitivePolynomial (p n))
    (budget := fun n => _root_.Real.exp (-c * ((p n).K : ℝ) ^ 2))
    (n₀ := n₀) (b₀ := 0)
  · constructor
    · intro n _
      rw [← hw n]
      exact ne_of_gt (primitivePolynomial_eval_pos (p n) (hp n))
    · intro n hn
      rw [← hw n, abs_of_pos (primitivePolynomial_eval_pos (p n) (hp n))]
      exact hupper n hn
  · intro b hb _
    obtain ⟨B, hB⟩ := exists_nat_gt (max 0 (_root_.Real.log (b : ℝ) / c))
    obtain ⟨n, hn₀, hn⟩ := hunbounded n₀ B
    have hnR : (B : ℝ) ≤ ((p n).K : ℝ) := by exact_mod_cast hn
    refine ⟨n, hn₀, quadratic_denominator_squeeze hb
      (primitivePolynomial_natDegree_le_K (p n)) ?_ ?_⟩
    · exact lt_of_le_of_lt (le_max_left _ _) (hB.trans_le hnR)
    · rw [mul_comm c]
      apply (div_lt_iff₀ hc).mp
      exact lt_of_le_of_lt (le_max_right _ _) (hB.trans_le hnR)

/-- The same result stated directly using Mathlib's Riemann zeta function. -/
theorem irrational_riemannZeta_of_normalized_decay (k : ℕ) (hk : 0 < k)
    (p : ℕ → Real.Parameters) (hp : ∀ n, Real.Admissible (p n))
    (hweight : ∀ n, (p n).k = k)
    (hunbounded : UnboundedOnTails p)
    (hdecay : NormalizedQuadraticDecay p) :
    Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  rw [← Real.zeta_eq_riemannZeta_re (show 1 < 2 * k + 1 by omega)]
  exact irrational_zeta_of_normalized_decay k p hp hweight hunbounded hdecay

/-- The single open family estimate for one odd weight, with its admissible
parameter family and unbounded K made explicit. -/
def OddWeightDecayHypothesis (k : ℕ) : Prop :=
  ∃ p : ℕ → Real.Parameters,
    (∀ n, Real.Admissible (p n)) ∧
    (∀ n, (p n).k = k) ∧
    UnboundedOnTails p ∧
    NormalizedQuadraticDecay p

theorem irrational_odd_zeta (k : ℕ) (h : OddWeightDecayHypothesis k) :
    Irrational (Real.zeta (2 * k + 1)) := by
  obtain ⟨p, hp, hw, hu, hd⟩ := h
  exact irrational_zeta_of_normalized_decay k p hp hw hu hd

theorem all_odd_zeta_irrational
    (h : ∀ k : ℕ, 0 < k → OddWeightDecayHypothesis k) :
    ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  obtain ⟨p, hp, hw, hu, hd⟩ := h k hk
  exact irrational_riemannZeta_of_normalized_decay k hk p hp hw hu hd

/-- An explicit structural family: m=3, N=3(n+1), K=30(n+1).
It is available for every positive k; no decay is claimed for it. -/
def affineFamily (k n : ℕ) : Real.Parameters :=
  ⟨k, 3, 3 * (n + 1), 30 * (n + 1)⟩

theorem affineFamily_admissible (k : ℕ) (hk : 0 < k) (n : ℕ) :
    Real.Admissible (affineFamily k n) := by
  constructor <;> dsimp [affineFamily] <;> omega

@[simp] theorem affineFamily_k (k n : ℕ) : (affineFamily k n).k = k := rfl

@[simp] theorem affineFamily_h (k n : ℕ) :
    (affineFamily k n).h = 27 * (n + 1) := by
  dsimp [affineFamily, Real.Parameters.h]
  omega

theorem affineFamily_unbounded (k : ℕ) : UnboundedOnTails (affineFamily k) := by
  intro n₀ B
  refine ⟨n₀ + B, by omega, ?_⟩
  dsimp [affineFamily]
  omega

/-- A concrete optional target C_k. It is stronger than the existential family
hypothesis because it fixes m,N,K to the displayed affine family. -/
def AffineFamilyDecay (k : ℕ) : Prop := NormalizedQuadraticDecay (affineFamily k)

theorem oddWeightDecayHypothesis_of_affineFamilyDecay (k : ℕ) (hk : 0 < k)
    (h : AffineFamilyDecay k) : OddWeightDecayHypothesis k :=
  ⟨affineFamily k, affineFamily_admissible k hk, affineFamily_k k,
    affineFamily_unbounded k, h⟩

theorem all_odd_zeta_irrational_of_affineFamilyDecay
    (h : ∀ k : ℕ, 0 < k → AffineFamilyDecay k) :
    ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  apply all_odd_zeta_irrational
  intro k hk
  exact oddWeightDecayHypothesis_of_affineFamilyDecay k hk (h k hk)

end ManuscriptChain.GeneralIrrationality

#print axioms ManuscriptChain.GeneralIrrationality.primitivePolynomial_eval_pos
#print axioms ManuscriptChain.GeneralIrrationality.normalizedQuadraticDecay_of_integral_rescalings
#print axioms ManuscriptChain.GeneralIrrationality.irrational_zeta_of_normalized_decay
#print axioms ManuscriptChain.GeneralIrrationality.irrational_riemannZeta_of_normalized_decay
#print axioms ManuscriptChain.GeneralIrrationality.all_odd_zeta_irrational
#print axioms ManuscriptChain.GeneralIrrationality.all_odd_zeta_irrational_of_affineFamilyDecay
