import ZHPreprint.WeightDependentConjecture
import ZHPreprint.InductionRates

/-!
# Conditional induction on actual ZH profiles

The profiles, leading coefficients, determinant ratios and primitive values
in this file are the existing concrete ZH constructions. The paper variable
t is n+1, so every sampled parameter value is positive.

There are two deliberately distinct interfaces.

* ProductInductionInput supplies an actual positive quadratic base estimate
  and the actual adjacent product estimates. Its irrationality transfer uses
  no separate analytic base estimate.
* HeightInductionInput supplies the proposed weight-five primitive-height
  estimate and the adjacent product estimates. Its transfer additionally
  requires AnalyticBaseInput. That analytic estimate is a paper-level result
  awaiting its own Lean formalization; it is NOT installed as an axiom and is
  NOT silently discharged here.

None of the input propositions is asserted. No successful profile or open
estimate is constructed by this file. Native Windows compilation and the
independent dependency audit remain pending. No local Lean run is authorized.
-/

noncomputable section

namespace ZHPreprint.ProfileInduction

open ManuscriptChain

/-- The fixed geometry at one weight, with its exact admissibility data. -/
structure Profile where
  m : ℕ
  a : ℕ
  b : ℕ
  hm : 0 < m
  ha : 0 < a
  hab : a < b

theorem Profile.b_pos (p : Profile) : 0 < p.b := lt_trans p.ha p.hab

/-- The actual family at weight 2k+1, sampled at t=n+1. -/
def Profile.atWeight (p : Profile) (k n : ℕ) : Real.Parameters :=
  WeightDependent.profile k p.m p.a p.b n

theorem Profile.atWeight_admissible (p : Profile) (k : ℕ)
    (hk : 0 < k) (n : ℕ) : Real.Admissible (p.atWeight k n) :=
  WeightDependent.profile_admissible k p.m p.a p.b hk p.hm p.ha p.hab n

@[simp] theorem Profile.atWeight_k (p : Profile) (k n : ℕ) :
    (p.atWeight k n).k = k := rfl

theorem Profile.atWeight_unbounded (p : Profile) (k : ℕ) :
    GeneralIrrationality.UnboundedOnTails (p.atWeight k) :=
  WeightDependent.profile_unbounded k p.m p.a p.b p.b_pos

theorem Profile.primitive_degree (p : Profile) (k n : ℕ) :
    (GeneralIrrationality.primitivePolynomial (p.atWeight k n)).natDegree =
      (p.b - p.a) * (n + 1) :=
  WeightDependent.profile_primitive_degree k p.m p.a p.b n

/-- Absolute leading coefficient of the actual canonical primitive polynomial. -/
def leading (p : Profile) (k n : ℕ) : ℝ :=
  LeadingCoefficientGap.leadingSize (p.atWeight k n)

/-- Actual positive Gram determinant divided by the absolute slope determinant. -/
def ratio (p : Profile) (k n : ℕ) : ℝ :=
  LeadingCoefficientGap.determinantRatio (p.atWeight k n)

/-- The actual positive primitive value, expressed as L times R. -/
def value (p : Profile) (k n : ℕ) : ℝ := leading p k n * ratio p k n

theorem leading_ge_one (p : Profile) (k n : ℕ) : 1 ≤ leading p k n :=
  LeadingCoefficientGap.leadingSize_ge_one (p.atWeight k n)

theorem leading_nonneg (p : Profile) (k n : ℕ) : 0 ≤ leading p k n :=
  (show (0 : ℝ) ≤ 1 by norm_num).trans (leading_ge_one p k n)

theorem ratio_pos (p : Profile) (k : ℕ) (hk : 0 < k) (n : ℕ) :
    0 < ratio p k n :=
  LeadingCoefficientGap.determinantRatio_pos _ (p.atWeight_admissible k hk n)

theorem value_pos (p : Profile) (k : ℕ) (hk : 0 < k) (n : ℕ) :
    0 < value p k n :=
  mul_pos ((show (0 : ℝ) < 1 by norm_num).trans_le (leading_ge_one p k n))
    (ratio_pos p k hk n)

/-- No replacement polynomial or independently chosen normalization occurs. -/
theorem primitive_eval_eq_value (p : Profile) (k n : ℕ) :
    RealTransfer.evalReal
        (GeneralIrrationality.primitivePolynomial (p.atWeight k n))
        (Real.zeta (p.atWeight k n).weight) = value p k n :=
  LeadingCoefficientGap.primitivePolynomial_eval_eq (p.atWeight k n)

/-- Convert the paper t-squared convention to the upstream K-squared one. -/
theorem normalizedDecay_of_quadraticDecay (p : Profile) (k : ℕ)
    (h : InductionRates.QuadraticDecay (value p k)) :
    GeneralIrrationality.NormalizedQuadraticDecay (p.atWeight k) := by
  obtain ⟨ε, hε, N, hupper⟩ := h
  have hbR : (0 : ℝ) < (p.b : ℝ) := by exact_mod_cast p.b_pos
  have hb2 : (0 : ℝ) < (p.b : ℝ) ^ 2 := pow_pos hbR 2
  refine ⟨ε / (p.b : ℝ) ^ 2, div_pos hε hb2, N, ?_⟩
  intro n hn
  rw [primitive_eval_eq_value]
  have hscale :
      -(ε / (p.b : ℝ) ^ 2) * ((p.atWeight k n).K : ℝ) ^ 2 =
        -ε * InductionRates.time n ^ 2 := by
    simpa only [Profile.atWeight, neg_div, WeightDependent.time,
      InductionRates.time] using
      WeightDependent.rate_rescale k p.m p.a p.b n p.b_pos (-ε)
  rw [hscale]
  exact hupper n hn

theorem irrational_of_quadraticDecay (p : Profile) (k : ℕ) (hk : 0 < k)
    (h : InductionRates.QuadraticDecay (value p k)) :
    Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re :=
  GeneralIrrationality.irrational_riemannZeta_of_normalized_decay k hk
    (p.atWeight k) (p.atWeight_admissible k hk) (p.atWeight_k k)
    (p.atWeight_unbounded k) (normalizedDecay_of_quadraticDecay p k h)

/-- The specific weight-five geometry discussed in the paper derivation. -/
def baseProfile : Profile :=
  ⟨1, 1, 2, by decide, by decide, by decide⟩

/-- Exact paper constant; no decimal approximation is used. -/
def delta : ℝ :=
  2 * _root_.Real.log (_root_.Real.pi / 2) + (9 / 2 : ℝ) * _root_.Real.log 3

/-- OPEN arithmetic base input on the actual weight-five leading coefficient. -/
def BaseHeightInput : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ A < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    leading baseProfile 2 n ≤ _root_.Real.exp (A * InductionRates.time n ^ 2)

/-- Explicit remaining Lean analytic obligation. The on-paper estimate is
not promoted to a formal theorem or hidden in a typeclass/axiom. -/
def AnalyticBaseInput : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ratio baseProfile 2 n ≤
      _root_.Real.exp (-(delta - η) * InductionRates.time n ^ 2)

/-- A quadratic base estimate on the actual normalized product. -/
def BaseProductInput (P : ℕ → Profile) : Prop :=
  InductionRates.QuadraticDecay (value (P 2) 2)

/-- The proposed actual adjacent product inequalities, with geometry allowed
to change at each fixed weight. No transfer inequality is asserted. -/
def AdjacentInput (P : ℕ → Profile) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    InductionRates.PowerTransfer (value (P k) k) (value (P (k + 1)) (k + 1))

/-- Two open product inputs plus the specified base profile. -/
def ProductInductionInput : Prop :=
  ∃ P : ℕ → Profile,
    P 2 = baseProfile ∧ BaseProductInput P ∧ AdjacentInput P

/-- The two inputs proposed in the discussion. The conditional transfer from
this proposition still requires AnalyticBaseInput separately. -/
def HeightInductionInput : Prop :=
  ∃ P : ℕ → Profile,
    P 2 = baseProfile ∧ BaseHeightInput ∧ AdjacentInput P

theorem baseProduct_of_height_and_analytic (P : ℕ → Profile)
    (hprofile : P 2 = baseProfile) (hheight : BaseHeightInput)
    (hanalytic : AnalyticBaseInput) : BaseProductInput P := by
  obtain ⟨A, _hA, hgap, N, hleading⟩ := hheight
  unfold BaseProductInput
  rw [hprofile]
  change InductionRates.QuadraticDecay
    (fun n => leading baseProfile 2 n * ratio baseProfile 2 n)
  exact InductionRates.product_quadraticDecay
    (fun n => leading_nonneg baseProfile 2 n) hgap ⟨N, hleading⟩ hanalytic

theorem quadraticDecay_all_of_base_and_adjacent (P : ℕ → Profile)
    (hbase : BaseProductInput P) (hstep : AdjacentInput P) :
    ∀ k : ℕ, 2 ≤ k → InductionRates.QuadraticDecay (value (P k) k) := by
  apply InductionRates.fromTwo_of_adjacent (fun k n => value (P k) k n)
  · intro k n hk
    exact (value_pos (P k) k (by omega) n).le
  · exact hbase
  · exact hstep

theorem all_odd_ge_five_of_base_and_adjacent (P : ℕ → Profile)
    (hbase : BaseProductInput P) (hstep : AdjacentInput P) :
    ∀ k : ℕ, 2 ≤ k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  exact irrational_of_quadraticDecay (P k) k (by omega)
    (quadraticDecay_all_of_base_and_adjacent P hbase hstep k hk)

theorem all_odd_ge_five_of_productInduction (h : ProductInductionInput) :
    ∀ k : ℕ, 2 ≤ k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  obtain ⟨P, _hprofile, hbase, hstep⟩ := h
  exact all_odd_ge_five_of_base_and_adjacent P hbase hstep

/-- Full product-input endpoint. Apéry is separate, and no analytic-base
estimate is a premise of this endpoint. -/
theorem all_odd_irrational_of_productInduction
    (h : ProductInductionInput)
    (hapery : Irrational (riemannZeta (3 : ℂ)).re) :
    ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  by_cases hone : k = 1
  · subst k
    simpa using hapery
  · exact all_odd_ge_five_of_productInduction h k (by omega)

theorem productInduction_of_heightInduction
    (h : HeightInductionInput) (hanalytic : AnalyticBaseInput) :
    ProductInductionInput := by
  obtain ⟨P, hprofile, hheight, hstep⟩ := h
  exact ⟨P, hprofile, baseProduct_of_height_and_analytic P hprofile hheight hanalytic,
    hstep⟩

theorem all_odd_ge_five_of_heightInduction
    (h : HeightInductionInput) (hanalytic : AnalyticBaseInput) :
    ∀ k : ℕ, 2 ≤ k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re :=
  all_odd_ge_five_of_productInduction (productInduction_of_heightInduction h hanalytic)

/-- Height-input endpoint with every unformalized estimate visible in its
type. This proves neither the height input nor the analytic base input. -/
theorem all_odd_irrational_of_heightInduction
    (h : HeightInductionInput) (hanalytic : AnalyticBaseInput)
    (hapery : Irrational (riemannZeta (3 : ℂ)).re) :
    ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re :=
  all_odd_irrational_of_productInduction
    (productInduction_of_heightInduction h hanalytic) hapery

end ZHPreprint.ProfileInduction

#print axioms ZHPreprint.ProfileInduction.primitive_eval_eq_value
#print axioms ZHPreprint.ProfileInduction.normalizedDecay_of_quadraticDecay
#print axioms ZHPreprint.ProfileInduction.irrational_of_quadraticDecay
#print axioms ZHPreprint.ProfileInduction.baseProduct_of_height_and_analytic
#print axioms ZHPreprint.ProfileInduction.quadraticDecay_all_of_base_and_adjacent
#print axioms ZHPreprint.ProfileInduction.all_odd_irrational_of_productInduction
#print axioms ZHPreprint.ProfileInduction.productInduction_of_heightInduction
#print axioms ZHPreprint.ProfileInduction.all_odd_irrational_of_heightInduction
