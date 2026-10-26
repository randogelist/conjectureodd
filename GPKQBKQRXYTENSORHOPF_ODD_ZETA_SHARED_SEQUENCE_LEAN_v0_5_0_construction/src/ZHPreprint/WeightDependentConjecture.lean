import Theorem_4_1_Leading_Coefficient_Gap

/-!
# Weight-dependent ZH profiles and the proposed arithmetic/analytic gap

The positive integer t in the paper is n+1 here. Each fixed odd weight may
choose its own positive m,a,b with a<b; its actual ZH parameters are
  (k,m,N,K) = (k,m,a*(n+1),b*(n+1)).

WEIGHT_DEPENDENT_GAP_CONJECTURE is a proposition defining the new open
conjecture. It is not asserted or installed as an axiom. The conditional
transfer below uses the existing concrete ZH determinant and primitive
normalization, not an arbitrary polynomial sequence.

No old fixed-profile growth conjecture, weight-five seed, or finite Gram
comparison premise occurs in the new endpoint. Apéry's theorem is retained
as an explicit input only for the final weight-three case.

Construction source: native Windows compilation and the independent axiom
audit are pending. No local Lean execution is authorized.
-/

noncomputable section

namespace ZHPreprint.WeightDependent

open ManuscriptChain

/-- A fixed profile at one weight, with paper index t=n+1. -/
def profile (k m a b n : ℕ) : Real.Parameters :=
  ⟨k, m, a * (n + 1), b * (n + 1)⟩

/-- The positive real paper index. -/
def time (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

theorem profile_admissible (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    Real.Admissible (profile k m a b n) := by
  constructor
  · exact hk
  · exact hm
  · exact Nat.mul_pos ha (Nat.succ_pos n)
  · exact Nat.mul_lt_mul_of_pos_right hab (Nat.succ_pos n)

@[simp] theorem profile_k (k m a b n : ℕ) :
    (profile k m a b n).k = k := rfl

/-- The primitive polynomial still has degree linear in the paper index. -/
theorem profile_primitive_degree (k m a b n : ℕ) :
    (GeneralIrrationality.primitivePolynomial (profile k m a b n)).natDegree =
      (b - a) * (n + 1) := by
  rw [GeneralIrrationality.primitivePolynomial_natDegree]
  change b * (n + 1) - a * (n + 1) = (b - a) * (n + 1)
  exact (Nat.sub_mul b a (n + 1)).symm

theorem profile_unbounded (k m a b : ℕ) (hb : 0 < b) :
    GeneralIrrationality.UnboundedOnTails (profile k m a b) := by
  intro n₀ D
  refine ⟨n₀ + D, by omega, ?_⟩
  have hmul := Nat.mul_le_mul_right (n₀ + D + 1) (show 1 ≤ b by omega)
  simp only [one_mul] at hmul
  change D ≤ b * (n₀ + D + 1)
  omega

/-- Positivity of the determinant ratio is proved from the actual profile. -/
theorem profile_ratio_pos (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    0 < LeadingCoefficientGap.determinantRatio (profile k m a b n) :=
  LeadingCoefficientGap.determinantRatio_pos _
    (profile_admissible k m a b hk hm ha hab n)

/-- Separate eventual t^2 bounds on the actual leading coefficient and
Gram/slope determinant ratio, with a strictly positive rate gap. -/
def ProfileGap (k m a b : ℕ) : Prop :=
  ∃ A B : ℝ, 0 ≤ A ∧ A < B ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    LeadingCoefficientGap.leadingSize (profile k m a b n) ≤
        _root_.Real.exp (A * time n ^ 2) ∧
    LeadingCoefficientGap.determinantRatio (profile k m a b n) ≤
        _root_.Real.exp (-B * time n ^ 2)

/-- NEW OPEN CONJECTURE. Geometry and rates may depend on the fixed weight.
No witness profile, growth estimate, or decay estimate is supplied here. -/
def WEIGHT_DEPENDENT_GAP_CONJECTURE : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ m a b : ℕ, 0 < m ∧ 0 < a ∧ a < b ∧ ProfileGap k m a b

/-- Exact conversion of a paper t^2 rate to the upstream K^2 convention. -/
theorem rate_rescale (k m a b n : ℕ) (hb : 0 < b) (C : ℝ) :
    (C / (b : ℝ) ^ 2) * ((profile k m a b n).K : ℝ) ^ 2 =
      C * time n ^ 2 := by
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  change (C / (b : ℝ) ^ 2) * ((b * (n + 1) : ℕ) : ℝ) ^ 2 =
    C * ((n + 1 : ℕ) : ℝ) ^ 2
  rw [Nat.cast_mul, mul_pow, ← mul_assoc,
    div_mul_cancel₀ _ (pow_ne_zero _ hbR)]

/-- A profile satisfying the new gap proves irrationality at that weight.
All positivity, degree, and unboundedness obligations are discharged here. -/
theorem irrational_riemannZeta_of_profileGap (k m a b : ℕ)
    (hk : 0 < k) (hm : 0 < m) (ha : 0 < a) (hab : a < b)
    (hgap : ProfileGap k m a b) :
    Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  obtain ⟨A, B, _hA, hAB, N, hbounds⟩ := hgap
  have hb : 0 < b := lt_trans ha hab
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hbsq : 0 < (b : ℝ) ^ 2 := by positivity
  have hscaled : A / (b : ℝ) ^ 2 < B / (b : ℝ) ^ 2 := by
    apply (div_lt_iff₀ hbsq).2
    simpa only [div_mul_cancel₀ _ (ne_of_gt hbsq)] using hAB
  apply LeadingCoefficientGap.irrational_riemannZeta_of_gap k hk
    (profile k m a b)
    (profile_admissible k m a b hk hm ha hab)
    (profile_k k m a b)
    (profile_unbounded k m a b hb)
    (A / (b : ℝ) ^ 2) (B / (b : ℝ) ^ 2) hscaled N
  · intro n hn
    rw [rate_rescale k m a b n hb A]
    exact (hbounds n hn).1
  · intro n hn
    have hnegative :
        -(B / (b : ℝ) ^ 2) * ((profile k m a b n).K : ℝ) ^ 2 =
          -B * time n ^ 2 := by
      simpa only [neg_div] using rate_rescale k m a b n hb (-B)
    rw [hnegative]
    exact (hbounds n hn).2

/-- The conjecture supplies each weight >=5; it is the sole open premise. -/
theorem all_odd_ge_five_of_weightDependentGap
    (h : WEIGHT_DEPENDENT_GAP_CONJECTURE) :
    ∀ k : ℕ, 2 ≤ k →
      Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  obtain ⟨m, a, b, hm, ha, hab, hgap⟩ := h k hk
  exact irrational_riemannZeta_of_profileGap k m a b (by omega) hm ha hab hgap

/-- Final endpoint: the new conjecture plus the separate weight-three input.
This theorem does not assert the conjecture or construct a successful profile. -/
theorem all_odd_irrational_of_weightDependentGap
    (h : WEIGHT_DEPENDENT_GAP_CONJECTURE)
    (hapery : Irrational (riemannZeta (3 : ℂ)).re) :
    ∀ k : ℕ, 0 < k →
      Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  by_cases hone : k = 1
  · subst k
    simpa using hapery
  · exact all_odd_ge_five_of_weightDependentGap h k (by omega)

end ZHPreprint.WeightDependent

#print axioms ZHPreprint.WeightDependent.profile_admissible
#print axioms ZHPreprint.WeightDependent.profile_primitive_degree
#print axioms ZHPreprint.WeightDependent.profile_unbounded
#print axioms ZHPreprint.WeightDependent.profile_ratio_pos
#print axioms ZHPreprint.WeightDependent.rate_rescale
#print axioms ZHPreprint.WeightDependent.irrational_riemannZeta_of_profileGap
#print axioms ZHPreprint.WeightDependent.all_odd_ge_five_of_weightDependentGap
#print axioms ZHPreprint.WeightDependent.all_odd_irrational_of_weightDependentGap
