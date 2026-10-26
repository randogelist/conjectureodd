import ZHPreprint.DerivationRouter
import ZHPreprint.SequenceRates

/-!
# Conditional induction along one shared sequence of actual ZH samples

The sampling map sigma uses the existing natural parameter n; its paper
sample is t_j = sigma j + 1. The paper witness label is j+1. Every weight
uses this same map. Profiles may change with weight, and all product
comparisons are explicit inputs on their actual primitive normalizations.

The input supplies a base bound at the sampled indices and eventual
adjacent comparisons along those indices. No quadratic estimate or separate
height/analytic base estimate is assumed. No successful sequence, base
estimate, or adjacent comparison is constructed here.

Construction source: native Windows compilation and audit are pending.
No Lean, Lake, or leanchecker process was run on the authoring host.
-/

noncomputable section

namespace ZHPreprint.SharedSequence

open ManuscriptChain

/-- The positive paper parameter at a sampled index. -/
def sampledTime (sigma : ℕ → ℕ) (j : ℕ) : ℝ :=
  InductionRates.time (sigma j)

/-- The actual primitive polynomial value at the sampled index. -/
def sampledValue (p : ProfileInduction.Profile) (k : ℕ)
    (sigma : ℕ → ℕ) (j : ℕ) : ℝ :=
  ProfileInduction.value p k (sigma j)

theorem sampledTime_pos (sigma : ℕ → ℕ) (j : ℕ) :
    0 < sampledTime sigma j :=
  InductionRates.time_pos (sigma j)

theorem sampledValue_pos (p : ProfileInduction.Profile) (k : ℕ)
    (hk : 0 < k) (sigma : ℕ → ℕ) (j : ℕ) :
    0 < sampledValue p k sigma j :=
  ProfileInduction.value_pos p k hk (sigma j)

/-- The normalization remains exactly the existing primitive polynomial. -/
theorem sampled_eval_eq_value (p : ProfileInduction.Profile) (k : ℕ)
    (sigma : ℕ → ℕ) (j : ℕ) :
    RealTransfer.evalReal
        (GeneralIrrationality.primitivePolynomial (p.atWeight k (sigma j)))
        (Real.zeta (2 * k + 1)) = sampledValue p k sigma j := by
  simpa only [Real.Parameters.weight, ProfileInduction.Profile.atWeight_k,
    sampledValue] using ProfileInduction.primitive_eval_eq_value p k (sigma j)

/-- The open base bound: the paper label is j+1, not the sampling parameter. -/
def BaseInput (P : ℕ → ProfileInduction.Profile) (sigma : ℕ → ℕ) : Prop :=
  ∀ j : ℕ, sampledValue (P 2) 2 sigma j ≤
    _root_.Real.exp (-InductionRates.time j * sampledTime sigma j)

/-- Each weight step compares the actual products on the same sampled indices. -/
def AdjacentInput (P : ℕ → ProfileInduction.Profile) (sigma : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    SequenceRates.SamplePowerTransfer (sampledTime sigma)
      (sampledValue (P k) k sigma)
      (sampledValue (P (k + 1)) (k + 1) sigma)

/-- The exact shared-sequence proposal. Admissibility is part of Profile.
Strict monotonicity records the requested increasing positive paper samples.
This proposition is an input, not a theorem asserting its existence. -/
def SharedSequenceInput : Prop :=
  ∃ P : ℕ → ProfileInduction.Profile, ∃ sigma : ℕ → ℕ,
    P 2 = ProfileInduction.baseProfile ∧ StrictMono sigma ∧
    BaseInput P sigma ∧ AdjacentInput P sigma

/-- The one-unit exponential margin defeats a denominator of any size. -/
private theorem linear_denominator_squeeze {b d t : ℕ}
    (hb : 0 < b) (ht : 0 < t) :
    (b : ℝ) ^ (d * t) *
      _root_.Real.exp (-((d : ℝ) * _root_.Real.log (b : ℝ) + 1) * (t : ℝ)) < 1 := by
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hpow : (b : ℝ) ^ (d * t) =
      _root_.Real.exp (((d * t : ℕ) : ℝ) * _root_.Real.log (b : ℝ)) := by
    rw [_root_.Real.exp_nat_mul, _root_.Real.exp_log hbR]
  calc
    (b : ℝ) ^ (d * t) *
        _root_.Real.exp (-((d : ℝ) * _root_.Real.log (b : ℝ) + 1) * (t : ℝ)) =
        _root_.Real.exp (((d * t : ℕ) : ℝ) * _root_.Real.log (b : ℝ) +
          -((d : ℝ) * _root_.Real.log (b : ℝ) + 1) * (t : ℝ)) := by
      rw [hpow, _root_.Real.exp_add]
    _ = _root_.Real.exp (-(t : ℝ)) := by
      congr 1
      push_cast
      ring
    _ < 1 := _root_.Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr htR)

/-- A sampled rate envelope supplies the actual denominator criterion.
No all-parameter quadratic estimate is used or concluded. -/
theorem irrational_of_rateEnvelope (p : ProfileInduction.Profile) (k : ℕ)
    (hk : 0 < k) (sigma : ℕ → ℕ)
    (h : SequenceRates.RateEnvelope (sampledTime sigma) (sampledValue p k sigma)) :
    Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  rw [← Real.zeta_eq_riemannZeta_re (show 1 < 2 * k + 1 by omega)]
  apply RealTransfer.irrational_of_decay_and_denominator_budget
    (Q := fun j => GeneralIrrationality.primitivePolynomial (p.atWeight k (sigma j)))
    (budget := sampledValue p k sigma) (n₀ := 0) (b₀ := 0)
  · constructor
    · intro j _
      rw [sampled_eval_eq_value]
      exact ne_of_gt (sampledValue_pos p k hk sigma j)
    · intro j _
      simpa only [sampled_eval_eq_value, abs_of_pos (sampledValue_pos p k hk sigma j)]
        using (le_rfl : sampledValue p k sigma j ≤ sampledValue p k sigma j)
  · intro b hb _
    obtain ⟨N, hN⟩ := SequenceRates.eventually_exp_bound
      (fun j => (sampledTime_pos sigma j).le) h
      (((p.b - p.a : ℕ) : ℝ) * _root_.Real.log (b : ℝ) + 1)
    refine ⟨N, Nat.zero_le N, ?_⟩
    rw [p.primitive_degree k (sigma N)]
    have hmult := mul_le_mul_of_nonneg_left (hN N le_rfl)
      (show 0 ≤ (b : ℝ) ^ ((p.b - p.a) * (sigma N + 1)) by positivity)
    apply hmult.trans_lt
    simpa only [sampledTime, InductionRates.time] using
      linear_denominator_squeeze (d := p.b - p.a) (t := sigma N + 1)
        hb (Nat.succ_pos (sigma N))

/-- Quantitative induction retains a positive coefficient of the witness label.
All constants and thresholds may depend on the fixed weight. -/
theorem rateEnvelope_all_of_base_and_adjacent
    (P : ℕ → ProfileInduction.Profile) (sigma : ℕ → ℕ)
    (hbase : BaseInput P sigma) (hstep : AdjacentInput P sigma) :
    ∀ k : ℕ, 2 ≤ k → SequenceRates.RateEnvelope (sampledTime sigma)
      (sampledValue (P k) k sigma) := by
  apply SequenceRates.fromTwo_of_adjacent (sampledTime sigma)
    (fun k => sampledValue (P k) k sigma)
  · intro k j hk
    exact (sampledValue_pos (P k) k (by omega) sigma j).le
  · exact SequenceRates.rateEnvelope_of_base hbase
  · exact hstep

/-- The precise logarithmic invariant stated in the shared-sequence proposal. -/
theorem tendsto_neg_log_div_of_rateEnvelope (p : ProfileInduction.Profile) (k : ℕ)
    (hk : 0 < k) (sigma : ℕ → ℕ)
    (h : SequenceRates.RateEnvelope (sampledTime sigma) (sampledValue p k sigma)) :
    Filter.Tendsto
      (fun j => -_root_.Real.log (sampledValue p k sigma j) / sampledTime sigma j)
      Filter.atTop Filter.atTop :=
  SequenceRates.tendsto_neg_log_div_atTop
    (fun j => sampledTime_pos sigma j) (fun j => sampledValue_pos p k hk sigma j) h

/-- The supplied base and steps propagate the exact invariant at each fixed weight. -/
theorem all_logarithmic_rates_of_sharedSequence (h : SharedSequenceInput) :
    ∃ P : ℕ → ProfileInduction.Profile, ∃ sigma : ℕ → ℕ,
      P 2 = ProfileInduction.baseProfile ∧ StrictMono sigma ∧
      ∀ k : ℕ, 2 ≤ k → Filter.Tendsto
        (fun j => -_root_.Real.log (sampledValue (P k) k sigma j) / sampledTime sigma j)
        Filter.atTop Filter.atTop := by
  obtain ⟨P, sigma, hprofile, hmono, hbase, hstep⟩ := h
  refine ⟨P, sigma, hprofile, hmono, ?_⟩
  intro k hk
  exact tendsto_neg_log_div_of_rateEnvelope (P k) k (by omega) sigma
    (rateEnvelope_all_of_base_and_adjacent P sigma hbase hstep k hk)

theorem all_odd_ge_five_of_sharedSequence (h : SharedSequenceInput) :
    ∀ k : ℕ, 2 ≤ k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  obtain ⟨P, sigma, _hprofile, _hmono, hbase, hstep⟩ := h
  intro k hk
  exact irrational_of_rateEnvelope (P k) k (by omega) sigma
    (rateEnvelope_all_of_base_and_adjacent P sigma hbase hstep k hk)

/-- Conditional all-odd endpoint. The separate weight-three theorem remains
an explicit input, and no successful shared sequence is asserted. -/
theorem all_odd_irrational_of_sharedSequence (h : SharedSequenceInput)
    (hapery : Irrational (riemannZeta (3 : ℂ)).re) :
    ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  by_cases hone : k = 1
  · subst k
    simpa using hapery
  · exact all_odd_ge_five_of_sharedSequence h k (by omega)

end ZHPreprint.SharedSequence

#print axioms ZHPreprint.SharedSequence.sampled_eval_eq_value
#print axioms ZHPreprint.SharedSequence.irrational_of_rateEnvelope
#print axioms ZHPreprint.SharedSequence.rateEnvelope_all_of_base_and_adjacent
#print axioms ZHPreprint.SharedSequence.tendsto_neg_log_div_of_rateEnvelope
#print axioms ZHPreprint.SharedSequence.all_logarithmic_rates_of_sharedSequence
#print axioms ZHPreprint.SharedSequence.all_odd_ge_five_of_sharedSequence
#print axioms ZHPreprint.SharedSequence.all_odd_irrational_of_sharedSequence
