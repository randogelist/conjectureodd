import ZHPreprint.InductionRates

/-!
# Quantitative decay along one shared sampling sequence

The real sequence τ records the sampled paper times. The independent index
j is represented by time j = j+1, so the initial bound has exponent
-(j+1)*τ j. A rate envelope retains a positive coefficient of this index
under positive-power transfers with loss linear in the sampled time.

Only implications between explicit estimates are proved. No actual ZH
sample sequence or estimate is constructed here. Native Windows compilation
and the independent axiom audit remain pending; no Lean process was run on
the authoring host.
-/

noncomputable section

namespace ZHPreprint.SequenceRates

open InductionRates

/-- Eventual decay whose exponent per sampled time tends to minus infinity.
The positive rate and finite offset may depend on the fixed weight. -/
def RateEnvelope (τ f : ℕ → ℝ) : Prop :=
  ∃ Θ : ℝ, 0 < Θ ∧ ∃ D : ℝ, 0 ≤ D ∧ ∃ N : ℕ,
    ∀ j : ℕ, N ≤ j →
      f j ≤ Real.exp ((D - Θ * time j) * τ j)

/-- A comparison evaluated only at the common sampling indices. -/
def SamplePowerTransfer (τ f g : ℕ → ℝ) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ j : ℕ, N ≤ j →
      g j ≤ Real.exp (C * τ j) * (f j) ^ θ

/-- The proposed shared-sequence base supplies rate one and offset zero. -/
theorem rateEnvelope_of_base {τ f : ℕ → ℝ}
    (hbase : ∀ j : ℕ, f j ≤ Real.exp (-time j * τ j)) :
    RateEnvelope τ f := by
  refine ⟨1, by norm_num, 0, by norm_num, 0, ?_⟩
  intro j _
  simpa only [one_mul, zero_sub] using hbase j

/-- The same samples propagate with rate θ*Θ and offset C+θ*D. -/
theorem rateEnvelope_of_powerTransfer {τ f g : ℕ → ℝ}
    (hf : ∀ j : ℕ, 0 ≤ f j)
    (hdecay : RateEnvelope τ f)
    (htransfer : SamplePowerTransfer τ f g) :
    RateEnvelope τ g := by
  obtain ⟨Θ, hΘ, D, hD, N₁, hN₁⟩ := hdecay
  obtain ⟨θ, hθ, C, hC, N₂, hN₂⟩ := htransfer
  refine ⟨θ * Θ, mul_pos hθ hΘ,
    C + θ * D, add_nonneg hC (mul_nonneg hθ.le hD), max N₁ N₂, ?_⟩
  intro j hj
  have hj₁ : N₁ ≤ j := (le_max_left _ _).trans hj
  have hj₂ : N₂ ≤ j := (le_max_right _ _).trans hj
  have hpower : (f j) ^ θ ≤
      (Real.exp ((D - Θ * time j) * τ j)) ^ θ :=
    Real.rpow_le_rpow (hf j) (hN₁ j hj₁) hθ.le
  calc
    g j ≤ Real.exp (C * τ j) * (f j) ^ θ := hN₂ j hj₂
    _ ≤ Real.exp (C * τ j) *
        (Real.exp ((D - Θ * time j) * τ j)) ^ θ :=
      mul_le_mul_of_nonneg_left hpower (Real.exp_pos _).le
    _ = Real.exp (C * τ j + ((D - Θ * time j) * τ j) * θ) := by
      rw [← Real.exp_mul, ← Real.exp_add]
    _ = Real.exp ((C + θ * D - (θ * Θ) * time j) * τ j) := by
      congr 1
      ring

/-- Induction keeps one common sampling sequence across all fixed weights. -/
theorem fromTwo_of_adjacent (τ : ℕ → ℝ) (E : ℕ → ℕ → ℝ)
    (hE : ∀ k j : ℕ, 2 ≤ k → 0 ≤ E k j)
    (hbase : RateEnvelope τ (E 2))
    (hstep : ∀ k : ℕ, 2 ≤ k → SamplePowerTransfer τ (E k) (E (k + 1))) :
    ∀ k : ℕ, 2 ≤ k → RateEnvelope τ (E k) := by
  have hind : ∀ d : ℕ, RateEnvelope τ (E (2 + d)) := by
    intro d
    induction d with
    | zero => simpa using hbase
    | succ d ih =>
      have hkd : 2 ≤ 2 + d := by omega
      have hres := rateEnvelope_of_powerTransfer
        (fun j => hE (2 + d) j hkd) ih (hstep (2 + d) hkd)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hres
  intro k hk
  have heq : 2 + (k - 2) = k := by omega
  simpa only [heq] using hind (k - 2)

/-- At nonnegative sampled times, every fixed exponential rate is eventually
beaten. This statement needs no quadratic decay or rate uniform in weight. -/
theorem eventually_exp_bound {τ f : ℕ → ℝ}
    (hτ : ∀ j : ℕ, 0 ≤ τ j) (h : RateEnvelope τ f) (M : ℝ) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → f j ≤ Real.exp (-M * τ j) := by
  obtain ⟨Θ, hΘ, D, _hD, N₁, hN₁⟩ := h
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge ((D + M) / Θ)
  refine ⟨max N₁ N₂, ?_⟩
  intro j hj
  have hj₁ : N₁ ≤ j := (le_max_left _ _).trans hj
  have hj₂ : N₂ ≤ j := (le_max_right _ _).trans hj
  have hNt : (N₂ : ℝ) ≤ time j := by
    unfold time
    exact_mod_cast (le_trans hj₂ (Nat.le_succ j))
  have hlarge : (D + M) / Θ ≤ time j := hN₂.trans hNt
  have hDM : D + M ≤ time j * Θ := (div_le_iff₀ hΘ).mp hlarge
  have hcoeff : D - Θ * time j ≤ -M := by nlinarith
  exact (hN₁ j hj₁).trans (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hcoeff (hτ j)))

/-- The explicit logarithmic invariant discussed in the shared-sequence
reduction. Positivity justifies both the logarithm estimate and division. -/
theorem tendsto_neg_log_div_atTop {τ f : ℕ → ℝ}
    (hτ : ∀ j : ℕ, 0 < τ j) (hf : ∀ j : ℕ, 0 < f j)
    (h : RateEnvelope τ f) :
    Filter.Tendsto (fun j => -Real.log (f j) / τ j)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro M
  obtain ⟨N, hN⟩ := eventually_exp_bound (fun j => (hτ j).le) h M
  refine ⟨N, ?_⟩
  intro j hj
  have hlog : Real.log (f j) ≤ -M * τ j :=
    (Real.log_le_iff_le_exp (hf j)).mpr (hN j hj)
  apply (le_div_iff₀ (hτ j)).mpr
  nlinarith

end ZHPreprint.SequenceRates

#print axioms ZHPreprint.SequenceRates.rateEnvelope_of_base
#print axioms ZHPreprint.SequenceRates.rateEnvelope_of_powerTransfer
#print axioms ZHPreprint.SequenceRates.fromTwo_of_adjacent
#print axioms ZHPreprint.SequenceRates.eventually_exp_bound
#print axioms ZHPreprint.SequenceRates.tendsto_neg_log_div_atTop
