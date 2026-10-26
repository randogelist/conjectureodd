import Theorem_4_1_Spectral_Irrationality_Measure_Criterion

/-!
# Direct irrationality from integer-polynomial decay

At a rational target a/b, every nonzero integer-polynomial value has absolute
value at least b^(-degree). Thus a sufficiently small nonzero value contradicts
rationality directly. No root separation or local comparison is needed.
-/

noncomputable section

namespace ManuscriptChain.RealTransfer

/-- Direct denominator squeeze. A uniform spectral estimate is unnecessary
when the desired conclusion is irrationality rather than an irrationality measure. -/
theorem irrational_of_decay_and_denominator_budget
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {budget : ℕ → ℝ} {n₀ b₀ : ℕ}
    (decay : Decay Q ξ budget n₀)
    (squeeze : ∀ b : ℕ, 0 < b → b₀ ≤ b →
      ∃ n : ℕ, n₀ ≤ n ∧ (b : ℝ) ^ (Q n).natDegree * budget n < 1) :
    Irrational ξ := by
  rw [Irrational]
  rintro ⟨r, hr⟩
  let t : ℕ := b₀ + 1
  let b : ℕ := r.den * t
  let a : ℤ := r.num * (t : ℤ)
  have ht : 0 < t := by dsimp [t]; omega
  have hd : 0 < r.den := r.pos
  have hb : 0 < b := Nat.mul_pos hd ht
  have hbb : b₀ ≤ b := by
    dsimp [b, t]
    nlinarith
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  have hdR : (r.den : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hab : (a : ℝ) / (b : ℝ) = ξ := by
    calc
      (a : ℝ) / (b : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
        dsimp [a, b]
        push_cast
        field_simp
      _ = (r : ℝ) := (Rat.cast_def r).symm
      _ = ξ := hr
  obtain ⟨n, hn, hsmall⟩ := squeeze b hb hbb
  apply polynomial_integer_squeeze (Q n) a b hb
  · rw [hab]
    exact decay.nonzero n hn
  · rw [hab]
    exact (mul_le_mul_of_nonneg_left (decay.upper n hn)
      (show 0 ≤ (b : ℝ) ^ (Q n).natDegree by positivity)).trans_lt hsmall

end ManuscriptChain.RealTransfer

#print axioms ManuscriptChain.RealTransfer.irrational_of_decay_and_denominator_budget
