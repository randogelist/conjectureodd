import Mathlib

/-!
# Conversion of the explicit finite raw-Gram bound to a subquadratic rate

This module proves only the asymptotic conversion and finite-weight propagation.
The explicit finite bound remains a theorem premise. Its proof for the actual
integral ensemble is a separate new formalization obligation, not a ZH axiom.

Prepared against Mathlib commit db584cd6d46c92f209a44c0f1c829460d327499d.
No native compiler execution or axiom-audit PASS is asserted by this source.
-/

noncomputable section
open Filter
open scoped Topology

namespace ZHPreprint.RawGramRate

/-- The preprint's proved-on-paper finite upper bound at N=3t, K=30t, m=3. -/
def rawGramBound (k t : ℕ) : ℝ :=
  (Nat.factorial (2 * k) : ℝ) ^ (27 * t) *
    (90 * (t : ℝ) + 2 * (k : ℝ) + 3) ^ (54 * t)

theorem rawGramBound_pos (k t : ℕ) : 0 < rawGramBound k t := by
  have hfac : (0 : ℝ) < Nat.factorial (2 * k) := by
    exact_mod_cast Nat.factorial_pos (2 * k)
  unfold rawGramBound
  positivity

theorem rawGramBound_log (k t : ℕ) :
    Real.log (rawGramBound k t) =
      27 * (t : ℝ) * Real.log (Nat.factorial (2 * k) : ℝ) +
      54 * (t : ℝ) * Real.log (90 * (t : ℝ) + 2 * (k : ℝ) + 3) := by
  have hfac : (0 : ℝ) < Nat.factorial (2 * k) := by
    exact_mod_cast Nat.factorial_pos (2 * k)
  have hbase : 0 < 90 * (t : ℝ) + 2 * (k : ℝ) + 3 := by positivity
  unfold rawGramBound
  rw [Real.log_mul (pow_ne_zero _ hfac.ne') (pow_ne_zero _ hbase.ne'),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- Any positive quadratic exponential eventually absorbs the explicit
factorial-times-linear-power bound, for every fixed weight. -/
theorem rawGramBound_eventually_le_exp (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      rawGramBound k t ≤ Real.exp (ε * (t : ℝ) ^ 2) := by
  let D : ℝ := 93 + 2 * (k : ℝ)
  let C : ℝ := 27 * Real.log (Nat.factorial (2 * k) : ℝ) + 54 * Real.log D
  have hD : 0 < D := by dsimp [D]; positivity
  have hcast : Tendsto (fun t : ℕ => (t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsmallR : ∀ᶠ x : ℝ in atTop,
      |Real.log x| ≤ (ε / 108) * |x| := by
    simpa only [Real.norm_eq_abs, id_eq] using
      Real.isLittleO_log_id_atTop.bound (show 0 < ε / 108 by positivity)
  have hsmall : ∀ᶠ t : ℕ in atTop,
      |Real.log (t : ℝ)| ≤ (ε / 108) * (t : ℝ) := by
    filter_upwards [hcast.eventually hsmallR] with t ht
    have htR : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    simpa only [abs_of_nonneg htR] using ht
  have hlarge : ∀ᶠ t : ℕ in atTop, C / (ε / 2) ≤ (t : ℝ) :=
    hcast.eventually_ge_atTop (C / (ε / 2))
  have hev : ∀ᶠ t : ℕ in atTop,
      rawGramBound k t ≤ Real.exp (ε * (t : ℝ) ^ 2) := by
    filter_upwards [hsmall, hlarge, eventually_ge_atTop (1 : ℕ)] with t htlog htC ht1
    have ht1R : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1R
    have hlinear : 90 * (t : ℝ) + 2 * (k : ℝ) + 3 ≤ D * (t : ℝ) := by
      have hm := mul_nonneg (show (0 : ℝ) ≤ 2 * (k : ℝ) + 3 by positivity)
        (sub_nonneg.mpr ht1R)
      dsimp [D]
      nlinarith
    have hlogbase : Real.log (90 * (t : ℝ) + 2 * (k : ℝ) + 3) ≤
        Real.log D + Real.log (t : ℝ) := by
      calc
        Real.log (90 * (t : ℝ) + 2 * (k : ℝ) + 3) ≤
            Real.log (D * (t : ℝ)) := Real.log_le_log (by positivity) hlinear
        _ = Real.log D + Real.log (t : ℝ) := Real.log_mul hD.ne' htpos.ne'
    have hlog : Real.log (t : ℝ) ≤ (ε / 108) * (t : ℝ) :=
      (le_abs_self _).trans htlog
    have hC : C ≤ (ε / 2) * (t : ℝ) := by
      have h := (div_le_iff₀ (show 0 < ε / 2 by positivity)).mp htC
      simpa only [mul_comm] using h
    have hlogB : Real.log (rawGramBound k t) ≤
        (t : ℝ) * C + 54 * (t : ℝ) * Real.log (t : ℝ) := by
      rw [rawGramBound_log]
      have hm := mul_le_mul_of_nonneg_left hlogbase
        (show (0 : ℝ) ≤ 54 * (t : ℝ) by positivity)
      dsimp [C]
      nlinarith
    have hconst := mul_le_mul_of_nonneg_left hC htpos.le
    have hlogmul := mul_le_mul_of_nonneg_left hlog
      (show (0 : ℝ) ≤ 54 * (t : ℝ) by positivity)
    apply (Real.log_le_iff_le_exp (rawGramBound_pos k t)).mp
    nlinarith
  exact Filter.eventually_atTop.1 hev

/-- The explicit finite lower factor from the preprint. -/
def rawGramLowerBound (k t : ℕ) : ℝ :=
  ((Nat.factorial (2 * k + 2) : ℝ) ^ (27 * t))⁻¹

/-- The linear logarithmic loss in the finite lower bound is also
subquadratic, for every fixed weight. -/
theorem exp_neg_eventually_le_rawGramLowerBound
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
      Real.exp (-ε * (t : ℝ) ^ 2) ≤ rawGramLowerBound k t := by
  let C : ℝ := 27 * Real.log (Nat.factorial (2 * k + 2) : ℝ)
  have hcast : Tendsto (fun t : ℕ => (t : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ t : ℕ in atTop, C / ε ≤ (t : ℝ) :=
    hcast.eventually_ge_atTop (C / ε)
  have hev : ∀ᶠ t : ℕ in atTop,
      Real.exp (-ε * (t : ℝ) ^ 2) ≤ rawGramLowerBound k t := by
    filter_upwards [hlarge] with t ht
    have htR : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    have hC : C ≤ (t : ℝ) * ε := (div_le_iff₀ hε).mp ht
    have hm := mul_le_mul_of_nonneg_left hC htR
    have hfac : (0 : ℝ) < Nat.factorial (2 * k + 2) := by
      exact_mod_cast Nat.factorial_pos (2 * k + 2)
    have hlogpow :
        Real.log ((Nat.factorial (2 * k + 2) : ℝ) ^ (27 * t)) =
          27 * (t : ℝ) * Real.log (Nat.factorial (2 * k + 2) : ℝ) := by
      rw [Real.log_pow]
      push_cast
      ring
    calc
      Real.exp (-ε * (t : ℝ) ^ 2) ≤
          Real.exp (-(27 * (t : ℝ) * Real.log (Nat.factorial (2 * k + 2) : ℝ))) := by
        apply Real.exp_le_exp.mpr
        dsimp [C] at hm
        nlinarith
      _ = rawGramLowerBound k t := by
        rw [← hlogpow, Real.exp_neg, Real.exp_log (pow_pos hfac _)]
        rfl
  exact Filter.eventually_atTop.1 hev

/-- A subquadratic upper comparison between any two nonnegative sequences. -/
def SubquadraticUpper (f g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ t : ℕ, N ≤ t →
    f t ≤ Real.exp (ε * (t : ℝ) ^ 2) * g t

/-- This is an intermediate implication. The finite integral bound must be
proved independently for the intended actual Gram sequence. -/
theorem eventual_cross_weight_of_finite_bound
    (k : ℕ) (f g : ℕ → ℝ)
    (hg : ∀ t : ℕ, 1 ≤ t → 0 ≤ g t)
    (hfinite : ∀ t : ℕ, 1 ≤ t → f t ≤ rawGramBound k t * g t) :
    SubquadraticUpper f g := by
  intro ε hε
  obtain ⟨N, hN⟩ := rawGramBound_eventually_le_exp k ε hε
  refine ⟨max N 1, ?_⟩
  intro t ht
  have htN : N ≤ t := (le_max_left N 1).trans ht
  have ht1 : 1 ≤ t := (le_max_right N 1).trans ht
  exact (hfinite t ht1).trans
    (mul_le_mul_of_nonneg_right (hN t htN) (hg t ht1))

/-- Finite propagation of arbitrary-small quadratic loss. No cutoff uniform
in the weight is asserted or required. -/
theorem fromTwo_of_adjacent (G : ℕ → ℕ → ℝ)
    (hG : ∀ k t : ℕ, 1 ≤ t → 0 ≤ G k t)
    (hstep : ∀ k : ℕ, 2 ≤ k → SubquadraticUpper (G (k + 1)) (G k)) :
    ∀ k : ℕ, 2 ≤ k → SubquadraticUpper (G k) (G 2) := by
  have hind : ∀ d : ℕ, SubquadraticUpper (G (2 + d)) (G 2) := by
    intro d
    induction d with
    | zero =>
      intro ε hε
      refine ⟨1, ?_⟩
      intro t ht
      have he : 1 ≤ Real.exp (ε * (t : ℝ) ^ 2) :=
        Real.one_le_exp_iff.mpr (by positivity)
      have hm := mul_le_mul_of_nonneg_right he (hG 2 t ht)
      simpa using hm
    | succ d ih =>
      intro ε hε
      have hh : 0 < ε / 2 := by positivity
      obtain ⟨N₁, hN₁⟩ := hstep (2 + d) (by omega) (ε / 2) hh
      obtain ⟨N₂, hN₂⟩ := ih (ε / 2) hh
      refine ⟨max N₁ N₂, ?_⟩
      intro t ht
      have ht₁ : N₁ ≤ t := (le_max_left N₁ N₂).trans ht
      have ht₂ : N₂ ≤ t := (le_max_right N₁ N₂).trans ht
      have hfirst : G (2 + Nat.succ d) t ≤
          Real.exp ((ε / 2) * (t : ℝ) ^ 2) * G (2 + d) t := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hN₁ t ht₁
      calc
        G (2 + Nat.succ d) t ≤
            Real.exp ((ε / 2) * (t : ℝ) ^ 2) * G (2 + d) t := hfirst
        _ ≤ Real.exp ((ε / 2) * (t : ℝ) ^ 2) *
            (Real.exp ((ε / 2) * (t : ℝ) ^ 2) * G 2 t) :=
          mul_le_mul_of_nonneg_left (hN₂ t ht₂) (Real.exp_pos _).le
        _ = Real.exp (ε * (t : ℝ) ^ 2) * G 2 t := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring
  intro k hk
  have heq : 2 + (k - 2) = k := by omega
  simpa only [heq] using hind (k - 2)

/-- Full abstract bridge from the preprint's explicit adjacent finite bounds
to the direct comparison with weight five. -/
theorem fromTwo_of_finite_bounds (G : ℕ → ℕ → ℝ)
    (hG : ∀ k t : ℕ, 1 ≤ t → 0 ≤ G k t)
    (hfinite : ∀ k t : ℕ, 2 ≤ k → 1 ≤ t →
      G (k + 1) t ≤ rawGramBound k t * G k t) :
    ∀ k : ℕ, 2 ≤ k → SubquadraticUpper (G k) (G 2) := by
  apply fromTwo_of_adjacent G hG
  intro k hk
  exact eventual_cross_weight_of_finite_bound k (G (k + 1)) (G k)
    (hG k) (fun t ht => hfinite k t hk ht)

/-- The same rate convention with `t=n+1`, matching the actual affine family. -/
def SubquadraticUpperSucc (f g : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    f n ≤ Real.exp (ε * ((n + 1 : ℕ) : ℝ) ^ 2) * g n

/-- Shifted-index conversion. There is no finite-bound obligation at t=0. -/
theorem eventual_cross_weight_succ_of_finite_bound
    (k : ℕ) (f g : ℕ → ℝ)
    (hg : ∀ n : ℕ, 0 ≤ g n)
    (hfinite : ∀ n : ℕ, f n ≤ rawGramBound k (n + 1) * g n) :
    SubquadraticUpperSucc f g := by
  intro ε hε
  obtain ⟨N, hN⟩ := rawGramBound_eventually_le_exp k ε hε
  refine ⟨N, ?_⟩
  intro n hn
  exact (hfinite n).trans
    (mul_le_mul_of_nonneg_right (hN (n + 1) (by omega)) (hg n))

/-- Finite propagation on the shifted affine-family index. -/
theorem fromTwo_succ_of_adjacent (G : ℕ → ℕ → ℝ)
    (hG : ∀ k n : ℕ, 0 < k → 0 ≤ G k n)
    (hstep : ∀ k : ℕ, 2 ≤ k → SubquadraticUpperSucc (G (k + 1)) (G k)) :
    ∀ k : ℕ, 2 ≤ k → SubquadraticUpperSucc (G k) (G 2) := by
  have hind : ∀ d : ℕ, SubquadraticUpperSucc (G (2 + d)) (G 2) := by
    intro d
    induction d with
    | zero =>
      intro ε hε
      refine ⟨0, ?_⟩
      intro n hn
      have he : 1 ≤ Real.exp (ε * ((n + 1 : ℕ) : ℝ) ^ 2) :=
        Real.one_le_exp_iff.mpr (by positivity)
      have hm := mul_le_mul_of_nonneg_right he (hG 2 n (by omega))
      simpa using hm
    | succ d ih =>
      intro ε hε
      have hh : 0 < ε / 2 := by positivity
      obtain ⟨N₁, hN₁⟩ := hstep (2 + d) (by omega) (ε / 2) hh
      obtain ⟨N₂, hN₂⟩ := ih (ε / 2) hh
      refine ⟨max N₁ N₂, ?_⟩
      intro n hn
      have hn₁ : N₁ ≤ n := (le_max_left N₁ N₂).trans hn
      have hn₂ : N₂ ≤ n := (le_max_right N₁ N₂).trans hn
      have hfirst : G (2 + Nat.succ d) n ≤
          Real.exp ((ε / 2) * ((n + 1 : ℕ) : ℝ) ^ 2) * G (2 + d) n := by
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hN₁ n hn₁
      calc
        G (2 + Nat.succ d) n ≤
            Real.exp ((ε / 2) * ((n + 1 : ℕ) : ℝ) ^ 2) * G (2 + d) n := hfirst
        _ ≤ Real.exp ((ε / 2) * ((n + 1 : ℕ) : ℝ) ^ 2) *
            (Real.exp ((ε / 2) * ((n + 1 : ℕ) : ℝ) ^ 2) * G 2 n) :=
          mul_le_mul_of_nonneg_left (hN₂ n hn₂) (Real.exp_pos _).le
        _ = Real.exp (ε * ((n + 1 : ℕ) : ℝ) ^ 2) * G 2 n := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring
  intro k hk
  have heq : 2 + (k - 2) = k := by omega
  simpa only [heq] using hind (k - 2)

/-- Direct affine-family bridge from the exact finite bound to the comparison
with weight five. All finite inequalities are explicit theorem parameters. -/
theorem fromTwo_succ_of_finite_bounds (G : ℕ → ℕ → ℝ)
    (hG : ∀ k n : ℕ, 0 < k → 0 ≤ G k n)
    (hfinite : ∀ k n : ℕ, 0 < k →
      G (k + 1) n ≤ rawGramBound k (n + 1) * G k n) :
    ∀ k : ℕ, 2 ≤ k → SubquadraticUpperSucc (G k) (G 2) := by
  apply fromTwo_succ_of_adjacent G hG
  intro k hk
  exact eventual_cross_weight_succ_of_finite_bound k (G (k + 1)) (G k)
    (fun n => hG k n (by omega)) (fun n => hfinite k n (by omega))

end ZHPreprint.RawGramRate

#print axioms ZHPreprint.RawGramRate.rawGramBound_eventually_le_exp
#print axioms ZHPreprint.RawGramRate.exp_neg_eventually_le_rawGramLowerBound
#print axioms ZHPreprint.RawGramRate.eventual_cross_weight_of_finite_bound
#print axioms ZHPreprint.RawGramRate.fromTwo_of_adjacent
#print axioms ZHPreprint.RawGramRate.fromTwo_of_finite_bounds
#print axioms ZHPreprint.RawGramRate.eventual_cross_weight_succ_of_finite_bound
#print axioms ZHPreprint.RawGramRate.fromTwo_succ_of_adjacent
#print axioms ZHPreprint.RawGramRate.fromTwo_succ_of_finite_bounds
