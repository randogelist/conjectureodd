import Mathlib

/-!
# Quadratic decay transported by a power and a linear exponential loss

The paper index t >= 1 is represented by n+1.  This module proves only
abstract implications between explicit estimates.  It supplies no estimate
for an actual ZH sequence and installs no unproved statement as an axiom.

Construction source: native Windows compilation and the independent audit
remain pending.  No Lean process was run on the authoring host.
-/

noncomputable section

namespace ZHPreprint.InductionRates

/-- The positive real index corresponding to paper t=n+1. -/
def time (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

theorem time_pos (n : ℕ) : 0 < time n := by
  unfold time
  exact_mod_cast Nat.succ_pos n

theorem time_nonneg (n : ℕ) : 0 ≤ time n := (time_pos n).le

/-- A positive eventual quadratic exponential decay rate. -/
def QuadraticDecay (f : ℕ → ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    f n ≤ Real.exp (-ε * time n ^ 2)

/-- An eventual comparison with a positive real power and linear log-loss. -/
def PowerTransfer (f g : ℕ → ℝ) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n →
      g n ≤ Real.exp (C * time n) * (f n) ^ θ

/-- Linear logarithmic loss preserves positive quadratic decay. -/
theorem quadraticDecay_of_powerTransfer {f g : ℕ → ℝ}
    (hf : ∀ n : ℕ, 0 ≤ f n)
    (hdecay : QuadraticDecay f)
    (htransfer : PowerTransfer f g) :
    QuadraticDecay g := by
  obtain ⟨ε, hε, N₁, hN₁⟩ := hdecay
  obtain ⟨θ, hθ, C, _hC, N₂, hN₂⟩ := htransfer
  have hrate : 0 < θ * ε / 2 := by positivity
  obtain ⟨N₃, hN₃⟩ := exists_nat_ge (C / (θ * ε / 2))
  refine ⟨θ * ε / 2, hrate, max N₁ (max N₂ N₃), ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂₃ : max N₂ N₃ ≤ n := (le_max_right _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left _ _).trans hn₂₃
  have hn₃ : N₃ ≤ n := (le_max_right _ _).trans hn₂₃
  have hNt : (N₃ : ℝ) ≤ time n := by
    unfold time
    exact_mod_cast (le_trans hn₃ (Nat.le_succ n))
  have hCt : C / (θ * ε / 2) ≤ time n := hN₃.trans hNt
  have hCbound : C ≤ time n * (θ * ε / 2) :=
    (div_le_iff₀ hrate).mp hCt
  have hClinear : C * time n ≤ (θ * ε / 2) * time n ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hCbound (time_nonneg n)
    nlinarith
  have hpower : (f n) ^ θ ≤ (Real.exp (-ε * time n ^ 2)) ^ θ :=
    Real.rpow_le_rpow (hf n) (hN₁ n hn₁) hθ.le
  calc
    g n ≤ Real.exp (C * time n) * (f n) ^ θ := hN₂ n hn₂
    _ ≤ Real.exp (C * time n) * (Real.exp (-ε * time n ^ 2)) ^ θ :=
      mul_le_mul_of_nonneg_left hpower (Real.exp_pos _).le
    _ = Real.exp (C * time n + (-ε * time n ^ 2) * θ) := by
      rw [← Real.exp_mul, ← Real.exp_add]
    _ ≤ Real.exp (-(θ * ε / 2) * time n ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- A base at k=2 and adjacent transfers give quadratic decay at every k>=2.
The sequence and every estimate remain explicit inputs. -/
theorem fromTwo_of_adjacent (E : ℕ → ℕ → ℝ)
    (hE : ∀ k n : ℕ, 2 ≤ k → 0 ≤ E k n)
    (hbase : QuadraticDecay (E 2))
    (hstep : ∀ k : ℕ, 2 ≤ k → PowerTransfer (E k) (E (k + 1))) :
    ∀ k : ℕ, 2 ≤ k → QuadraticDecay (E k) := by
  have hind : ∀ d : ℕ, QuadraticDecay (E (2 + d)) := by
    intro d
    induction d with
    | zero => simpa using hbase
    | succ d ih =>
      have hkd : 2 ≤ 2 + d := by omega
      have hres := quadraticDecay_of_powerTransfer
        (fun n => hE (2 + d) n hkd) ih (hstep (2 + d) hkd)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hres
  intro k hk
  have heq : 2 + (k - 2) = k := by omega
  simpa only [heq] using hind (k - 2)

/-- A height rate below an analytic limiting decay rate gives product decay.
In particular, the analytic estimate is a premise here, not a proved anchor. -/
theorem product_quadraticDecay {L R : ℕ → ℝ} {A δ : ℝ}
    (hLnonneg : ∀ n : ℕ, 0 ≤ L n)
    (hgap : A < δ)
    (hleading : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      L n ≤ Real.exp (A * time n ^ 2))
    (hanalytic : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      R n ≤ Real.exp (-(δ - η) * time n ^ 2)) :
    QuadraticDecay (fun n => L n * R n) := by
  have hη : 0 < (δ - A) / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := hleading
  obtain ⟨N₂, hN₂⟩ := hanalytic ((δ - A) / 2) hη
  refine ⟨(δ - A) / 2, hη, max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  calc
    L n * R n ≤ L n * Real.exp (-(δ - (δ - A) / 2) * time n ^ 2) :=
      mul_le_mul_of_nonneg_left (hN₂ n hn₂) (hLnonneg n)
    _ ≤ Real.exp (A * time n ^ 2) *
        Real.exp (-(δ - (δ - A) / 2) * time n ^ 2) :=
      mul_le_mul_of_nonneg_right (hN₁ n hn₁) (Real.exp_pos _).le
    _ = Real.exp (-((δ - A) / 2) * time n ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

end ZHPreprint.InductionRates

#print axioms ZHPreprint.InductionRates.quadraticDecay_of_powerTransfer
#print axioms ZHPreprint.InductionRates.fromTwo_of_adjacent
#print axioms ZHPreprint.InductionRates.product_quadraticDecay
