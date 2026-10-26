import ZHPreprint.InductionRates

/-!
# Algebraic routes between explicit decay estimates

These lemmas combine supplied estimates. They neither search for estimates
nor assert their validity on any actual ZH profile. The paper index remains
t=n+1 throughout; no passage to a different sampling subsequence occurs.

Construction source: native Windows compilation and audit are pending.
No Lean, Lake, or leanchecker process was run on the authoring host.
-/

noncomputable section

namespace ZHPreprint.RouterAlgebra

open InductionRates

/-- A strict separated quadratic gap supplies positive product decay. -/
theorem quadraticDecay_of_separatedBounds {L R : ℕ → ℝ} {A B : ℝ}
    (hLnonneg : ∀ n : ℕ, 0 ≤ L n)
    (hAB : A < B)
    (hleading : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      L n ≤ Real.exp (A * time n ^ 2))
    (hratio : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      R n ≤ Real.exp (-B * time n ^ 2)) :
    QuadraticDecay (fun n => L n * R n) := by
  obtain ⟨N₁, hN₁⟩ := hleading
  obtain ⟨N₂, hN₂⟩ := hratio
  refine ⟨B - A, sub_pos.mpr hAB, max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  calc
    L n * R n ≤ L n * Real.exp (-B * time n ^ 2) :=
      mul_le_mul_of_nonneg_left (hN₂ n hn₂) (hLnonneg n)
    _ ≤ Real.exp (A * time n ^ 2) * Real.exp (-B * time n ^ 2) :=
      mul_le_mul_of_nonneg_right (hN₁ n hn₁) (Real.exp_pos _).le
    _ = Real.exp (-(B - A) * time n ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Separate factor transfers must share the same positive real exponent.
The two linear logarithmic losses may differ and are added by the router. -/
def PairedPowerTransfer (L R L' R' : ℕ → ℝ) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ ∃ C_L : ℝ, 0 ≤ C_L ∧ ∃ C_R : ℝ, 0 ≤ C_R ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      L' n ≤ Real.exp (C_L * time n) * (L n) ^ θ ∧
      R' n ≤ Real.exp (C_R * time n) * (R n) ^ θ

/-- Multiply actual factor estimates without discarding either factor. -/
theorem powerTransfer_of_paired {L R L' R' : ℕ → ℝ}
    (hL : ∀ n : ℕ, 0 ≤ L n)
    (hR : ∀ n : ℕ, 0 ≤ R n)
    (_hL' : ∀ n : ℕ, 0 ≤ L' n)
    (hR' : ∀ n : ℕ, 0 ≤ R' n)
    (h : PairedPowerTransfer L R L' R') :
    PowerTransfer (fun n => L n * R n) (fun n => L' n * R' n) := by
  obtain ⟨θ, hθ, C_L, hC_L, C_R, hC_R, N, hN⟩ := h
  refine ⟨θ, hθ, C_L + C_R, add_nonneg hC_L hC_R, N, ?_⟩
  intro n hn
  obtain ⟨hLn, hRn⟩ := hN n hn
  have hupper : 0 ≤ Real.exp (C_L * time n) * (L n) ^ θ :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (hL n) θ)
  have hexp : Real.exp (C_L * time n) * Real.exp (C_R * time n) =
      Real.exp ((C_L + C_R) * time n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow : (L n) ^ θ * (R n) ^ θ = (L n * R n) ^ θ :=
    (Real.mul_rpow (hL n) (hR n)).symm
  calc
    L' n * R' n ≤
        (Real.exp (C_L * time n) * (L n) ^ θ) *
          (Real.exp (C_R * time n) * (R n) ^ θ) :=
      mul_le_mul hLn hRn (hR' n) hupper
    _ = (Real.exp (C_L * time n) * Real.exp (C_R * time n)) *
        ((L n) ^ θ * (R n) ^ θ) := by ring
    _ = Real.exp ((C_L + C_R) * time n) * (L n * R n) ^ θ := by
      rw [hexp, hpow]

/-- Compose two estimate routes, retaining their exact exponent and loss.
The intermediate sequence may correspond to a different weight or geometry. -/
theorem powerTransfer_trans {f g h : ℕ → ℝ}
    (hf : ∀ n : ℕ, 0 ≤ f n)
    (hg : ∀ n : ℕ, 0 ≤ g n)
    (hfg : PowerTransfer f g)
    (hgh : PowerTransfer g h) :
    PowerTransfer f h := by
  obtain ⟨θ₁, hθ₁, C₁, hC₁, N₁, hN₁⟩ := hfg
  obtain ⟨θ₂, hθ₂, C₂, hC₂, N₂, hN₂⟩ := hgh
  refine ⟨θ₁ * θ₂, mul_pos hθ₁ hθ₂,
    C₂ + θ₂ * C₁, add_nonneg hC₂ (mul_nonneg hθ₂.le hC₁),
    max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  have hp : (g n) ^ θ₂ ≤
      (Real.exp (C₁ * time n) * (f n) ^ θ₁) ^ θ₂ :=
    Real.rpow_le_rpow (hg n) (hN₁ n hn₁) hθ₂.le
  have hpow : ((f n) ^ θ₁) ^ θ₂ = (f n) ^ (θ₁ * θ₂) :=
    (Real.rpow_mul (hf n) θ₁ θ₂).symm
  have hexpPow : (Real.exp (C₁ * time n)) ^ θ₂ =
      Real.exp ((C₁ * time n) * θ₂) :=
    (Real.exp_mul (C₁ * time n) θ₂).symm
  have hexp : Real.exp (C₂ * time n) * Real.exp ((C₁ * time n) * θ₂) =
      Real.exp ((C₂ + θ₂ * C₁) * time n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    h n ≤ Real.exp (C₂ * time n) * (g n) ^ θ₂ := hN₂ n hn₂
    _ ≤ Real.exp (C₂ * time n) *
        (Real.exp (C₁ * time n) * (f n) ^ θ₁) ^ θ₂ :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = Real.exp (C₂ * time n) *
        ((Real.exp (C₁ * time n)) ^ θ₂ * ((f n) ^ θ₁) ^ θ₂) := by
      rw [Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg (hf n) θ₁)]
    _ = (Real.exp (C₂ * time n) * Real.exp ((C₁ * time n) * θ₂)) *
        (f n) ^ (θ₁ * θ₂) := by
      rw [hexpPow, hpow]
      ring
    _ = Real.exp ((C₂ + θ₂ * C₁) * time n) * (f n) ^ (θ₁ * θ₂) := by
      rw [hexp]

end ZHPreprint.RouterAlgebra

#print axioms ZHPreprint.RouterAlgebra.quadraticDecay_of_separatedBounds
#print axioms ZHPreprint.RouterAlgebra.powerTransfer_of_paired
#print axioms ZHPreprint.RouterAlgebra.powerTransfer_trans
