import MAIN_CHAIN
import Zetahyperbolic.ManuscriptCompatibility

/-!
# General endpoint for the original uploaded pencil

The compatibility theorems identify the actual original rational pencil and
determinant at every odd weight. Positivity below is stated on that original
pencil, and is the remaining analytic premise. No specialized zeta application
or external irrationality assertion enters this module.
-/

noncomputable section
namespace Zetahyperbolic
open ManuscriptCompatibility

def GramPositiveOriginal (p : HankelParams) (k : ℕ) : Prop :=
  Matrix.PosDef (fun i j => (G_pencil p k i j).eval₂ (algebraMap ℚ ℝ)
    (ManuscriptChain.Real.zeta (2 * k + 1)))

theorem gramPositiveOriginal_iff (p : HankelParams) (k : ℕ) :
    GramPositiveOriginal p k ↔
      ManuscriptChain.General.GramPositive (toParameters p k) := by
  unfold GramPositiveOriginal ManuscriptChain.General.GramPositive
  rw [gram_eq_original_evaluation]
  rfl

/-- The principal endpoint is general in k,m,N,K. -/
theorem MAIN_CHAIN (p : HankelParams) (k : ℕ) (hk : 1 ≤ k)
    (positive : GramPositiveOriginal p k) :
    ManuscriptChain.General.GeneralStatement (toParameters p k) :=
  ManuscriptChain.MAIN_CHAIN (toParameters p k) (toParameters_admissible p k hk)
    ((gramPositiveOriginal_iff p k).mp positive)

/-- Full degree of the original determinant needs no analytic premise. -/
theorem original_delta_degree (p : HankelParams) (k : ℕ) :
    (Delta_poly p k).natDegree = p.h := by
  rw [Delta_poly_eq_delta]
  exact ManuscriptChain.General.delta_degree (toParameters p k)

/-- Explicit complex-root and disk statement on the original determinant. -/
theorem MAIN_CHAIN_ORIGINAL_ROOTS (p : HankelParams) (k : ℕ) (hk : 1 ≤ k)
    (positive : GramPositiveOriginal p k) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ z : ℂ, (Delta_poly p k).eval₂ (algebraMap ℚ ℂ) z = 0 →
        z.im = 0 ∧
        z ≠ (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ) ∧
        radius ≤ ‖z - (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ)‖ := by
  let q := toParameters p k
  have hq : ManuscriptChain.Real.Admissible q := toParameters_admissible p k hk
  have hg : ManuscriptChain.General.GramPositive q :=
    (gramPositiveOriginal_iff p k).mp positive
  refine ⟨ManuscriptChain.General.zeroFreeRadius q hq hg,
    ManuscriptChain.General.zeroFreeRadius_pos q hq hg, ?_⟩
  intro z hz
  have hroot : ManuscriptChain.General.ComplexRoot q z := by
    simpa [ManuscriptChain.General.ComplexRoot, q, Delta_poly_eq_delta] using hz
  have hd := ManuscriptChain.General.complex_root_distance q hq hg z hroot
  change ManuscriptChain.General.zeroFreeRadius q hq hg ≤
    ‖z - (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ)‖ at hd
  refine ⟨ManuscriptChain.General.roots_real q hg z hroot, ?_, hd⟩
  intro heq
  rw [heq, sub_self, norm_zero] at hd
  exact (not_le_of_gt (ManuscriptChain.General.zeroFreeRadius_pos q hq hg)) hd

end Zetahyperbolic

#print axioms Zetahyperbolic.MAIN_CHAIN
#print axioms Zetahyperbolic.original_delta_degree
#print axioms Zetahyperbolic.MAIN_CHAIN_ORIGINAL_ROOTS
