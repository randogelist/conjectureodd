import ANALYTIC_FRONTIER
import Zetahyperbolic.AnalyticMainChain
import Theorem_3_1_Pole_Integral_Identity

/-!
# General odd-weight theorem with the analytic input discharged

The proved simple-pole integral identity constructs the actual positive moment
realization. All conclusions below require only the structural parameter
conditions k,m,N >= 1 and N < K. No Gram positivity, integral evaluation,
spectral certificate, or arithmetic growth estimate is supplied as an input.
The result concerns the determinant's roots, not irrationality of zeta values.
-/

noncomputable section

namespace ManuscriptChain

/-- The concrete hyperbolic measure realizes the actual rational moments. -/
def REALIZATION (p : Real.Parameters) (hp : Real.Admissible p) :
    Real.PositiveMomentRealization p :=
  REALIZATION_FROM_POLE_INTEGRALS p hp
    (Hyperbolic.poleIntegralIdentity p.k hp.k_pos)

/-- Positive definiteness is now a conclusion for every admissible instance. -/
theorem GRAM_POSITIVE (p : Real.Parameters) (hp : Real.Admissible p) :
    General.GramPositive p :=
  (REALIZATION p hp).gram_posDef

/-- General odd-weight spectral theorem with no unproved analytic premise. -/
theorem MAIN_CHAIN_UNCONDITIONAL (p : Real.Parameters) (hp : Real.Admissible p) :
    General.GeneralStatement p :=
  MAIN_CHAIN p hp (GRAM_POSITIVE p hp)

/-- A positive disk free of roots, with a root at exactly its boundary radius. -/
theorem EXACT_ZERO_FREE_DISK (p : Real.Parameters) (hp : Real.Admissible p) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ z : ℂ, ‖z - (Real.zeta p.weight : ℂ)‖ < radius →
        ¬ General.ComplexRoot p z) ∧
      (∃ z : ℂ, General.ComplexRoot p z ∧
        ‖z - (Real.zeta p.weight : ℂ)‖ = radius) := by
  let positive := GRAM_POSITIVE p hp
  exact ⟨General.zeroFreeRadius p hp positive,
    General.zeroFreeRadius_pos p hp positive,
    General.complex_zero_free_disk p hp positive,
    General.complex_root_on_boundary p hp positive⟩

end ManuscriptChain

namespace Zetahyperbolic
open ManuscriptCompatibility

/-- Positive definiteness of the original uploaded pencil. -/
theorem GRAM_POSITIVE_ORIGINAL (p : HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    GramPositiveOriginal p k :=
  (gramPositiveOriginal_iff p k).mpr
    (ManuscriptChain.GRAM_POSITIVE (toParameters p k) (toParameters_admissible p k hk))

/-- The general theorem on the original pencil and its exact compatibility map. -/
theorem MAIN_CHAIN_UNCONDITIONAL (p : HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    ManuscriptChain.General.GeneralStatement (toParameters p k) :=
  MAIN_CHAIN p k hk (GRAM_POSITIVE_ORIGINAL p k hk)

/-- Every original determinant root is real and outside the positive disk;
one root attains the boundary, so the radius is exact. -/
theorem ORIGINAL_EXACT_ZERO_FREE_DISK (p : HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    ∃ radius : ℝ, 0 < radius ∧
      (∀ z : ℂ, (Delta_poly p k).eval₂ (algebraMap ℚ ℂ) z = 0 →
        z.im = 0 ∧
        z ≠ (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ) ∧
        radius ≤ ‖z - (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ)‖) ∧
      (∃ z : ℂ, (Delta_poly p k).eval₂ (algebraMap ℚ ℂ) z = 0 ∧
        ‖z - (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ)‖ = radius) := by
  let q := toParameters p k
  have hq : ManuscriptChain.Real.Admissible q := toParameters_admissible p k hk
  have hg : ManuscriptChain.General.GramPositive q :=
    ManuscriptChain.GRAM_POSITIVE q hq
  refine ⟨ManuscriptChain.General.zeroFreeRadius q hq hg,
    ManuscriptChain.General.zeroFreeRadius_pos q hq hg, ?_, ?_⟩
  · intro z hz
    have hroot : ManuscriptChain.General.ComplexRoot q z := by
      simpa [ManuscriptChain.General.ComplexRoot, q, Delta_poly_eq_delta] using hz
    have hd := ManuscriptChain.General.complex_root_distance q hq hg z hroot
    change ManuscriptChain.General.zeroFreeRadius q hq hg ≤
      ‖z - (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ)‖ at hd
    refine ⟨ManuscriptChain.General.roots_real q hg z hroot, ?_, hd⟩
    intro heq
    rw [heq, sub_self, norm_zero] at hd
    exact (not_le_of_gt (ManuscriptChain.General.zeroFreeRadius_pos q hq hg)) hd
  · obtain ⟨z, hz, hd⟩ := ManuscriptChain.General.complex_root_on_boundary q hq hg
    refine ⟨z, ?_, hd⟩
    simpa [ManuscriptChain.General.ComplexRoot, q, Delta_poly_eq_delta] using hz

end Zetahyperbolic

#print axioms ManuscriptChain.REALIZATION
#print axioms ManuscriptChain.GRAM_POSITIVE
#print axioms ManuscriptChain.MAIN_CHAIN_UNCONDITIONAL
#print axioms ManuscriptChain.EXACT_ZERO_FREE_DISK
#print axioms Zetahyperbolic.GRAM_POSITIVE_ORIGINAL
#print axioms Zetahyperbolic.MAIN_CHAIN_UNCONDITIONAL
#print axioms Zetahyperbolic.ORIGINAL_EXACT_ZERO_FREE_DISK
