import ANALYTIC_FRONTIER
import Zetahyperbolic.MainChain
import Zetahyperbolic.ManuscriptCompatibility

/-!
# Original-pencil endpoint from the simple-pole integral identity

These theorems apply the concrete hyperbolic measure construction to the
original uploaded pencil. The structural admissibility conditions follow
from `HankelParams` and `1 ≤ k`; no separate admissibility or Gram-positivity
argument is required. The special-function evaluation
`ManuscriptChain.Hyperbolic.PoleIntegralIdentity k` is an explicit argument
to these decomposition lemmas. `MAIN_CHAIN_ASSEMBLED` supplies its proof
and exports the corresponding unconditional endpoints.
-/

noncomputable section

namespace Zetahyperbolic
open ManuscriptCompatibility

/-- Positivity of the original pencil from the remaining integral evaluation. -/
theorem GRAM_POSITIVE_ORIGINAL_FROM_POLE_INTEGRALS
    (p : HankelParams) (k : ℕ) (hk : 1 ≤ k)
    (hpole : ManuscriptChain.Hyperbolic.PoleIntegralIdentity k) :
    GramPositiveOriginal p k := by
  apply (gramPositiveOriginal_iff p k).mpr
  exact ManuscriptChain.GRAM_POSITIVE_FROM_POLE_INTEGRALS (toParameters p k)
    (toParameters_admissible p k hk) hpole

/-- The general statement for the original parameters, with admissibility
discharged internally and only the simple-pole identity supplied analytically. -/
theorem MAIN_CHAIN_FROM_POLE_INTEGRALS
    (p : HankelParams) (k : ℕ) (hk : 1 ≤ k)
    (hpole : ManuscriptChain.Hyperbolic.PoleIntegralIdentity k) :
    ManuscriptChain.General.GeneralStatement (toParameters p k) :=
  MAIN_CHAIN p k hk (GRAM_POSITIVE_ORIGINAL_FROM_POLE_INTEGRALS p k hk hpole)

/-- Reality of every complex root and a positive zero-free radius for the
actual original determinant, conditional on the displayed integral identity. -/
theorem MAIN_CHAIN_ORIGINAL_ROOTS_FROM_POLE_INTEGRALS
    (p : HankelParams) (k : ℕ) (hk : 1 ≤ k)
    (hpole : ManuscriptChain.Hyperbolic.PoleIntegralIdentity k) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ z : ℂ, (Delta_poly p k).eval₂ (algebraMap ℚ ℂ) z = 0 →
        z.im = 0 ∧
        z ≠ (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ) ∧
        radius ≤ ‖z - (ManuscriptChain.Real.zeta (2 * k + 1) : ℂ)‖ :=
  MAIN_CHAIN_ORIGINAL_ROOTS p k hk
    (GRAM_POSITIVE_ORIGINAL_FROM_POLE_INTEGRALS p k hk hpole)

/-- A uniform proof of the simple-pole identities would supply all original
parameter choices and all positive odd-weight indices. -/
theorem MAIN_CHAIN_UNIFORM_FROM_POLE_INTEGRALS
    (hpole : ∀ k : ℕ, 0 < k → ManuscriptChain.Hyperbolic.PoleIntegralIdentity k) :
    ∀ (p : HankelParams) (k : ℕ), 1 ≤ k →
      ManuscriptChain.General.GeneralStatement (toParameters p k) := by
  intro p k hk
  exact MAIN_CHAIN_FROM_POLE_INTEGRALS p k hk (hpole k hk)

end Zetahyperbolic

#print axioms Zetahyperbolic.GRAM_POSITIVE_ORIGINAL_FROM_POLE_INTEGRALS
#print axioms Zetahyperbolic.MAIN_CHAIN_FROM_POLE_INTEGRALS
#print axioms Zetahyperbolic.MAIN_CHAIN_ORIGINAL_ROOTS_FROM_POLE_INTEGRALS
#print axioms Zetahyperbolic.MAIN_CHAIN_UNIFORM_FROM_POLE_INTEGRALS
