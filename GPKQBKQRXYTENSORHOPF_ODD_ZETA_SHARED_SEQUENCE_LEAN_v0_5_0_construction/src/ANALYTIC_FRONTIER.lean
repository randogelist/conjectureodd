import MAIN_CHAIN
import Theorem_3_1_Rational_Integral_Bridge

/-!
# The general endpoint from a simple-pole integral identity

The explicit hyperbolic density, all monomial moments, the actual weighted
measure, absence of atoms, integrability, and finite partial-fraction assembly
are now constructed and proved in Lean. The only analytic input to this
endpoint is `Hyperbolic.PoleIntegralIdentity p.k`. This module isolates that
input so the algebraic and analytic parts can be checked separately.

`Theorem_3_1_Pole_Integral_Identity` proves the identity using cotangent partial
fractions, changes of variables, and Gamma integrals. `MAIN_CHAIN_ASSEMBLED`
supplies that proof here and exposes endpoints requiring only admissibility.
The conditional interfaces below remain reusable decomposition lemmas.
-/

noncomputable section

namespace ManuscriptChain

/-- The actual moment measure is constructed from the single remaining
special-function evaluation. -/
def REALIZATION_FROM_POLE_INTEGRALS (p : Real.Parameters)
    (hp : Real.Admissible p) (hpole : Hyperbolic.PoleIntegralIdentity p.k) :
    Real.PositiveMomentRealization p :=
  ConcreteMoment.realization p (Hyperbolic.gram_eq_weighted_integral p hp hpole)

/-- All nondegeneracy, integrability, and algebraic assembly obligations are
discharged; only the displayed simple-pole integral identity remains. -/
theorem GRAM_POSITIVE_FROM_POLE_INTEGRALS (p : Real.Parameters)
    (hp : Real.Admissible p) (hpole : Hyperbolic.PoleIntegralIdentity p.k) :
    General.GramPositive p :=
  (REALIZATION_FROM_POLE_INTEGRALS p hp hpole).gram_posDef

/-- General odd-weight spectral theorem through the concrete analytic route. -/
theorem MAIN_CHAIN_FROM_POLE_INTEGRALS (p : Real.Parameters)
    (hp : Real.Admissible p) (hpole : Hyperbolic.PoleIntegralIdentity p.k) :
    General.GeneralStatement p :=
  MAIN_CHAIN p hp (GRAM_POSITIVE_FROM_POLE_INTEGRALS p hp hpole)

/-- One uniform simple-pole identity supplies every admissible instance. -/
theorem MAIN_CHAIN_UNIFORM_FROM_POLE_INTEGRALS
    (hpole : ∀ k : ℕ, 0 < k → Hyperbolic.PoleIntegralIdentity k) :
    ∀ p : Real.Parameters, Real.Admissible p → General.GeneralStatement p := by
  intro p hp
  exact MAIN_CHAIN_FROM_POLE_INTEGRALS p hp (hpole p.k hp.k_pos)

end ManuscriptChain

#print axioms ManuscriptChain.REALIZATION_FROM_POLE_INTEGRALS
#print axioms ManuscriptChain.GRAM_POSITIVE_FROM_POLE_INTEGRALS
#print axioms ManuscriptChain.MAIN_CHAIN_FROM_POLE_INTEGRALS
#print axioms ManuscriptChain.MAIN_CHAIN_UNIFORM_FROM_POLE_INTEGRALS
