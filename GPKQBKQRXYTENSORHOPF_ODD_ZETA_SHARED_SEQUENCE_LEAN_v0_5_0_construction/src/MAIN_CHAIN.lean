import Theorem_2_4_Canonical_Basis_Invariance
import Theorem_3_1_General_Odd_Weight_Endpoint
import Theorem_3_1_Positive_Moment_Realization
import Theorem_4_1_Spectral_Irrationality_Measure_Criterion

/-!
# General odd-weight manuscript chain

The primary endpoint covers every admissible k,m,N,K and weight 2*k+1.
Exact degree and derivative nonsingularity are unconditional finite algebra.
Gram positivity supplies real spectral factors and a positive complex zero-free
disk. This module exposes positivity as an explicit argument so that analytic
constructions can be assembled separately. Irrationality requires separate
arithmetic and quantitative inputs to the generic transfer theorem.
Specialized zeta(5) endpoints are exported by ZETA5_APPLICATION instead.
-/

namespace ManuscriptChain

/-- Principal theorem for arbitrary odd weight and admissible dimensions. -/
theorem MAIN_CHAIN (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : General.GramPositive p) : General.GeneralStatement p :=
  General.theorem_3_1_general p hp positive

/-- A genuine analytic moment realization suffices for the spectral endpoint. -/
theorem MAIN_CHAIN_FROM_MOMENTS (p : Real.Parameters) (hp : Real.Admissible p)
    (realization : Real.PositiveMomentRealization p) : General.GeneralStatement p :=
  MAIN_CHAIN p hp realization.gram_posDef

/-- Uniform generality requires positivity for every admissible parameter set. -/
theorem MAIN_CHAIN_UNIFORM
    (positive : ∀ p : Real.Parameters, Real.Admissible p → General.GramPositive p) :
    ∀ p : Real.Parameters, Real.Admissible p → General.GeneralStatement p :=
  fun p hp => MAIN_CHAIN p hp (positive p hp)

/-- Independent Diophantine transfer for any real target, with all quantitative
inputs explicit. The general spectral endpoint alone does not supply them. -/
theorem GENERAL_DIOPHANTINE_TRANSFER
    {Q : ℕ → Polynomial ℤ} {ξ : ℝ} {radius budget : ℕ → ℝ} {n₀ μ b₀ : ℕ}
    (comparison : RealTransfer.LocalComparison Q ξ radius n₀)
    (decay : RealTransfer.Decay Q ξ budget n₀)
    (index : RealTransfer.IndexBudget Q radius budget n₀ μ b₀) :
    RealTransfer.RationalMeasure ξ μ b₀ ∧ Irrational ξ :=
  ⟨RealTransfer.conditional_measure comparison decay index,
    RealTransfer.conditional_irrational comparison decay index⟩

end ManuscriptChain

#print axioms ManuscriptChain.MAIN_CHAIN
#print axioms ManuscriptChain.MAIN_CHAIN_FROM_MOMENTS
#print axioms ManuscriptChain.MAIN_CHAIN_UNIFORM
#print axioms ManuscriptChain.GENERAL_DIOPHANTINE_TRANSFER
