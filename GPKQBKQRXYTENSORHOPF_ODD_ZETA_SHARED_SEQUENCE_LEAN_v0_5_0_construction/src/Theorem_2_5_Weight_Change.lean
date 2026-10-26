import Theorem_2_5_Lagrange_Pole_Diagonalization

/-!
Exact weight change at fixed m,N,K. The pole nodes and Vandermonde matrix
remain fixed, while the pole weights acquire explicit even powers. This proves
the corresponding derivative-determinant and leading-coefficient identities.
No admissibility or asymptotic estimate is assumed or asserted.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.PoleDiagonalization

/-- Replace the odd-weight index, retaining the structural parameters m,N,K. -/
abbrev reweight (p : Real.Parameters) (k : ℕ) : Real.Parameters := { p with k := k }

@[simp] theorem reweight_h (p : Real.Parameters) (k : ℕ) :
    (reweight p k).h = p.h := rfl

@[simp] theorem poleIndex_reweight (p : Real.Parameters) (k : ℕ) (a : Fin p.h) :
    poleIndex (reweight p k) a = poleIndex p a := rfl

@[simp] theorem poleNode_reweight (p : Real.Parameters) (k : ℕ) (a : Fin p.h) :
    poleNode (reweight p k) a = poleNode p a := rfl

@[simp] theorem poleVandermonde_reweight (p : Real.Parameters) (k : ℕ) :
    poleVandermonde (reweight p k) = poleVandermonde p := rfl

/-- Increasing the index by step multiplies each pole weight by a^(2*step). -/
theorem poleWeight_reweight_add (p : Real.Parameters) (k step : ℕ) (a : Fin p.h) :
    poleWeight (reweight p (k + step)) a =
      poleWeight (reweight p k) a * (poleIndex p a : ℚ) ^ (2 * step) := by
  simp only [poleWeight, reweight, poleNode, poleIndex, Real.tailD]
  rw [Nat.mul_add, pow_add, mul_assoc]

/-- Exact derivative-determinant scaling, including the empty matrix case. -/
theorem rationalDerivativeMatrix_det_reweight_add
    (p : Real.Parameters) (k step : ℕ) :
    (rationalDerivativeMatrix (reweight p (k + step))).det =
      (rationalDerivativeMatrix (reweight p k)).det *
        ∏ a : Fin p.h, (poleIndex p a : ℚ) ^ (2 * step) := by
  rw [rationalDerivativeMatrix_det, rationalDerivativeMatrix_det]
  change (poleVandermonde p).det ^ 2 *
      (∏ a : Fin p.h, poleWeight (reweight p (k + step)) a) =
    ((poleVandermonde p).det ^ 2 *
      (∏ a : Fin p.h, poleWeight (reweight p k) a)) *
        ∏ a : Fin p.h, (poleIndex p a : ℚ) ^ (2 * step)
  simp_rw [poleWeight_reweight_add]
  erw [Finset.prod_mul_distrib, mul_assoc]

/-- A division-free comparison for any two weight indices. -/
theorem rationalDerivativeMatrix_det_reweight_cross
    (p : Real.Parameters) (k l : ℕ) :
    (rationalDerivativeMatrix (reweight p k)).det *
        (∏ a : Fin p.h, (poleIndex p a : ℚ) ^ (2 * l)) =
      (rationalDerivativeMatrix (reweight p l)).det *
        (∏ a : Fin p.h, (poleIndex p a : ℚ) ^ (2 * k)) := by
  have hk := rationalDerivativeMatrix_det_reweight_add p 0 k
  have hl := rationalDerivativeMatrix_det_reweight_add p 0 l
  erw [Nat.zero_add] at hk hl
  erw [hk, hl]
  ring

/-- The scaling factor is strictly positive for every geometry. -/
theorem reweight_factor_pos (p : Real.Parameters) (step : ℕ) :
    (0 : ℚ) < ∏ a : Fin p.h, (poleIndex p a : ℚ) ^ (2 * step) := by
  apply Finset.prod_pos
  intro a _
  exact pow_pos (by exact_mod_cast poleIndex_pos p a) _

/-- Nonsingularity gives an exact rational quotient as well. -/
theorem rationalDerivativeMatrix_det_reweight_ratio
    (p : Real.Parameters) (k step : ℕ) :
    (rationalDerivativeMatrix (reweight p (k + step))).det /
        (rationalDerivativeMatrix (reweight p k)).det =
      ∏ a : Fin p.h, (poleIndex p a : ℚ) ^ (2 * step) := by
  rw [rationalDerivativeMatrix_det_reweight_add]
  exact mul_div_cancel_left₀ _ (rationalDerivativeMatrix_det_ne_zero (reweight p k))

/-- The leading coefficient of the actual determinant has the same scaling. -/
theorem delta_leadingCoeff_reweight_add (p : Real.Parameters) (k step : ℕ) :
    (Real.delta (reweight p (k + step))).leadingCoeff =
      (Real.delta (reweight p k)).leadingCoeff *
        ∏ a : Fin p.h, (poleIndex p a : ℚ) ^ (2 * step) := by
  simpa only [delta_leadingCoeff] using rationalDerivativeMatrix_det_reweight_add p k step

/-- Cross-weight leading-coefficient comparison on the actual rational polynomials. -/
theorem delta_leadingCoeff_reweight_cross (p : Real.Parameters) (k l : ℕ) :
    (Real.delta (reweight p k)).leadingCoeff *
        (∏ a : Fin p.h, (poleIndex p a : ℚ) ^ (2 * l)) =
      (Real.delta (reweight p l)).leadingCoeff *
        (∏ a : Fin p.h, (poleIndex p a : ℚ) ^ (2 * k)) := by
  simpa only [delta_leadingCoeff] using rationalDerivativeMatrix_det_reweight_cross p k l

end ManuscriptChain.PoleDiagonalization

#print axioms ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix_det_reweight_add
#print axioms ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix_det_reweight_cross
#print axioms ManuscriptChain.PoleDiagonalization.rationalDerivativeMatrix_det_reweight_ratio
#print axioms ManuscriptChain.PoleDiagonalization.delta_leadingCoeff_reweight_add
#print axioms ManuscriptChain.PoleDiagonalization.delta_leadingCoeff_reweight_cross
