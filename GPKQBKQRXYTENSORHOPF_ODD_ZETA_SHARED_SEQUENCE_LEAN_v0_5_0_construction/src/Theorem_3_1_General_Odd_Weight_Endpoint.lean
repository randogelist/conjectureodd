import Theorem_2_5_Lagrange_Pole_Diagonalization
import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk

/-!
# General odd-weight Hankel theorem

For arbitrary k,m,N,K with k,m,N positive and N < K, the finite algebra
proves exact degree and derivative nonsingularity. One analytic input remains:
positive definiteness of the actual Gram matrix at zeta(2k+1).
From that input this module constructs the spectral factorization, identifies
all complex roots, and constructs a positive zero-free disk using the maximum
absolute spectral factor. No quantitative exponential estimate, arithmetic
multiplier estimate, or irrationality claim is assumed or concluded here.
Roots are real and avoid the center; pairwise distinctness is not asserted.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.General

/-- The exact analytic input for the general manuscript pencil. -/
def GramPositive (p : Real.Parameters) : Prop :=
  (Real.gram p (Real.zeta p.weight)).PosDef

/-- The rational determinant has full degree without a positivity assumption. -/
theorem delta_degree (p : Real.Parameters) : (Real.delta p).natDegree = p.h :=
  PoleDiagonalization.delta_natDegree p

theorem delta_nonzero (p : Real.Parameters) : Real.delta p ≠ 0 :=
  PoleDiagonalization.delta_ne_zero p

theorem derivative_nonsingular (p : Real.Parameters) :
    (Real.derivativeMatrix p).det ≠ 0 :=
  PoleDiagonalization.derivativeMatrix_det_ne_zero p

/-- Constructed spectral data: no factorization certificate is an extra input. -/
def factorization (p : Real.Parameters) (positive : GramPositive p) :
    Spectral.RootFactorization (Real.manuscriptPencil p) :=
  Spectral.rootFactorizationOfPosDef (Real.manuscriptPencil p) positive
    (derivative_nonsingular p)

def ComplexRoot (p : Real.Parameters) (z : ℂ) : Prop :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) z (Real.delta p) = 0

theorem complex_eval_transport (p : Real.Parameters) (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) z
        (Real.manuscriptPencil p).detPolynomial =
      Polynomial.eval₂ (algebraMap ℚ ℂ) z (Real.delta p) := by
  rw [Real.manuscriptPencil_detPolynomial, Real.realPolynomial, Polynomial.eval₂_map]
  congr 1

/-- Every complex root is one of the constructed real roots, and conversely. -/
theorem complex_root_iff (p : Real.Parameters) (positive : GramPositive p) (z : ℂ) :
    ComplexRoot p z ↔ ∃ i, z = ((factorization p positive).root i : ℂ) := by
  constructor
  · intro hz
    apply (factorization p positive).complex_root_location z
    rw [complex_eval_transport]
    exact hz
  · rintro ⟨i, rfl⟩
    unfold ComplexRoot
    rw [← complex_eval_transport]
    have he := Polynomial.eval₂_at_apply (algebraMap ℝ ℂ)
      ((factorization p positive).root i)
      (p := (Real.manuscriptPencil p).detPolynomial)
    simpa only [Complex.coe_algebraMap, (factorization p positive).eval_root,
      map_zero] using he

theorem roots_real (p : Real.Parameters) (positive : GramPositive p) (z : ℂ)
    (hz : ComplexRoot p z) : z.im = 0 := by
  obtain ⟨i, rfl⟩ := (complex_root_iff p positive z).mp hz
  simp

theorem roots_avoid_center (p : Real.Parameters) (positive : GramPositive p)
    (i : Fin p.h) : (factorization p positive).root i ≠ Real.zeta p.weight :=
  (factorization p positive).root_ne_center i

theorem center_nonvanishing (p : Real.Parameters) (positive : GramPositive p) :
    Real.evalQ (Real.delta p) (Real.zeta p.weight) ≠ 0 :=
  Real.delta_nonzero_of_positive p positive

theorem indices_nonempty (p : Real.Parameters) (hp : Real.Admissible p) :
    (Finset.univ : Finset (Fin p.h)).Nonempty := by
  exact ⟨⟨0, Nat.sub_pos_of_lt hp.N_lt_K⟩, Finset.mem_univ _⟩

/-- Maximum absolute spectral factor of the constructed pencil. -/
def spectralRadius (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : ℝ :=
  Finset.univ.sup' (indices_nonempty p hp)
    (fun i => |(factorization p positive).beta i|)

theorem beta_abs_le (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) (i : Fin p.h) :
    |(factorization p positive).beta i| ≤ spectralRadius p hp positive := by
  unfold spectralRadius
  exact Finset.le_sup' (fun j => |(factorization p positive).beta j|)
    (Finset.mem_univ i)

theorem spectralRadius_pos (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : 0 < spectralRadius p hp positive := by
  let i : Fin p.h := ⟨0, Nat.sub_pos_of_lt hp.N_lt_K⟩
  exact lt_of_lt_of_le
    (abs_pos.mpr ((factorization p positive).beta_ne_zero i))
    (beta_abs_le p hp positive i)

/-- No extra norm estimate is needed to construct this positive radius. -/
def zeroFreeRadius (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : ℝ := 1 / spectralRadius p hp positive

theorem zeroFreeRadius_pos (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : 0 < zeroFreeRadius p hp positive := by
  exact one_div_pos.mpr (spectralRadius_pos p hp positive)

theorem complex_root_distance (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) (z : ℂ) (hz : ComplexRoot p z) :
    zeroFreeRadius p hp positive ≤ ‖z - (Real.zeta p.weight : ℂ)‖ := by
  obtain ⟨i, rfl⟩ := (complex_root_iff p positive z).mp hz
  have h := (factorization p positive).root_distance_lower_bound
    (spectralRadius p hp positive) (beta_abs_le p hp positive) i
  simpa [zeroFreeRadius, ← Complex.ofReal_sub] using h

theorem complex_zero_free_disk (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) (z : ℂ)
    (hz : ‖z - (Real.zeta p.weight : ℂ)‖ < zeroFreeRadius p hp positive) :
    ¬ ComplexRoot p z := by
  intro hroot
  exact (not_lt_of_ge (complex_root_distance p hp positive z hroot)) hz

/-- The radius is attained by a root, so it is the exact distance to the roots. -/
theorem zeroFreeRadius_attained (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) :
    ∃ i, |(factorization p positive).root i - Real.zeta p.weight| =
      zeroFreeRadius p hp positive := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (indices_nonempty p hp)
    (fun i => |(factorization p positive).beta i|)
  refine ⟨i, ?_⟩
  simpa only [zeroFreeRadius, spectralRadius, hi, Real.manuscriptPencil_center] using
    (factorization p positive).root_distance i

theorem complex_root_on_boundary (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) :
    ∃ z : ℂ, ComplexRoot p z ∧
      ‖z - (Real.zeta p.weight : ℂ)‖ = zeroFreeRadius p hp positive := by
  obtain ⟨i, hi⟩ := zeroFreeRadius_attained p hp positive
  refine ⟨((factorization p positive).root i : ℂ),
    (complex_root_iff p positive _).mpr ⟨i, rfl⟩, ?_⟩
  simpa [← Complex.ofReal_sub] using hi

theorem center_eq_riemannZeta (p : Real.Parameters) (hp : Real.Admissible p) :
    Real.zeta p.weight = (riemannZeta (p.weight : ℂ)).re := by
  apply Real.zeta_eq_riemannZeta_re
  unfold Real.Parameters.weight
  have hk := hp.k_pos
  omega

/-- General theorem, expressed entirely on the actual manuscript family. -/
def GeneralStatement (p : Real.Parameters) : Prop :=
  (Real.delta p).natDegree = p.h ∧
  (Real.derivativeMatrix p).det ≠ 0 ∧
  Real.zeta p.weight = (riemannZeta (p.weight : ℂ)).re ∧
  ∃ (c : Spectral.RootFactorization (Real.manuscriptPencil p)) (radius : ℝ),
    0 < radius ∧
    (∀ z : ℂ, ComplexRoot p z ↔ ∃ i, z = (c.root i : ℂ)) ∧
    (∀ i, c.root i ≠ Real.zeta p.weight) ∧
    (∀ z : ℂ, ComplexRoot p z → z.im = 0) ∧
    (∀ z : ℂ, ‖z - (Real.zeta p.weight : ℂ)‖ < radius → ¬ ComplexRoot p z)

/-- The general odd-weight endpoint has exactly one analytic input. -/
theorem theorem_3_1_general (p : Real.Parameters) (hp : Real.Admissible p)
    (positive : GramPositive p) : GeneralStatement p := by
  refine ⟨delta_degree p, derivative_nonsingular p, center_eq_riemannZeta p hp,
    factorization p positive, zeroFreeRadius p hp positive,
    zeroFreeRadius_pos p hp positive, ?_, ?_, ?_, ?_⟩
  · exact complex_root_iff p positive
  · exact roots_avoid_center p positive
  · exact roots_real p positive
  · exact complex_zero_free_disk p hp positive

end ManuscriptChain.General

#print axioms ManuscriptChain.General.delta_degree
#print axioms ManuscriptChain.General.derivative_nonsingular
#print axioms ManuscriptChain.General.complex_zero_free_disk
#print axioms ManuscriptChain.General.theorem_3_1_general
