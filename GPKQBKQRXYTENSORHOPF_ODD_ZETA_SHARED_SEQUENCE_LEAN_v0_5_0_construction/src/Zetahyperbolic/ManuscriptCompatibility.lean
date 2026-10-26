import Zetahyperbolic.Section2Checked
import Theorem_2_5_Lagrange_Pole_Diagonalization
import Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk

/-! Exact compatibility of the original and reconstructed pencils for arbitrary
k, m, N and K. No specialized zeta-value application is imported. -/
noncomputable section
open scoped BigOperators Matrix Polynomial
open Polynomial
namespace Zetahyperbolic
namespace ManuscriptCompatibility

/-- The original structural parameters, with the moment order supplied separately. -/
def toParameters (p : HankelParams) (k : ℕ) : ManuscriptChain.Real.Parameters :=
  ⟨k, p.m, p.N, p.K⟩

@[simp] theorem toParameters_h (p : HankelParams) (k : ℕ) :
    (toParameters p k).h = p.h := rfl

theorem toParameters_admissible (p : HankelParams) (k : ℕ) (hk : 1 ≤ k) :
    ManuscriptChain.Real.Admissible (toParameters p k) := by
  exact ⟨hk, p.hm, p.hN, p.hK⟩

/-- The original Icc convention and the checked chain's shifted-range convention agree. -/
theorem harmonicWeight_eq_harmonic (s n : ℕ) :
    harmonicWeight s n = ManuscriptChain.Real.harmonic s n := by
  induction n with
  | zero => simp [harmonicWeight, ManuscriptChain.Real.harmonic]
  | succ n ih =>
      rw [harmonicWeight_succ, ManuscriptChain.Real.harmonic,
        Finset.sum_range_succ, ← ManuscriptChain.Real.harmonic, ← ih]
      simp [one_div]

theorem D_poly_eq_D (n : ℕ) : D_poly n = ManuscriptChain.Real.D n := by
  induction n with
  | zero => simp [D_poly, ManuscriptChain.Real.D]
  | succ n ih =>
      unfold D_poly ManuscriptChain.Real.D at *
      rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_range_succ, ih]

theorem tailPolynomial_eq_tailD (p : HankelParams) (k : ℕ) :
    tailPolynomial p.N p.K = ManuscriptChain.Real.tailD (toParameters p k) := rfl

theorem muMonomial_eq_monomialMoment (k e : ℕ) :
    muMonomial k e = ManuscriptChain.Real.monomialMoment k e := rfl

theorem kernelNumerator_eq_numerator (p : HankelParams) (k i j : ℕ) :
    kernelNumerator p (i + j) =
      ManuscriptChain.Real.numerator (toParameters p k) i j := by
  simp only [kernelNumerator, ManuscriptChain.Real.numerator, toParameters, D_poly_eq_D]

/-- Simple-pole functionals agree, including their X-independent terms. -/
theorem muPolePoly_eq_affine (k a : ℕ) :
    muPolePoly k a =
      C (ManuscriptChain.Real.poleConstant k a) + C ((a : ℚ) ^ (2 * k)) * X := by
  simp only [muPolePoly, ManuscriptChain.Real.poleConstant, harmonicWeight_eq_harmonic,
    map_add, map_sub, map_neg, map_mul]
  ring

/-- The selected partial-fraction residues equal the explicit derivative residues. -/
theorem kernelRatElem_residue_eq (p : HankelParams) (k i j a : ℕ)
    (ha : a ∈ Finset.Icc (p.N + 1) p.K) :
    (kernelRatElem p (i + j)).poleRes a =
      ManuscriptChain.Real.residue (toParameters p k) i j a := by
  rw [kernelRatElem_poleRes_eq_prod p (i + j) a ha,
    kernelNumerator_eq_numerator p k i j]
  unfold ManuscriptChain.Real.residue
  rw [← tailPolynomial_eq_tailD, tailPolynomial_derivative_eval_pole p.N p.K a ha]

/-- The polynomial part selected by partial fractions is the Euclidean quotient.
The remainder degree is proved from the simple tail factors. -/
theorem kernelRatElem_polyPart_eq_div (p : HankelParams) (d : ℕ) :
    (kernelRatElem p d).polyPart = kernelNumerator p d / tailPolynomial p.N p.K := by
  classical
  let s := Finset.Icc (p.N + 1) p.K
  let g : ℕ → ℚ[X] := fun a => X + C ((a : ℚ) ^ 2)
  let data := kernelPartialFractionData p d
  let rem : ℚ[X] := ∑ a ∈ s, data.remainder a * ∏ b ∈ s.erase a, g b
  have hg (a : ℕ) : (g a).Monic := monic_X_add_C _
  have hmonic : (tailPolynomial p.N p.K).Monic :=
    monic_prod_of_monic s g (fun a _ => hg a)
  have hdegree : rem.degree < (tailPolynomial p.N p.K).degree := by
    change (∑ a ∈ s, data.remainder a * ∏ b ∈ s.erase a, g b).degree <
      (∏ a ∈ s, g a).degree
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 ?_)
    · rw [bot_lt_iff_ne_bot, degree_ne_bot]
      exact hmonic.ne_zero
    · intro a ha
      rw [← Finset.mul_prod_erase s g ha, mul_comm (g a), (hg a).degree_mul]
      refine (degree_mul_le _ _).trans_lt ?_
      have hnb : (∏ b ∈ s.erase a, g b).degree ≠ ⊥ := by
        rw [degree_ne_bot]
        exact (monic_prod_of_monic _ g (fun b _ => hg b)).ne_zero
      rw [add_comm, WithBot.add_lt_add_iff_left hnb]
      exact data.remainder_degree a ha
  have hidentity : rem + tailPolynomial p.N p.K * data.quotient = kernelNumerator p d := by
    rw [data.numerator_eq]
    change rem + tailPolynomial p.N p.K * data.quotient =
      data.quotient * tailPolynomial p.N p.K + rem
    ring
  have hu := div_modByMonic_unique data.quotient rem hmonic ⟨hidentity, hdegree⟩
  rw [divByMonic_eq_div _ hmonic] at hu
  exact hu.1.symm

theorem kernelRatElem_polyPart_eq_quotient (p : HankelParams) (k i j : ℕ) :
    (kernelRatElem p (i + j)).polyPart =
      ManuscriptChain.Real.quotient (toParameters p k) i j := by
  rw [kernelRatElem_polyPart_eq_div, kernelNumerator_eq_numerator p k i j,
    tailPolynomial_eq_tailD p k]
  rfl

theorem polynomialMoment_sum (k : ℕ) (q : ℚ[X]) :
    (∑ e ∈ Finset.range (q.natDegree + 1), C (q.coeff e * muMonomial k e)) =
      C (ManuscriptChain.Real.polynomialMoment k q) := by
  rw [← map_sum]
  congr 1
  have h := q.sum_over_range (f := fun e a => a * muMonomial k e) (by simp)
  simpa [Polynomial.sum, ManuscriptChain.Real.polynomialMoment,
    muMonomial_eq_monomialMoment] using h.symm

/-- The actual original pencil equals the pencil used by the checked main chain. -/
theorem G_pencil_eq_pencil (p : HankelParams) (k : ℕ) :
    G_pencil p k = ManuscriptChain.Real.pencil (toParameters p k) := by
  classical
  funext i j
  unfold G_pencil muFunctionalPoly
  rw [polynomialMoment_sum, kernelRatElem_polyPart_eq_quotient p k i.val j.val]
  have htail :
      (∑ a ∈ Finset.Icc 1 p.K,
        C ((kernelRatElem p (i.val + j.val)).poleRes a) * muPolePoly k a) =
      ∑ a ∈ Finset.Icc (p.N + 1) p.K,
        C ((kernelRatElem p (i.val + j.val)).poleRes a) * muPolePoly k a := by
    symm
    apply Finset.sum_subset
    · intro a ha
      simp only [Finset.mem_Icc] at ha ⊢
      omega
    · intro a ha hanot
      have haold : a ∈ Finset.Icc 1 p.N := by
        simp only [Finset.mem_Icc] at ha hanot ⊢
        omega
      rw [kernelRatElem_poleRes_old_zero p (i.val + j.val) a haold]
      simp
  change C (ManuscriptChain.Real.polynomialMoment k
      (ManuscriptChain.Real.quotient (toParameters p k) i.val j.val)) +
    (∑ a ∈ Finset.Icc 1 p.K,
      C ((kernelRatElem p (i.val + j.val)).poleRes a) * muPolePoly k a) = _
  rw [htail]
  have hterms :
      (∑ a ∈ Finset.Icc (p.N + 1) p.K,
        C ((kernelRatElem p (i.val + j.val)).poleRes a) * muPolePoly k a) =
      ∑ a ∈ Finset.Icc (p.N + 1) p.K,
        C (ManuscriptChain.Real.residue (toParameters p k) i.val j.val a) *
          (C (ManuscriptChain.Real.poleConstant k a) + C ((a : ℚ) ^ (2 * k)) * X) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [kernelRatElem_residue_eq p k i.val j.val a ha, muPolePoly_eq_affine]
  rw [hterms]
  simp only [ManuscriptChain.Real.pencil, ManuscriptChain.Real.entryA,
    ManuscriptChain.Real.entryM, toParameters, map_add, map_sum,
    map_mul, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  simp only [mul_left_comm, mul_comm, add_assoc]

theorem Delta_poly_eq_delta (p : HankelParams) (k : ℕ) :
    Delta_poly p k = ManuscriptChain.Real.delta (toParameters p k) := by
  unfold Delta_poly ManuscriptChain.Real.delta
  rw [G_pencil_eq_pencil]
  rfl

theorem gram_eq_original_evaluation (p : HankelParams) (k : ℕ) (x : ℝ) :
    ManuscriptChain.Real.gram (toParameters p k) x =
      fun i j => (G_pencil p k i j).eval₂ (algebraMap ℚ ℝ) x := by
  ext i j
  rw [G_pencil_eq_pencil]
  simp [ManuscriptChain.Real.gram, ManuscriptChain.Real.evalQ,
    ManuscriptChain.Real.realPolynomial, Polynomial.eval_map]
  rfl

/-- The derivative matrix bridge already follows from the proved residue identities. -/
theorem M_deriv_entry_eq (p : HankelParams) (k : ℕ) (i j : Fin p.h) :
    M_deriv p k i j =
      ManuscriptChain.Real.entryM (toParameters p k) i.val j.val := by
  rw [M_deriv_entry_eq_tail_residue_sum]
  unfold ManuscriptChain.Real.entryM
  apply Finset.sum_congr rfl
  intro a ha
  rw [kernelRatElem_residue_eq p k i.val j.val a ha]
  rfl

end ManuscriptCompatibility
end Zetahyperbolic

#print axioms Zetahyperbolic.ManuscriptCompatibility.G_pencil_eq_pencil
#print axioms Zetahyperbolic.ManuscriptCompatibility.Delta_poly_eq_delta
#print axioms Zetahyperbolic.ManuscriptCompatibility.M_deriv_entry_eq
