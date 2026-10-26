import Definition_2_1_Order_s_Rational_Moment_Functional
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Tactic.Ring

/-!
# Theorem 2.4 (Canonical basis invariance)

PDF p. 6. The rational change-of-basis matrix identity, determinant scaling,
root preservation, and invariance of primitive integer polynomials up to sign
are proved. PrimitiveNormalization records the paper's positive rational
rescaling to a primitive integer polynomial. Its existence is constructed for
every nonzero rational polynomial by clearing denominators, removing content,
and correcting the sign. The final theorem specializes to the actual manuscript
pencil and constructs both normalizations from determinant nonvanishing.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace ManuscriptChain.BasisInvariance

def changeBasisPencil {h : ℕ} (G : Matrix (Fin h) (Fin h) ℚ[X])
    (A B : Matrix (Fin h) (Fin h) ℚ) : Matrix (Fin h) (Fin h) ℚ[X] :=
  A.map C * G * (B.map C).transpose

theorem changeBasisPencil_apply {h : ℕ} (G : Matrix (Fin h) (Fin h) ℚ[X])
    (A B : Matrix (Fin h) (Fin h) ℚ) (i j : Fin h) :
    changeBasisPencil G A B i j =
      ∑ r, ∑ s, C (A i r * B j s) * G r s := by
  simp only [changeBasisPencil, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem det_changeBasisPencil {h : ℕ} (G : Matrix (Fin h) (Fin h) ℚ[X])
    (A B : Matrix (Fin h) (Fin h) ℚ) :
    Matrix.det (changeBasisPencil G A B) = C (Matrix.det A * Matrix.det B) * Matrix.det G := by
  have hA : Matrix.det (A.map C) = C (Matrix.det A) := (Polynomial.C.map_det A).symm
  have hB : Matrix.det (B.map C) = C (Matrix.det B) := (Polynomial.C.map_det B).symm
  simp only [changeBasisPencil, Matrix.det_mul, Matrix.det_transpose, hA, hB, map_mul]
  ring

theorem det_changeBasisPencil_ne_zero_iff {h : ℕ} (G : Matrix (Fin h) (Fin h) ℚ[X])
    (A B : Matrix (Fin h) (Fin h) ℚ)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) :
    Matrix.det (changeBasisPencil G A B) ≠ 0 ↔ Matrix.det G ≠ 0 := by
  rw [det_changeBasisPencil]
  simp [hA, hB]

theorem changeBasisPencil_eval_zero_iff {h : ℕ} (G : Matrix (Fin h) (Fin h) ℚ[X])
    (A B : Matrix (Fin h) (Fin h) ℚ)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) (x : ℝ) :
    Real.evalQ (Matrix.det (changeBasisPencil G A B)) x = 0 ↔
      Real.evalQ (Matrix.det G) x = 0 := by
  rw [det_changeBasisPencil]
  simp [Real.evalQ, Real.realPolynomial, hA, hB]

structure PrimitiveNormalization (f : ℚ[X]) where
  polynomial : ℤ[X]
  primitive : polynomial.IsPrimitive
  scale : ℚ
  scale_pos : 0 < scale
  identity : polynomial.map (Int.castRingHom ℚ) = C scale * f

theorem primitive_eq_or_eq_neg_of_associated {P Q : ℤ[X]}
    (h : Associated P Q) : P = Q ∨ P = -Q := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨a, ha, hau⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have ha' : a = 1 ∨ a = -1 := Int.isUnit_iff.mp ha
  rcases ha' with rfl | rfl
  · left
    simpa [← hau] using hu
  · right
    simpa [← hau] using congrArg Neg.neg hu

theorem primitive_scalar_unique {P Q : ℤ[X]} (hP : P.IsPrimitive) (hQ : Q.IsPrimitive)
    {c : ℚ} (hc : c ≠ 0)
    (h : Q.map (Int.castRingHom ℚ) = C c * P.map (Int.castRingHom ℚ)) :
    P = Q ∨ P = -Q := by
  apply primitive_eq_or_eq_neg_of_associated
  apply associated_of_dvd_dvd
  · apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast P Q hP).mpr
    exact ⟨C c, by rw [h]; ring⟩
  · apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast Q P hQ).mpr
    refine ⟨C c⁻¹, ?_⟩
    rw [h]
    calc
      P.map (Int.castRingHom ℚ) = C (c * c⁻¹) * P.map (Int.castRingHom ℚ) := by
        simp [hc]
      _ = C c * P.map (Int.castRingHom ℚ) * C c⁻¹ := by rw [map_mul]; ring

theorem primitiveNormalization_scalar_invariance {f g : ℚ[X]}
    (nf : PrimitiveNormalization f) (ng : PrimitiveNormalization g)
    {c : ℚ} (hc : c ≠ 0) (h : g = C c * f) :
    ng.polynomial = nf.polynomial ∨ ng.polynomial = -nf.polynomial := by
  apply primitive_scalar_unique ng.primitive nf.primitive
    (c := nf.scale / (ng.scale * c))
    (div_ne_zero (ne_of_gt nf.scale_pos) (mul_ne_zero (ne_of_gt ng.scale_pos) hc))
  simp only [nf.identity, ng.identity, h]
  have hf : nf.scale ≠ 0 := ne_of_gt nf.scale_pos
  have hg : ng.scale ≠ 0 := ne_of_gt ng.scale_pos
  simp only [← mul_assoc, ← map_mul]
  congr 1
  field_simp

theorem theorem_2_4_canonical_basis_invariance (p : Real.Parameters)
    (A B : Matrix (Fin p.h) (Fin p.h) ℚ)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0)
    (n₀ : PrimitiveNormalization (Real.delta p))
    (nAB : PrimitiveNormalization (Matrix.det (changeBasisPencil (Real.pencil p) A B))) :
    nAB.polynomial = n₀.polynomial ∨ nAB.polynomial = -n₀.polynomial := by
  apply primitiveNormalization_scalar_invariance n₀ nAB (mul_ne_zero hA hB)
  exact det_changeBasisPencil (Real.pencil p) A B

open scoped nonZeroDivisors

theorem primitiveNormalization_nonempty (f : ℚ[X]) (hf : f ≠ 0) :
    Nonempty (PrimitiveNormalization f) := by
  let q : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f
  obtain ⟨b, hb, heq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f
  have hbZ : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast hbZ
  have hq : q ≠ 0 := by
    exact mt IsFractionRing.integerNormalization_eq_zero_iff.mp hf
  have hdZ : q.content ≠ 0 := mt Polynomial.content_eq_zero_iff.mp hq
  have hdQ : (q.content : ℚ) ≠ 0 := by exact_mod_cast hdZ
  have heq' : q.map (Int.castRingHom ℚ) = C (b : ℚ) * f := by
    simpa [q, Algebra.smul_def] using heq
  have hcontent : C (b : ℚ) * f =
      C (q.content : ℚ) * q.primPart.map (Int.castRingHom ℚ) := by
    rw [← heq']
    simpa using congrArg (fun p : ℤ[X] => p.map (Int.castRingHom ℚ))
      q.eq_C_content_mul_primPart
  let t : ℚ := (b : ℚ) / (q.content : ℚ)
  have ht : t ≠ 0 := div_ne_zero hbQ hdQ
  have hprimitive : q.primPart.map (Int.castRingHom ℚ) = C t * f := by
    calc
      q.primPart.map (Int.castRingHom ℚ) =
          C (q.content : ℚ)⁻¹ * (C (q.content : ℚ) * q.primPart.map (Int.castRingHom ℚ)) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hdQ, map_one, one_mul]
      _ = C (q.content : ℚ)⁻¹ * (C (b : ℚ) * f) := by rw [← hcontent]
      _ = C t * f := by
        rw [← mul_assoc, ← map_mul]
        simp only [t, div_eq_mul_inv, mul_comm]
  by_cases htpos : 0 < t
  · exact ⟨⟨q.primPart, q.isPrimitive_primPart, t, htpos, hprimitive⟩⟩
  · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht
    refine ⟨⟨-q.primPart, ?_, -t, neg_pos.mpr htneg, ?_⟩⟩
    · intro a ha
      apply q.isPrimitive_primPart a
      simpa using ha
    · simpa only [Polynomial.map_neg, map_neg, neg_mul] using congrArg Neg.neg hprimitive

noncomputable def primitiveNormalization (f : ℚ[X]) (hf : f ≠ 0) :
    PrimitiveNormalization f :=
  Classical.choice (primitiveNormalization_nonempty f hf)

theorem primitiveNormalization_exists_iff (f : ℚ[X]) :
    Nonempty (PrimitiveNormalization f) ↔ f ≠ 0 := by
  refine ⟨?_, primitiveNormalization_nonempty f⟩
  rintro ⟨n⟩ rfl
  have hzero : n.polynomial.map (Int.castRingHom ℚ) = 0 := by
    simpa using n.identity
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  exact n.primitive.ne_zero ((Polynomial.map_injective _ hinj) (by simpa using hzero))

theorem theorem_2_4_constructed_canonical_basis_invariance (p : Real.Parameters)
    (A B : Matrix (Fin p.h) (Fin p.h) ℚ)
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0) (hdelta : Real.delta p ≠ 0) :
    let n₀ := primitiveNormalization (Real.delta p) hdelta
    let nAB := primitiveNormalization
      (Matrix.det (changeBasisPencil (Real.pencil p) A B))
      ((det_changeBasisPencil_ne_zero_iff (Real.pencil p) A B hA hB).mpr hdelta)
    nAB.polynomial = n₀.polynomial ∨ nAB.polynomial = -n₀.polynomial := by
  exact theorem_2_4_canonical_basis_invariance p A B hA hB _ _

end ManuscriptChain.BasisInvariance
