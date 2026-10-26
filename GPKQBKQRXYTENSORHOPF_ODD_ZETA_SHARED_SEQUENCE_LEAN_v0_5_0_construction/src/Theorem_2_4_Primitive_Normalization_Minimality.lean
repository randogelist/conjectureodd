import Theorem_2_4_Canonical_Basis_Invariance

/-!
# Minimality of positive primitive normalization

Every positive rational rescaling of a rational polynomial that has integral
coefficients is a positive integer multiple of its positive primitive
normalization. Thus primitive normalization cannot increase a nonnegative
value relative to any explicit denominator-clearing construction.
-/

noncomputable section
open Polynomial

namespace ManuscriptChain.BasisInvariance

/-- An arbitrary integral positive rescaling is a positive integer multiple of
its primitive normalization, with the same relation between the scales. -/
theorem primitiveNormalization_integer_multiple {f : ℚ[X]}
    (nf : PrimitiveNormalization f) {g : ℤ[X]} {c : ℚ}
    (hc : 0 < c) (hg : g.map (Int.castRingHom ℚ) = C c * f) :
    ∃ d : ℤ, 0 < d ∧ g = C d * nf.polynomial ∧ c = (d : ℚ) * nf.scale := by
  have hs : nf.scale ≠ 0 := ne_of_gt nf.scale_pos
  have hscaled : g.map (Int.castRingHom ℚ) =
      C (c / nf.scale) * nf.polynomial.map (Int.castRingHom ℚ) := by
    rw [hg, nf.identity, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hs]
  have hdiv : nf.polynomial ∣ g := by
    apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
      nf.polynomial g nf.primitive).mpr
    exact ⟨C (c / nf.scale), by rw [hscaled]; ring⟩
  obtain ⟨q, hq⟩ := hdiv
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hnonzero : nf.polynomial.map (Int.castRingHom ℚ) ≠ 0 := by
    exact fun h => nf.primitive.ne_zero ((Polynomial.map_injective _ hinj) (by simpa using h))
  have hqmap : q.map (Int.castRingHom ℚ) = C (c / nf.scale) := by
    apply mul_left_cancel₀ hnonzero
    rw [← Polynomial.map_mul, ← hq, hscaled, mul_comm]
  have hdcast : ((q.coeff 0 : ℤ) : ℚ) = c / nf.scale := by
    simpa using congrArg (fun p : ℚ[X] => p.coeff 0) hqmap
  have hqconstant : q = C (q.coeff 0) := by
    apply Polynomial.map_injective (Int.castRingHom ℚ) hinj
    rw [Polynomial.map_C]
    change q.map (Int.castRingHom ℚ) = C ((q.coeff 0 : ℤ) : ℚ)
    rw [hdcast]
    exact hqmap
  refine ⟨q.coeff 0, ?_, ?_, ?_⟩
  · have hpos : (0 : ℚ) < (q.coeff 0 : ℤ) := by rw [hdcast]; exact div_pos hc nf.scale_pos
    exact_mod_cast hpos
  · calc
      g = nf.polynomial * q := hq
      _ = nf.polynomial * C (q.coeff 0) := congrArg (nf.polynomial * ·) hqconstant
      _ = C (q.coeff 0) * nf.polynomial := mul_comm _ _
  · rw [hdcast, div_mul_cancel₀ _ hs]

/-- The positive primitive scale is at most every positive integral scale. -/
theorem primitiveNormalization_scale_le {f : ℚ[X]}
    (nf : PrimitiveNormalization f) {g : ℤ[X]} {c : ℚ}
    (hc : 0 < c) (hg : g.map (Int.castRingHom ℚ) = C c * f) :
    nf.scale ≤ c := by
  obtain ⟨d, hd, _, rfl⟩ := primitiveNormalization_integer_multiple nf hc hg
  have hd1 : (1 : ℚ) ≤ d := by exact_mod_cast (show (1 : ℤ) ≤ d by omega)
  nlinarith [nf.scale_pos]

/-- At any point where the original polynomial is nonnegative, primitive
normalization is bounded by every integral positive rescaling. -/
theorem primitiveNormalization_eval_le {f : ℚ[X]}
    (nf : PrimitiveNormalization f) {g : ℤ[X]} {c : ℚ}
    (hc : 0 < c) (hg : g.map (Int.castRingHom ℚ) = C c * f)
    {x : ℝ} (hx : 0 ≤ Real.evalQ f x) :
    Real.evalQ (nf.polynomial.map (Int.castRingHom ℚ)) x ≤
      Real.evalQ (g.map (Int.castRingHom ℚ)) x := by
  have hs : (nf.scale : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast primitiveNormalization_scale_le nf hc hg
  rw [nf.identity, hg]
  simpa [Real.evalQ, Real.realPolynomial] using mul_le_mul_of_nonneg_right hs hx

/-- Absolute values also decrease, without a sign assumption on the value. -/
theorem primitiveNormalization_abs_eval_le {f : ℚ[X]}
    (nf : PrimitiveNormalization f) {g : ℤ[X]} {c : ℚ}
    (hc : 0 < c) (hg : g.map (Int.castRingHom ℚ) = C c * f) (x : ℝ) :
    |Real.evalQ (nf.polynomial.map (Int.castRingHom ℚ)) x| ≤
      |Real.evalQ (g.map (Int.castRingHom ℚ)) x| := by
  have hs : (nf.scale : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast primitiveNormalization_scale_le nf hc hg
  have hn : (0 : ℝ) ≤ (nf.scale : ℝ) := by exact_mod_cast nf.scale_pos.le
  have hc' : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc.le
  rw [nf.identity, hg]
  simp only [Real.evalQ, Real.realPolynomial, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.eval_mul, Polynomial.eval_C]
  change |(nf.scale : ℝ) * Real.evalQ f x| ≤ |(c : ℝ) * Real.evalQ f x|
  rw [abs_mul, abs_mul, abs_of_nonneg hn, abs_of_nonneg hc']
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)

/-- Compatibility of rational and direct real evaluation of an integer polynomial. -/
theorem evalQ_intMap (g : ℤ[X]) (x : ℝ) :
    Real.evalQ (g.map (Int.castRingHom ℚ)) x =
      (g.map (Int.castRingHom ℝ)).eval x := by
  simp only [Real.evalQ, Real.realPolynomial, Polynomial.map_map]
  congr 2

/-- Direct integer-polynomial evaluation form of the normalization bound. -/
theorem primitiveNormalization_abs_eval_int_le {f : ℚ[X]}
    (nf : PrimitiveNormalization f) {g : ℤ[X]} {c : ℚ}
    (hc : 0 < c) (hg : g.map (Int.castRingHom ℚ) = C c * f) (x : ℝ) :
    |(nf.polynomial.map (Int.castRingHom ℝ)).eval x| ≤
      |(g.map (Int.castRingHom ℝ)).eval x| := by
  simpa only [evalQ_intMap] using primitiveNormalization_abs_eval_le nf hc hg x

end ManuscriptChain.BasisInvariance

#print axioms ManuscriptChain.BasisInvariance.primitiveNormalization_integer_multiple
#print axioms ManuscriptChain.BasisInvariance.primitiveNormalization_scale_le

#print axioms ManuscriptChain.BasisInvariance.primitiveNormalization_eval_le

#print axioms ManuscriptChain.BasisInvariance.primitiveNormalization_abs_eval_int_le
