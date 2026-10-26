import ZHPreprint.ProfileInduction
import ZHPreprint.RouterAlgebra

/-!
# Evidence routes through the actual ZH derivations

A route contains proofs of its leaf estimates. It does not search for those
proofs, turn a numerical label into evidence, or assert that a successful
route exists. Every node uses an actual positive-weight ZH profile and the
existing canonical primitive normalization.

The decay routes accept a product estimate, a separated profile gap, or the
weight-five height estimate together with the explicit analytic base input.
Transfer routes accept a product comparison, matched-power factor estimates,
or a finite composition through actual intermediate nodes. The same paper
index t=n+1 is preserved at every edge; no unproved subsequence change occurs.

The paper-only exclusion tests and analytic estimates are not installed as
Lean facts by this file. Native compilation and the independent audit remain
pending. No Lean process was run on the authoring host.
-/

noncomputable section

namespace ZHPreprint.DerivationRouter

/-- A positive odd-weight index and an actual admissible fixed geometry. -/
structure Node where
  k : ℕ
  hk : 0 < k
  profile : ProfileInduction.Profile

/-- Make the weight index and its positivity explicit at route boundaries. -/
def node (k : ℕ) (hk : 0 < k) (p : ProfileInduction.Profile) : Node :=
  ⟨k, hk, p⟩

def Node.leading (x : Node) : ℕ → ℝ :=
  ProfileInduction.leading x.profile x.k

def Node.ratio (x : Node) : ℕ → ℝ :=
  ProfileInduction.ratio x.profile x.k

def Node.value (x : Node) : ℕ → ℝ :=
  ProfileInduction.value x.profile x.k

theorem Node.leading_nonneg (x : Node) (n : ℕ) : 0 ≤ x.leading n :=
  ProfileInduction.leading_nonneg x.profile x.k n

theorem Node.ratio_nonneg (x : Node) (n : ℕ) : 0 ≤ x.ratio n :=
  (ProfileInduction.ratio_pos x.profile x.k x.hk n).le

theorem Node.value_pos (x : Node) (n : ℕ) : 0 < x.value n :=
  ProfileInduction.value_pos x.profile x.k x.hk n

theorem Node.value_nonneg (x : Node) (n : ℕ) : 0 ≤ x.value n :=
  (x.value_pos n).le

/-- These alternatives require actual proofs, including the analytic input
on the height route. No constructor takes only a route name or status flag. -/
inductive DecayRoute (x : Node) : Prop where
  | product (h : InductionRates.QuadraticDecay x.value) : DecayRoute x
  | separatedGap
      (h : WeightDependent.ProfileGap x.k x.profile.m x.profile.a x.profile.b) :
      DecayRoute x
  | height
      (hweight : x.k = 2)
      (hprofile : x.profile = ProfileInduction.baseProfile)
      (hheight : ProfileInduction.BaseHeightInput)
      (hanalytic : ProfileInduction.AnalyticBaseInput) : DecayRoute x

/-- Every accepted decay route yields the actual quadratic product estimate. -/
theorem DecayRoute.sound {x : Node} (route : DecayRoute x) :
    InductionRates.QuadraticDecay x.value := by
  cases route with
  | product h => exact h
  | separatedGap h =>
    obtain ⟨A, B, _hA, hAB, N, hbounds⟩ := h
    change InductionRates.QuadraticDecay (fun n => x.leading n * x.ratio n)
    apply RouterAlgebra.quadraticDecay_of_separatedBounds
      (fun n => x.leading_nonneg n) hAB
    · exact ⟨N, fun n hn => (hbounds n hn).1⟩
    · exact ⟨N, fun n hn => (hbounds n hn).2⟩
  | height hweight hprofile hheight hanalytic =>
    have hbase := ProfileInduction.baseProduct_of_height_and_analytic
      (fun _ => ProfileInduction.baseProfile) rfl hheight hanalytic
    change InductionRates.QuadraticDecay
      (ProfileInduction.value x.profile x.k)
    rw [hprofile, hweight]
    exact hbase

theorem irrational_of_decayRoute (x : Node) (route : DecayRoute x) :
    Irrational (riemannZeta ((2 * x.k + 1 : ℕ) : ℂ)).re :=
  ProfileInduction.irrational_of_quadraticDecay x.profile x.k x.hk route.sound

/-- A finite route can cross weights, change geometry, or compose both.
Every edge compares the same t=n+1 index, and every leaf is an actual estimate. -/
inductive TransferRoute : Node → Node → Prop where
  | direct {s d : Node}
      (h : InductionRates.PowerTransfer s.value d.value) : TransferRoute s d
  | paired {s d : Node}
      (h : RouterAlgebra.PairedPowerTransfer s.leading s.ratio d.leading d.ratio) :
      TransferRoute s d
  | compose {s mid d : Node}
      (left : TransferRoute s mid) (right : TransferRoute mid d) : TransferRoute s d

/-- Composition preserves a positive exponent and only linear logarithmic loss. -/
theorem TransferRoute.sound {s d : Node} (route : TransferRoute s d) :
    InductionRates.PowerTransfer s.value d.value := by
  induction route with
  | direct h => exact h
  | @paired s d h =>
    exact RouterAlgebra.powerTransfer_of_paired
      (fun n => s.leading_nonneg n) (fun n => s.ratio_nonneg n)
      (fun n => d.leading_nonneg n) (fun n => d.ratio_nonneg n) h
  | @compose s mid d _left _right ihLeft ihRight =>
    exact RouterAlgebra.powerTransfer_trans
      (fun n => s.value_nonneg n) (fun n => mid.value_nonneg n) ihLeft ihRight

/-- Transport an actual successful estimate along an accepted finite route. -/
theorem quadraticDecay_of_routes {s d : Node}
    (hbase : DecayRoute s) (htransfer : TransferRoute s d) :
    InductionRates.QuadraticDecay d.value :=
  InductionRates.quadraticDecay_of_powerTransfer
    (fun n => s.value_nonneg n) hbase.sound htransfer.sound

theorem irrational_of_routes {s d : Node}
    (hbase : DecayRoute s) (htransfer : TransferRoute s d) :
    Irrational (riemannZeta ((2 * d.k + 1 : ℕ) : ℂ)).re :=
  ProfileInduction.irrational_of_quadraticDecay d.profile d.k d.hk
    (quadraticDecay_of_routes hbase htransfer)

/-- A separate accepted decay route may be supplied at each fixed weight. -/
def PerWeightRoutes : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ p : ProfileInduction.Profile,
    DecayRoute (node k (by omega) p)

/-- The previously fixed weight-five base and adjacent actual routes.
This is an input proposition; a successful family is not constructed here. -/
def InductionRoutes : Prop :=
  ∃ P : ℕ → ProfileInduction.Profile,
    P 2 = ProfileInduction.baseProfile ∧
    DecayRoute (node 2 (by decide) (P 2)) ∧
    ∀ (k : ℕ) (hk : 2 ≤ k),
      TransferRoute (node k (by omega) (P k))
        (node (k + 1) (by omega) (P (k + 1)))

theorem all_odd_ge_five_of_perWeightRoutes (h : PerWeightRoutes) :
    ∀ k : ℕ, 2 ≤ k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  obtain ⟨p, hp⟩ := h k hk
  exact irrational_of_decayRoute (node k (by omega) p) hp

/-- The router feeds the already established actual-profile induction interface. -/
theorem productInductionInput_of_inductionRoutes (h : InductionRoutes) :
    ProfileInduction.ProductInductionInput := by
  obtain ⟨P, hprofile, hbase, hstep⟩ := h
  refine ⟨P, hprofile, ?_, ?_⟩
  · exact hbase.sound
  · intro k hk
    exact (hstep k hk).sound

theorem all_odd_ge_five_of_inductionRoutes (h : InductionRoutes) :
    ∀ k : ℕ, 2 ≤ k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re :=
  ProfileInduction.all_odd_ge_five_of_productInduction
    (productInductionInput_of_inductionRoutes h)

/-- Global routing alternatives. Both constructors still require all leaf proofs. -/
inductive AllOddRoute : Prop where
  | perWeight (h : PerWeightRoutes) : AllOddRoute
  | byInduction (h : InductionRoutes) : AllOddRoute

theorem all_odd_ge_five_of_route (h : AllOddRoute) :
    ∀ k : ℕ, 2 ≤ k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  cases h with
  | perWeight h => exact all_odd_ge_five_of_perWeightRoutes h
  | byInduction h => exact all_odd_ge_five_of_inductionRoutes h

/-- The final router endpoint, with the separate weight-three theorem explicit.
No accepted route or new irrationality witness is asserted by this theorem. -/
theorem all_odd_irrational_of_route (h : AllOddRoute)
    (hapery : Irrational (riemannZeta (3 : ℂ)).re) :
    ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re := by
  intro k hk
  by_cases hone : k = 1
  · subst k
    simpa using hapery
  · exact all_odd_ge_five_of_route h k (by omega)

end ZHPreprint.DerivationRouter

#print axioms ZHPreprint.DerivationRouter.DecayRoute.sound
#print axioms ZHPreprint.DerivationRouter.TransferRoute.sound
#print axioms ZHPreprint.DerivationRouter.quadraticDecay_of_routes
#print axioms ZHPreprint.DerivationRouter.irrational_of_routes
#print axioms ZHPreprint.DerivationRouter.productInductionInput_of_inductionRoutes
#print axioms ZHPreprint.DerivationRouter.all_odd_irrational_of_route
