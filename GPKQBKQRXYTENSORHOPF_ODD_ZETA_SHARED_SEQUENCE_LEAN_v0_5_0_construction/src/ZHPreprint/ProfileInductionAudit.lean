import ZHPreprint.ProfileInduction
import LeanPaper.AxiomWalk

/-!
Native audit of the actual profile-induction conditional endpoints.
The product endpoint takes the actual product-base and adjacent inputs.
The height endpoint additionally takes the unformalized analytic base input.
All inputs are ordinary propositions, never installed axioms. This executable
audit walks dependencies; it is not itself a formal correctness theorem.
-/

open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

#print ZHPreprint.InductionRates.QuadraticDecay
#print ZHPreprint.InductionRates.PowerTransfer
#print ZHPreprint.ProfileInduction.baseProfile
#print ZHPreprint.ProfileInduction.delta
#print ZHPreprint.ProfileInduction.value
#print ZHPreprint.ProfileInduction.BaseHeightInput
#print ZHPreprint.ProfileInduction.AnalyticBaseInput
#print ZHPreprint.ProfileInduction.BaseProductInput
#print ZHPreprint.ProfileInduction.AdjacentInput
#print ZHPreprint.ProfileInduction.ProductInductionInput
#print ZHPreprint.ProfileInduction.HeightInductionInput
#check (ZHPreprint.ProfileInduction.all_odd_irrational_of_productInduction :
  ZHPreprint.ProfileInduction.ProductInductionInput →
  Irrational (riemannZeta (3 : ℂ)).re →
  ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re)
#check (ZHPreprint.ProfileInduction.all_odd_irrational_of_heightInduction :
  ZHPreprint.ProfileInduction.HeightInductionInput →
  ZHPreprint.ProfileInduction.AnalyticBaseInput →
  Irrational (riemannZeta (3 : ℂ)).re →
  ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re)
#print axioms ZHPreprint.ProfileInduction.all_odd_irrational_of_productInduction
#print axioms ZHPreprint.ProfileInduction.all_odd_irrational_of_heightInduction

run_cmd Elab.Command.liftCoreM do
  let env := (← getEnv).setExporting false
  let allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let projectModules : Array Name := #[
    `Definition_2_1_Order_s_Rational_Moment_Functional,
    `Theorem_2_4_Canonical_Basis_Invariance,
    `Theorem_2_5_Lagrange_Pole_Diagonalization,
    `Theorem_3_1_Universal_Hyperbolicity_And_Zero_Free_Disk,
    `Theorem_3_1_General_Odd_Weight_Endpoint,
    `Theorem_3_1_Positive_Moment_Realization,
    `Theorem_4_1_Spectral_Irrationality_Measure_Criterion,
    `MAIN_CHAIN,
    `Theorem_3_1_Hyperbolic_Weight,
    `Theorem_3_1_Hyperbolic_Moments,
    `Zetahyperbolic.CoreLinearAlgebra,
    `Zetahyperbolic.Foundations,
    `Zetahyperbolic.Section3Elementary,
    `Zetahyperbolic.Section2Checked,
    `Zetahyperbolic.ManuscriptCompatibility,
    `Theorem_3_1_Concrete_Moment_Realization,
    `Theorem_3_1_Rational_Integral_Bridge,
    `ANALYTIC_FRONTIER,
    `Zetahyperbolic.MainChain,
    `Zetahyperbolic.AnalyticMainChain,
    `Theorem_3_1_Pole_Scaling,
    `Theorem_3_1_Coth_Partial_Fractions,
    `Theorem_3_1_Zeta_Tail,
    `Theorem_3_1_Bose_Tail_Integral,
    `Theorem_3_1_Pole_Integral_Identity,
    `MAIN_CHAIN_ASSEMBLED,
    `Theorem_4_1_Direct_Irrationality_From_Decay,
    `Theorem_2_4_Primitive_Normalization_Minimality,
    `MAIN_CHAIN_IRRATIONALITY,
    `Theorem_4_1_Leading_Coefficient_Gap,
    `LeanPaper.AxiomWalk,
    `ZHPreprint.WeightDependentConjecture,
    `ZHPreprint.InductionRates,
    `ZHPreprint.ProfileInduction]
  let requiredTheorems : Array Name := #[
    ``ZHPreprint.InductionRates.time_pos,
    ``ZHPreprint.InductionRates.quadraticDecay_of_powerTransfer,
    ``ZHPreprint.InductionRates.fromTwo_of_adjacent,
    ``ZHPreprint.InductionRates.product_quadraticDecay,
    ``ZHPreprint.ProfileInduction.Profile.atWeight_admissible,
    ``ZHPreprint.ProfileInduction.Profile.primitive_degree,
    ``ZHPreprint.ProfileInduction.value_pos,
    ``ZHPreprint.ProfileInduction.primitive_eval_eq_value,
    ``ZHPreprint.ProfileInduction.normalizedDecay_of_quadraticDecay,
    ``ZHPreprint.ProfileInduction.irrational_of_quadraticDecay,
    ``ZHPreprint.ProfileInduction.baseProduct_of_height_and_analytic,
    ``ZHPreprint.ProfileInduction.quadraticDecay_all_of_base_and_adjacent,
    ``ZHPreprint.ProfileInduction.all_odd_ge_five_of_base_and_adjacent,
    ``ZHPreprint.ProfileInduction.all_odd_irrational_of_productInduction,
    ``ZHPreprint.ProfileInduction.productInduction_of_heightInduction,
    ``ZHPreprint.ProfileInduction.all_odd_irrational_of_heightInduction]
  let mut roots : Array Name := #[]
  let mut foundModules : Array Name := #[]
  for (decl, _) in env.constants do
    if let some idx := env.getModuleIdxFor? decl then
      let modName := env.header.moduleNames[idx.toNat]!
      if projectModules.contains modName then
        roots := roots.push decl
        if !foundModules.contains modName then
          foundModules := foundModules.push modName
  if roots.isEmpty then
    throwError "EMPTY_PROJECT_AUDIT"
  for modName in projectModules do
    if !foundModules.contains modName then
      throwError "UNINSPECTED_PROJECT_MODULE {modName}"
  for decl in requiredTheorems do
    if !roots.contains decl then
      throwError "REQUIRED_ENDPOINT_NOT_IN_AUDIT {decl}"
    match env.find? decl with
    | some (.thmInfo _) => pure ()
    | _ => throwError "REQUIRED_ENDPOINT_NOT_A_THEOREM {decl}"
  let inputDefinitions : Array Name := #[
    ``ZHPreprint.ProfileInduction.BaseHeightInput,
    ``ZHPreprint.ProfileInduction.AnalyticBaseInput,
    ``ZHPreprint.ProfileInduction.BaseProductInput,
    ``ZHPreprint.ProfileInduction.AdjacentInput,
    ``ZHPreprint.ProfileInduction.ProductInductionInput,
    ``ZHPreprint.ProfileInduction.HeightInductionInput]
  for decl in inputDefinitions do
    match env.find? decl with
    | some (.defnInfo _) => pure ()
    | _ => throwError "INPUT_MUST_BE_A_DEFINITION_NOT_AN_AXIOM {decl}"
  let result := LeanPaper.AxiomWalk.collect env roots
  match LeanPaper.AxiomWalk.check result allowed with
  | .error msg => throwError msg
  | .ok () => pure ()
  let productEndpoint := LeanPaper.AxiomWalk.collect env
    #[``ZHPreprint.ProfileInduction.all_odd_irrational_of_productInduction]
  let heightEndpoint := LeanPaper.AxiomWalk.collect env
    #[``ZHPreprint.ProfileInduction.all_odd_irrational_of_heightInduction]
  let forbidden : Array Name := #[
    `ZHPreprint.WeightFiveIntegralSeed,
    `ZHPreprint.WeightFiveSeed,
    `ZHPreprint.PRIMITIVE_GROWTH_CONJECTURE,
    `ZHPreprint.FiniteGramUpperBound,
    `ZHPreprint.RawGramSubquadratic,
    `ZHPreprint.WeightDependent.WEIGHT_DEPENDENT_GAP_CONJECTURE]
  for decl in forbidden do
    if productEndpoint.visited.contains decl || heightEndpoint.visited.contains decl then
      throwError "SUPERSEDED_PREMISE_IN_NEW_ENDPOINT {decl}"
  if productEndpoint.visited.contains ``ZHPreprint.ProfileInduction.AnalyticBaseInput then
    throwError "UNEXPECTED_ANALYTIC_PREMISE_IN_PRODUCT_ENDPOINT"
  if !heightEndpoint.visited.contains ``ZHPreprint.ProfileInduction.AnalyticBaseInput then
    throwError "HEIGHT_ENDPOINT_ANALYTIC_PREMISE_NOT_VISIBLE"
  for decl in #[``ZHPreprint.ProfileInduction.BaseProductInput,
      ``ZHPreprint.ProfileInduction.AdjacentInput,
      ``ManuscriptChain.GeneralIrrationality.primitivePolynomial] do
    if !productEndpoint.visited.contains decl then
      throwError "PRODUCT_ENDPOINT_REQUIRED_DEPENDENCY_MISSING {decl}"
  let theoremCount := roots.foldl (fun n decl => match env.find? decl with
    | some (.thmInfo _) => n + 1
    | _ => n) (0 : Nat)
  IO.println s!"AUDITED_PROJECT_MODULES={foundModules.size}"
  IO.println s!"AUDITED_PROJECT_THEOREM_DECLARATIONS={theoremCount}"
  IO.println s!"AUDITED_PROJECT_DECLARATIONS={roots.size}"
  IO.println s!"AUDITED_DEPENDENCY_DECLARATIONS={result.visited.toArray.size}"
  IO.println s!"AUDITED_AXIOMS={result.axioms.toArray.toList}"
  IO.println "AXIOM_AUDIT_METHOD=INDEPENDENT_VISITED_SET_GRAPH"
  IO.println "PRODUCT_ENDPOINT_HYPOTHESES=ACTUAL_PRODUCT_BASE;ACTUAL_ADJACENT_POWER_TRANSFER;APERY"
  IO.println "HEIGHT_ENDPOINT_HYPOTHESES=ACTUAL_HEIGHT_BASE;ACTUAL_ADJACENT_POWER_TRANSFER;EXPLICIT_ANALYTIC_BASE;APERY"
  IO.println "ANALYTIC_BASE_FORMALIZATION=OPEN_EXPLICIT_INPUT"
  IO.println "BASE_HEIGHT_ESTIMATE=OPEN_EXPLICIT_INPUT"
  IO.println "ACTUAL_ADJACENT_PRODUCT_ESTIMATE=OPEN_EXPLICIT_INPUT"
  IO.println "SUPERSEDED_CONJECTURES=ABSENT_FROM_NEW_ENDPOINT_DEPENDENCIES"
  IO.println "SUCCESSFUL_PROFILE_WITNESSES_CONSTRUCTED=NO"
  IO.println "UNCONDITIONAL_ALL_ODD_ZETA_IRRATIONALITY=NOT_CLAIMED"
  IO.println "AXIOM_AUDIT_ACCEPTED=ZH_PROFILE_INDUCTION_CLOSURE"
