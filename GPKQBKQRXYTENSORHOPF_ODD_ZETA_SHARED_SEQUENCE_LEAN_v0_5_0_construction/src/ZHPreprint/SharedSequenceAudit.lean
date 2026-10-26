import ZHPreprint.SharedSequence
import LeanPaper.AxiomWalk

/-!
Native dependency audit of the shared-sequence conditional endpoint.
The base estimate and adjacent sampled comparisons remain explicit inputs.
The conclusion concerns actual primitive polynomial values and Mathlib zeta.
No successful sequence is asserted, and no quadratic-decay premise is used.
This is executable dependency inspection, not a proof of its own correctness.
-/

open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

#print ZHPreprint.SequenceRates.RateEnvelope
#print ZHPreprint.SequenceRates.SamplePowerTransfer
#print ZHPreprint.SharedSequence.BaseInput
#print ZHPreprint.SharedSequence.AdjacentInput
#print ZHPreprint.SharedSequence.SharedSequenceInput
#print ZHPreprint.SharedSequence.all_logarithmic_rates_of_sharedSequence
#check (ZHPreprint.SharedSequence.all_odd_irrational_of_sharedSequence :
  ZHPreprint.SharedSequence.SharedSequenceInput →
  Irrational (riemannZeta (3 : ℂ)).re →
  ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re)
#print axioms ZHPreprint.SequenceRates.tendsto_neg_log_div_atTop
#print axioms ZHPreprint.SharedSequence.irrational_of_rateEnvelope
#print axioms ZHPreprint.SharedSequence.all_logarithmic_rates_of_sharedSequence
#print axioms ZHPreprint.SharedSequence.all_odd_irrational_of_sharedSequence

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
    `ZHPreprint.ProfileInduction,
    `ZHPreprint.RouterAlgebra,
    `ZHPreprint.DerivationRouter,
    `ZHPreprint.SequenceRates,
    `ZHPreprint.SharedSequence]
  let requiredTheorems : Array Name := #[
    ``ZHPreprint.SequenceRates.rateEnvelope_of_base,
    ``ZHPreprint.SequenceRates.rateEnvelope_of_powerTransfer,
    ``ZHPreprint.SequenceRates.fromTwo_of_adjacent,
    ``ZHPreprint.SequenceRates.eventually_exp_bound,
    ``ZHPreprint.SequenceRates.tendsto_neg_log_div_atTop,
    ``ZHPreprint.SharedSequence.sampledTime_pos,
    ``ZHPreprint.SharedSequence.sampledValue_pos,
    ``ZHPreprint.SharedSequence.sampled_eval_eq_value,
    ``ZHPreprint.SharedSequence.irrational_of_rateEnvelope,
    ``ZHPreprint.SharedSequence.rateEnvelope_all_of_base_and_adjacent,
    ``ZHPreprint.SharedSequence.tendsto_neg_log_div_of_rateEnvelope,
    ``ZHPreprint.SharedSequence.all_logarithmic_rates_of_sharedSequence,
    ``ZHPreprint.SharedSequence.all_odd_ge_five_of_sharedSequence,
    ``ZHPreprint.SharedSequence.all_odd_irrational_of_sharedSequence]
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
    ``ZHPreprint.SequenceRates.RateEnvelope,
    ``ZHPreprint.SequenceRates.SamplePowerTransfer,
    ``ZHPreprint.SharedSequence.BaseInput,
    ``ZHPreprint.SharedSequence.AdjacentInput,
    ``ZHPreprint.SharedSequence.SharedSequenceInput]
  for decl in inputDefinitions do
    match env.find? decl with
    | some (.defnInfo _) => pure ()
    | _ => throwError "INPUT_MUST_BE_A_DEFINITION_NOT_AN_AXIOM {decl}"
  let result := LeanPaper.AxiomWalk.collect env roots
  match LeanPaper.AxiomWalk.check result allowed with
  | .error msg => throwError msg
  | .ok () => pure ()
  let endpoint := LeanPaper.AxiomWalk.collect env
    #[``ZHPreprint.SharedSequence.all_odd_irrational_of_sharedSequence]
  let forbidden : Array Name := #[
    `ZHPreprint.WeightFiveIntegralSeed,
    `ZHPreprint.WeightFiveSeed,
    `ZHPreprint.PRIMITIVE_GROWTH_CONJECTURE,
    `ZHPreprint.FiniteGramUpperBound,
    `ZHPreprint.RawGramSubquadratic,
    `ZHPreprint.WeightDependent.WEIGHT_DEPENDENT_GAP_CONJECTURE,
    ``ZHPreprint.InductionRates.QuadraticDecay,
    ``ZHPreprint.ProfileInduction.AnalyticBaseInput,
    ``ZHPreprint.ProfileInduction.BaseHeightInput,
    ``ZHPreprint.ProfileInduction.ProductInductionInput,
    ``ZHPreprint.ProfileInduction.HeightInductionInput,
    ``ZHPreprint.DerivationRouter.AllOddRoute]
  for decl in forbidden do
    if endpoint.visited.contains decl then
      throwError "STRONGER_OR_SUPERSEDED_PREMISE_IN_SEQUENCE_ENDPOINT {decl}"
  for decl in #[``ZHPreprint.SharedSequence.SharedSequenceInput,
      ``ZHPreprint.SharedSequence.BaseInput,
      ``ZHPreprint.SharedSequence.AdjacentInput,
      ``ZHPreprint.SequenceRates.SamplePowerTransfer,
      ``ZHPreprint.SequenceRates.RateEnvelope,
      ``ManuscriptChain.GeneralIrrationality.primitivePolynomial,
      ``ManuscriptChain.RealTransfer.irrational_of_decay_and_denominator_budget] do
    if !endpoint.visited.contains decl then
      throwError "SEQUENCE_REQUIRED_DEPENDENCY_MISSING {decl}"
  let invariant := LeanPaper.AxiomWalk.collect env
    #[``ZHPreprint.SharedSequence.all_logarithmic_rates_of_sharedSequence]
  for decl in #[``ZHPreprint.SharedSequence.SharedSequenceInput,
      ``ZHPreprint.SequenceRates.tendsto_neg_log_div_atTop] do
    if !invariant.visited.contains decl then
      throwError "LOGARITHMIC_INVARIANT_DEPENDENCY_MISSING {decl}"
  let theoremCount := roots.foldl (fun n decl => match env.find? decl with
    | some (.thmInfo _) => n + 1
    | _ => n) (0 : Nat)
  IO.println s!"AUDITED_PROJECT_MODULES={foundModules.size}"
  IO.println s!"AUDITED_PROJECT_THEOREM_DECLARATIONS={theoremCount}"
  IO.println s!"AUDITED_PROJECT_DECLARATIONS={roots.size}"
  IO.println s!"AUDITED_DEPENDENCY_DECLARATIONS={result.visited.toArray.size}"
  IO.println s!"AUDITED_AXIOMS={result.axioms.toArray.toList}"
  IO.println "AXIOM_AUDIT_METHOD=INDEPENDENT_VISITED_SET_GRAPH"
  IO.println "SEQUENCE_ENDPOINT_HYPOTHESES=SHARED_SEQUENCE_INPUT;APERY"
  IO.println "BASE_SAMPLE_BOUND=EXPLICIT_INPUT"
  IO.println "ADJACENT_SAMPLE_TRANSFERS=EXPLICIT_INPUT"
  IO.println "SAMPLING=ONE_COMMON_STRICTLY_INCREASING_MAP"
  IO.println "PAPER_SAMPLE_TIME=SIGMA_J_PLUS_ONE"
  IO.println "PAPER_STRENGTH_INDEX=J_PLUS_ONE"
  IO.println "LOGARITHMIC_INVARIANT=EXACT_TENDSTO_ATTOP"
  IO.println "DENOMINATOR_BRIDGE=ACTUAL_PRIMITIVE_POLYNOMIAL"
  IO.println "QUADRATIC_DECAY_PREMISE=ABSENT_FROM_ENDPOINT"
  IO.println "SEQUENCE_TO_QUADRATIC_OR_SEPARATED_GAP=NOT_CLAIMED"
  IO.println "SUCCESSFUL_SEQUENCE_WITNESS_CONSTRUCTED=NO"
  IO.println "UNCONDITIONAL_ALL_ODD_ZETA_IRRATIONALITY=NOT_CLAIMED"
  IO.println "AXIOM_AUDIT_ACCEPTED=ZH_SHARED_SEQUENCE_CLOSURE"
