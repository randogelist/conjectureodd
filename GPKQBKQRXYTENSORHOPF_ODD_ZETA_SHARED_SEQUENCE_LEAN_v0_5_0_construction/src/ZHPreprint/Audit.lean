import ZHPreprint.Conjecture
import LeanPaper.AxiomWalk

/-!
Independent dependency audit for the actual-source conditional endpoint.
The audit is executable inspection, not a verified theorem about the auditor.
Passing it does not prove or erase the final theorem's explicit hypotheses.
-/

open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

#print ZHPreprint.WeightFiveIntegralSeed
#print ZHPreprint.PRIMITIVE_GROWTH_CONJECTURE
#print ZHPreprint.FiniteGramUpperBound
#check ZHPreprint.all_odd_irrational_of_integralSeed_growth_and_finiteGram
#print axioms ZHPreprint.all_odd_irrational_of_integralSeed_growth_and_finiteGram

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
    `Theorem_2_5_Weight_Change,
    `LeanPaper.AxiomWalk,
    `ZHPreprint.Algebra,
    `ZHPreprint.RawGramRate,
    `ZHPreprint.Conjecture]
  let requiredTheorems : Array Name := #[
    ``ZHPreprint.derivativeMagnitude_mono,
    ``ZHPreprint.value_upper_of_leading_gram_bounds,
    ``ZHPreprint.RawGramRate.rawGramBound_eventually_le_exp,
    ``ZHPreprint.RawGramRate.fromTwo_succ_of_finite_bounds,
    ``ZHPreprint.weightFiveSeed_of_integralSeed,
    ``ZHPreprint.rawGramSubquadratic_of_finiteBound,
    ``ZHPreprint.primitiveQuadraticDecay_of_conjecture,
    ``ZHPreprint.affineFamilyDecay_of_primitiveQuadraticDecay,
    ``ZHPreprint.irrational_of_primitiveQuadraticDecay,
    ``ZHPreprint.all_odd_irrational_of_integralSeed_growth_and_finiteGram]
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
  let result := LeanPaper.AxiomWalk.collect env roots
  match LeanPaper.AxiomWalk.check result allowed with
  | .error msg => throwError msg
  | .ok () => pure ()
  let theoremCount := roots.foldl (fun n decl => match env.find? decl with
    | some (.thmInfo _) => n + 1
    | _ => n) (0 : Nat)
  IO.println s!"AUDITED_PROJECT_MODULES={foundModules.size}"
  IO.println s!"AUDITED_PROJECT_THEOREM_DECLARATIONS={theoremCount}"
  IO.println s!"AUDITED_PROJECT_DECLARATIONS={roots.size}"
  IO.println s!"AUDITED_DEPENDENCY_DECLARATIONS={result.visited.toArray.size}"
  IO.println s!"AUDITED_AXIOMS={result.axioms.toArray.toList}"
  IO.println "AXIOM_AUDIT_METHOD=INDEPENDENT_VISITED_SET_GRAPH"
  IO.println "HYPOTHESES=ZH_WEIGHT_FIVE_SEED;PRIMITIVE_GROWTH_CONJECTURE;FINITE_GRAM_PROOF_FRONTIER;APERY"
  IO.println "UNCONDITIONAL_ALL_ODD_ZETA_IRRATIONALITY=NOT_CLAIMED"
  IO.println "AXIOM_AUDIT_ACCEPTED=ZH_PREPRINT_ACTUAL_SOURCE_CLOSURE"
