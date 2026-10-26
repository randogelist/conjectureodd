import ZHPreprint.WeightDependentConjecture
import LeanPaper.AxiomWalk

/-!
Native audit of the actual weight-dependent conditional endpoint.
The conjecture remains an explicit hypothesis, never an installed axiom.
This audit walks proof/type dependencies and checks the endpoint does not
depend on the superseded fixed-profile premises. It is executable inspection,
not a formal theorem asserting the correctness of the audit program.
-/

open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

#print ZHPreprint.WeightDependent.profile
#print ZHPreprint.WeightDependent.ProfileGap
#print ZHPreprint.WeightDependent.WEIGHT_DEPENDENT_GAP_CONJECTURE
#check (ZHPreprint.WeightDependent.all_odd_irrational_of_weightDependentGap :
  ZHPreprint.WeightDependent.WEIGHT_DEPENDENT_GAP_CONJECTURE →
  Irrational (riemannZeta (3 : ℂ)).re →
  ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re)
#print axioms ZHPreprint.WeightDependent.all_odd_irrational_of_weightDependentGap

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
    `ZHPreprint.WeightDependentConjecture]
  let requiredTheorems : Array Name := #[
    ``ZHPreprint.WeightDependent.profile_admissible,
    ``ZHPreprint.WeightDependent.profile_primitive_degree,
    ``ZHPreprint.WeightDependent.profile_unbounded,
    ``ZHPreprint.WeightDependent.profile_ratio_pos,
    ``ZHPreprint.WeightDependent.rate_rescale,
    ``ZHPreprint.WeightDependent.irrational_riemannZeta_of_profileGap,
    ``ZHPreprint.WeightDependent.all_odd_ge_five_of_weightDependentGap,
    ``ZHPreprint.WeightDependent.all_odd_irrational_of_weightDependentGap]
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
  match env.find? ``ZHPreprint.WeightDependent.WEIGHT_DEPENDENT_GAP_CONJECTURE with
  | some (.defnInfo _) => pure ()
  | _ => throwError "CONJECTURE_MUST_BE_A_DEFINITION_NOT_AN_AXIOM"
  let result := LeanPaper.AxiomWalk.collect env roots
  match LeanPaper.AxiomWalk.check result allowed with
  | .error msg => throwError msg
  | .ok () => pure ()
  let endpoint := LeanPaper.AxiomWalk.collect env
    #[``ZHPreprint.WeightDependent.all_odd_irrational_of_weightDependentGap]
  let forbidden : Array Name := #[
    `ZHPreprint.WeightFiveIntegralSeed,
    `ZHPreprint.WeightFiveSeed,
    `ZHPreprint.PRIMITIVE_GROWTH_CONJECTURE,
    `ZHPreprint.FiniteGramUpperBound,
    `ZHPreprint.RawGramSubquadratic]
  for decl in forbidden do
    if endpoint.visited.contains decl then
      throwError "SUPERSEDED_PREMISE_IN_NEW_ENDPOINT {decl}"
  let theoremCount := roots.foldl (fun n decl => match env.find? decl with
    | some (.thmInfo _) => n + 1
    | _ => n) (0 : Nat)
  IO.println s!"AUDITED_PROJECT_MODULES={foundModules.size}"
  IO.println s!"AUDITED_PROJECT_THEOREM_DECLARATIONS={theoremCount}"
  IO.println s!"AUDITED_PROJECT_DECLARATIONS={roots.size}"
  IO.println s!"AUDITED_DEPENDENCY_DECLARATIONS={result.visited.toArray.size}"
  IO.println s!"AUDITED_AXIOMS={result.axioms.toArray.toList}"
  IO.println "AXIOM_AUDIT_METHOD=INDEPENDENT_VISITED_SET_GRAPH"
  IO.println "HYPOTHESES=WEIGHT_DEPENDENT_GAP_CONJECTURE;APERY"
  IO.println "SUPERSEDED_FIXED_PROFILE_PREMISES=ABSENT_FROM_NEW_ENDPOINT_DEPENDENCIES"
  IO.println "CONJECTURE_PROVED=NO"
  IO.println "SUCCESSFUL_WEIGHT_DEPENDENT_PROFILES_CONSTRUCTED=NO"
  IO.println "UNCONDITIONAL_ALL_ODD_ZETA_IRRATIONALITY=NOT_CLAIMED"
  IO.println "AXIOM_AUDIT_ACCEPTED=ZH_WEIGHT_DEPENDENT_GAP_CLOSURE"
