import ZHPreprint.DerivationRouter
import LeanPaper.AxiomWalk

/-!
Native dependency audit of the conditional derivation router.
Route constructors require proofs of actual estimates. The height constructor
explicitly requires the analytic base input. The global router has multiple
branches, so reaching that name in its dependency graph does not assert a
global analytic hypothesis or supply its proof. No route witness is supplied.
This audit is executable inspection, not a theorem about its own correctness.
-/

open Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

#print ZHPreprint.RouterAlgebra.PairedPowerTransfer
#print ZHPreprint.DerivationRouter.Node
#print ZHPreprint.DerivationRouter.DecayRoute
#print ZHPreprint.DerivationRouter.DecayRoute.height
#print ZHPreprint.DerivationRouter.TransferRoute
#print ZHPreprint.DerivationRouter.PerWeightRoutes
#print ZHPreprint.DerivationRouter.InductionRoutes
#print ZHPreprint.DerivationRouter.AllOddRoute
#check (ZHPreprint.DerivationRouter.all_odd_irrational_of_route :
  ZHPreprint.DerivationRouter.AllOddRoute →
  Irrational (riemannZeta (3 : ℂ)).re →
  ∀ k : ℕ, 0 < k → Irrational (riemannZeta ((2 * k + 1 : ℕ) : ℂ)).re)
#check (@ZHPreprint.DerivationRouter.DecayRoute.height :
  ∀ x : ZHPreprint.DerivationRouter.Node,
    x.k = 2 → x.profile = ZHPreprint.ProfileInduction.baseProfile →
    ZHPreprint.ProfileInduction.BaseHeightInput →
    ZHPreprint.ProfileInduction.AnalyticBaseInput →
    ZHPreprint.DerivationRouter.DecayRoute x)
#print axioms ZHPreprint.DerivationRouter.DecayRoute.sound
#print axioms ZHPreprint.DerivationRouter.TransferRoute.sound
#print axioms ZHPreprint.DerivationRouter.all_odd_irrational_of_route

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
    `ZHPreprint.DerivationRouter]
  let requiredTheorems : Array Name := #[
    ``ZHPreprint.RouterAlgebra.quadraticDecay_of_separatedBounds,
    ``ZHPreprint.RouterAlgebra.powerTransfer_of_paired,
    ``ZHPreprint.RouterAlgebra.powerTransfer_trans,
    ``ZHPreprint.DerivationRouter.Node.value_pos,
    ``ZHPreprint.DerivationRouter.DecayRoute.sound,
    ``ZHPreprint.DerivationRouter.TransferRoute.sound,
    ``ZHPreprint.DerivationRouter.irrational_of_decayRoute,
    ``ZHPreprint.DerivationRouter.quadraticDecay_of_routes,
    ``ZHPreprint.DerivationRouter.irrational_of_routes,
    ``ZHPreprint.DerivationRouter.all_odd_ge_five_of_perWeightRoutes,
    ``ZHPreprint.DerivationRouter.productInductionInput_of_inductionRoutes,
    ``ZHPreprint.DerivationRouter.all_odd_ge_five_of_inductionRoutes,
    ``ZHPreprint.DerivationRouter.all_odd_ge_five_of_route,
    ``ZHPreprint.DerivationRouter.all_odd_irrational_of_route]
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
    ``ZHPreprint.RouterAlgebra.PairedPowerTransfer,
    ``ZHPreprint.ProfileInduction.AnalyticBaseInput,
    ``ZHPreprint.DerivationRouter.PerWeightRoutes,
    ``ZHPreprint.DerivationRouter.InductionRoutes]
  for decl in inputDefinitions do
    match env.find? decl with
    | some (.defnInfo _) => pure ()
    | _ => throwError "INPUT_MUST_BE_A_DEFINITION_NOT_AN_AXIOM {decl}"
  for decl in #[``ZHPreprint.DerivationRouter.DecayRoute,
      ``ZHPreprint.DerivationRouter.TransferRoute,
      ``ZHPreprint.DerivationRouter.AllOddRoute] do
    match env.find? decl with
    | some (.inductInfo _) => pure ()
    | _ => throwError "ROUTE_MUST_BE_AN_INDUCTIVE_NOT_AN_AXIOM {decl}"
  let result := LeanPaper.AxiomWalk.collect env roots
  match LeanPaper.AxiomWalk.check result allowed with
  | .error msg => throwError msg
  | .ok () => pure ()
  let endpoint := LeanPaper.AxiomWalk.collect env
    #[``ZHPreprint.DerivationRouter.all_odd_irrational_of_route]
  let forbidden : Array Name := #[
    `ZHPreprint.WeightFiveIntegralSeed,
    `ZHPreprint.WeightFiveSeed,
    `ZHPreprint.PRIMITIVE_GROWTH_CONJECTURE,
    `ZHPreprint.FiniteGramUpperBound,
    `ZHPreprint.RawGramSubquadratic,
    `ZHPreprint.WeightDependent.WEIGHT_DEPENDENT_GAP_CONJECTURE]
  for decl in forbidden do
    if endpoint.visited.contains decl then
      throwError "SUPERSEDED_PREMISE_IN_ROUTER_ENDPOINT {decl}"
  for decl in #[``ZHPreprint.DerivationRouter.AllOddRoute,
      ``ZHPreprint.DerivationRouter.DecayRoute,
      ``ZHPreprint.DerivationRouter.TransferRoute,
      ``ManuscriptChain.GeneralIrrationality.primitivePolynomial] do
    if !endpoint.visited.contains decl then
      throwError "ROUTER_REQUIRED_DEPENDENCY_MISSING {decl}"
  let heightConstructor := LeanPaper.AxiomWalk.collect env
    #[``ZHPreprint.DerivationRouter.DecayRoute.height]
  for decl in #[``ZHPreprint.ProfileInduction.BaseHeightInput,
      ``ZHPreprint.ProfileInduction.AnalyticBaseInput] do
    if !heightConstructor.visited.contains decl then
      throwError "HEIGHT_ROUTE_REQUIRED_INPUT_MISSING {decl}"
  let theoremCount := roots.foldl (fun n decl => match env.find? decl with
    | some (.thmInfo _) => n + 1
    | _ => n) (0 : Nat)
  IO.println s!"AUDITED_PROJECT_MODULES={foundModules.size}"
  IO.println s!"AUDITED_PROJECT_THEOREM_DECLARATIONS={theoremCount}"
  IO.println s!"AUDITED_PROJECT_DECLARATIONS={roots.size}"
  IO.println s!"AUDITED_DEPENDENCY_DECLARATIONS={result.visited.toArray.size}"
  IO.println s!"AUDITED_AXIOMS={result.axioms.toArray.toList}"
  IO.println "AXIOM_AUDIT_METHOD=INDEPENDENT_VISITED_SET_GRAPH"
  IO.println "ROUTER_ENDPOINT_HYPOTHESES=ACCEPTED_ACTUAL_ROUTE;APERY"
  IO.println "ROUTER_DECAY_BRANCHES=PRODUCT;SEPARATED_GAP;HEIGHT_WITH_ANALYTIC_INPUT"
  IO.println "ROUTER_TRANSFER_BRANCHES=DIRECT;MATCHED_POWER_FACTORS;COMPOSITION"
  IO.println "HEIGHT_ROUTE_ANALYTIC_BASE=EXPLICIT_INPUT"
  IO.println "PAPER_EXCLUSIONS=ADVISORY_NOT_INSTALLED_AS_LEAN_PROOFS"
  IO.println "INSUFFICIENT_RATE_BOUNDS=INCONCLUSIVE_NOT_REJECTION"
  IO.println "PRODUCT_DECAY_TO_SEPARATED_GAP=NOT_CLAIMED"
  IO.println "SUCCESSFUL_ROUTE_WITNESSES_CONSTRUCTED=NO"
  IO.println "UNCONDITIONAL_ALL_ODD_ZETA_IRRATIONALITY=NOT_CLAIMED"
  IO.println "AXIOM_AUDIT_ACCEPTED=ZH_DERIVATION_ROUTER_CLOSURE"
