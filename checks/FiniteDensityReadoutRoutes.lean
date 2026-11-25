import LocalCertification.Information.ProductDensityChainRule
import LocalCertification.Information.SeedCountingReference
import LocalCertification.Quantum.CompleteReadoutLoewner
import CertificationGaussian.CompleteMUBFullControl
import CertificationGaussian.FiniteWickInclusionExclusionBounds
import Lean

open Lean Elab Command
private def releaseRouteRecord (root : String) (passed : Bool)
    (required forbidden : List String) : String :=
  "ROUTE_CHECK\t" ++ (Json.mkObj [("id",toJson root),("passed",toJson passed),
    ("required",toJson required),("forbidden",toJson forbidden),
    ("required_count",toJson required.length),("forbidden_count",toJson forbidden.length)]).compress


open Lean Elab Command


run_elab do
  let env ← getEnv
  let mut failed := false
  let forbidden : List Name := [`LocalCertification.Information.prefixLaw_klDiv_eq_sum,
          `LocalCertification.Information.prefixLaw_stopped_klDiv_le,
          `InformationTheory.klDiv_compProd_eq_add,
          `CertificationGaussian.complexGaussian_four_normal_blocks,
          `CertificationGaussian.complexGaussian_block_wick,
          `CertificationGaussian.gaussianNormalProduct_recursion,
          `CertificationGaussian.gaussianNormalQuartic_adjoint,
          `CertificationGaussian.gaussianBarCreation_adjoint,
          `CertificationGaussian.three_matching_sixth_bound,
          `CertificationGaussian.FourVertexMultigraph.overlap_integral_le,
          `CertificationGaussian.FourVertexMultigraph.overlapProduct_matchings,
          `CertificationGaussian.pauliConditionalIntegral_le,
          `CertificationGaussian.pauliResidualProduct_integral_le,
          `CertificationGaussian.completeMUBConditionalIntegral_le,
          `CertificationGaussian.completeMUBResidualProduct_integral_le]
  for (root, required) in [
      (`LocalCertification.Information.prefixLaw_stopped_klDiv_le_product_density,
        [`LocalCertification.Information.prefixLaw_withDensity_productDensity,
         `LocalCertification.Information.sum_negativeRelativeEntropyAtom_le,
         `LocalCertification.Information.sum_positiveRelativeEntropyAtom_le,
         `LocalCertification.Information.integrable_slotLogLikelihood,
         `LocalCertification.Information.prefixProductLikelihood_log_expand,
         `LocalCertification.Information.prefixLogLikelihoodSum_integral]),
      (`LocalCertification.Quantum.completeHaarReadout_loewner_eventually,
        [`CertificationGaussian.haarFourOverlapIntegral_scaled_le_via_incident_holder,
         `CertificationGaussian.IncidentHolder.integral_six_holder,
         `CertificationGaussian.IncidentHolder.integral_incident_holder,
         `CertificationGaussian.IncidentHolder.triangle_elimination,
         `CertificationGaussian.fourWickExpansionFiberEquiv,
         `CertificationGaussian.fourWickExpansionFiberEquiv_sign,
         `CertificationGaussian.finiteWick_subset_cancellation]),
      (`LocalCertification.Quantum.completePauliReadout_loewner_eventually,
        [`CertificationGaussian.pauliFourOverlapIntegral_scaled_le_via_incident_holder,
         `CertificationGaussian.IncidentHolder.integral_incident_holder,
         `CertificationGaussian.IncidentHolder.triangle_elimination,
         `CertificationGaussian.fourWickExpansionFiberEquiv,
         `CertificationGaussian.finiteWick_subset_cancellation]),
      (`CertificationGaussian.radialMUB_full_readout_haar_eventually,
        [`CertificationGaussian.completeMUBFourOverlapIntegral_scaled_le_via_incident_holder,
         `CertificationGaussian.IncidentHolder.integral_incident_holder,
         `CertificationGaussian.IncidentHolder.triangle_elimination,
         `CertificationGaussian.fourWickExpansionFiberEquiv,
         `CertificationGaussian.finiteWick_subset_cancellation])] do
    unless env.contains root do throwError "Missing endpoint: {root}"
    let mut todo : List (Name × List Name) := [(root, [])]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let (n, path) := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      if forbidden.contains n then
        failed := true
        logInfo m!"OLD_ROUTE_REACHED: {String.intercalate " → " ((n :: path).reverse.map toString)}"
      let some ci := env.find? n | continue
      let deps := ci.type.getUsedConstants ++
        ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
      for d in deps do
        if d.toString.startsWith "LocalCertification." || d.toString.startsWith "CertificationGaussian." ||
            d == `InformationTheory.klDiv_compProd_eq_add then
          todo := (d, n :: path) :: todo
    for n in required do
      unless seen.contains n do
        failed := true
        logInfo m!"MISSING_NEW_STEP {root}: {n}"
    logInfo m!"REVIEW_ENDPOINT_INSPECTED {root}; LocalCertification declarations={seen.size}"
    logInfo (releaseRouteRecord root.toString (!failed) (required.map toString) (forbidden.map toString))
  if failed then throwError "Independent downstream route audit found old-route or missing-step dependencies"
  logInfo "FINITE_DENSITY_READOUT_ROUTES_PASS"

#print axioms LocalCertification.Information.prefixLaw_stopped_klDiv_le_product_density
#print axioms LocalCertification.Quantum.completeHaarReadout_loewner_eventually
#print axioms LocalCertification.Quantum.completePauliReadout_loewner_eventually
#print axioms CertificationGaussian.radialMUB_full_readout_haar_eventually
#check @LocalCertification.Information.originalSeed_prefixLaw_product_density
#check @CertificationGaussian.complexGaussian_four_normal_blocks_finite_inclusion_exclusion
#check @CertificationGaussian.completeMUB_local_graph_contraction_via_incident_holder

