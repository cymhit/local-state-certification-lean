import LocalCertification.Asymptotic.EulerMomentAsymptotics
import LocalCertification.Certificates.StagedSearchConsumers
import Lean

open Lean Elab Command
private def releaseRouteRecord (root : String) (passed : Bool)
    (required forbidden : List String) : String :=
  "ROUTE_CHECK\t" ++ (Json.mkObj [("id",toJson root),("passed",toJson passed),
    ("required",toJson required),("forbidden",toJson forbidden),
    ("required_count",toJson required.length),("forbidden_count",toJson forbidden.length)]).compress


open scoped BigOperators OnePoint
open Polynomial LocalCertification.Extremal LocalCertification.Certificates
namespace EulerCertificatesReview

example (q : ℝ) (hq : 1 < q) :
    2*(q⁻¹)^1/(1+LocalCertification.Asymptotic.blaschkeCoefficientConstant q*Real.sqrt 1) ≤ gamma q 0 := by
  simpa using LocalCertification.Asymptotic.EulerMoments.gamma_blaschke_lower q hq 0
example : HasSum (fun n : ℕ => (n:ℝ)^0 * LocalCertification.Asymptotic.blaschkeCoeff 0 1 n * (0:ℝ)^n) 0 :=
  LocalCertification.Asymptotic.EulerMoments.blaschkeCoeff_hasSum_root_moment 0 (by norm_num) 1 0 (by omega)
-- Arbitrary positive node 8 at r=0; beta positivity needs neither feasibility nor optimality.
def farZeroNodes : Fin 2 → OnePoint ℕ := ![some 7,none]
example (q : ℚ) (hq : 1 < (q:ℝ)) :
    ∃ c : CanonicalCandidate q 0, c.x=farZeroNodes ∧ 1<c.beta ∧ c.p.eval 0=1 := by
  have ho : OrderedExtendedNodes (fun i => nodeToExtended (farZeroNodes i)) := by
    intro i j hij
    apply canonicalNodeLt_sound
    fin_cases i <;> fin_cases j <;> norm_num [farZeroNodes,canonicalNodeLt] at *
  obtain ⟨c,hc⟩ := canonicalCandidate_exists q hq 0 farZeroNodes ho rfl
  exact ⟨c,hc,c.beta_gt_one,c.p_zero⟩
example {q : ℚ} {r : ℕ} (c : CanonicalCandidate q r) (M : ℕ)
    (hc : c.canonicalArrayCheck M=true) (x : ℝ) (hx : M≤x) :
    0≤(c.Q.map (Rat.castHom ℝ)).eval x ∧
      0≤((weightedDifference q c.Q).map (Rat.castHom ℝ)).eval x :=
  c.canonical_real_ray M hc hx
-- A valid general certificate with its nodes permuted is deliberately noncanonical.
def permutedZero : CertificateData 0 := (-1,fun _ => 6,1,![none,some 0],![-2,3])
example : certificateCheck 3 0 permutedZero=true ∧ canonicalRawCheck 3 0 permutedZero=false := by
  unfold permutedZero
  norm_num [certificateCheck,canonicalRawCheck,canonicalRawCandidateCheck,canonicalNodeLt,canonicalParity,
    permutedZero,arrayTailCheck,shiftArrayCoeff,arrayPrefixCheck,arrayEval,
    executableNodeMonomial,Fin.sum_univ_succ,Fin.forall_fin_succ,Fin.last]
-- The final result is really the first passing member of the first successful finite stage.
example (q : ℚ) (hq : 1<(q:ℝ)) (r : ℕ) :
    (∀ N < stagedSearchIndex q hq r, stagedFind q r N=none) ∧
    ∃ before after,
      stagedData r (stagedSearchIndex q hq r)=before++stagedSearch q hq r::after ∧
      (∀ c ∈ before, canonicalRawCheck q r c=false) := by
  exact ⟨fun N hN => stagedSearchIndex_first q hq r N hN,
    (stagedFind_first q r _ _ (stagedSearch_terminates q hq r)).2⟩
#eval (stagedNodes 1 2).map fun f => List.ofFn f
#eval (List.range 4).map fun N => (stagedFind (3/2) 0 N).isSome
#eval stagedSearchIndex (3/2) (by norm_num) 0
#eval (stagedGamma (3/2) (by norm_num) 0,
  List.ofFn (stagedPolynomial (3/2) (by norm_num) 0))
#check @LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion
#check @canonicalCandidate_exists
#check @CanonicalCandidate.beta_gt_one
#check @LocalCertification.Certificates.CanonicalCandidate.optimality
#check @canonical_certificate_exists
#check @stagedData_canonical
#check @stagedOutput_correct
#print axioms LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion
#print axioms canonicalCandidate_exists
#print axioms CanonicalCandidate.beta_gt_one
#print axioms LocalCertification.Certificates.CanonicalCandidate.optimality
#print axioms canonical_certificate_exists
#print axioms stagedSearch_terminates
#print axioms stagedOutput_correct
end EulerCertificatesReview

open Lean Elab Command
run_elab do
  let env ← getEnv
  let suites : List (Name × List Name × List Name) := [
    (`LocalCertification.Asymptotic.EulerMoments.sharp_order_and_inversion,
      [`LocalCertification.Asymptotic.EulerMoments.eulerExpansion_succ, `LocalCertification.Asymptotic.EulerMoments.euler_root_zero,
       `LocalCertification.Asymptotic.EulerMoments.eulerExpansion_monomial, `LocalCertification.Asymptotic.blaschke_iteratedDeriv_eq_tsum,
       `LocalCertification.Asymptotic.EulerMoments.blaschkeCoeff_hasSum_root_moment,
       `LocalCertification.Asymptotic.EulerMoments.blaschkeDual_totalVariation, `LocalCertification.Asymptotic.EulerMoments.gamma_blaschke_lower,
       `LocalCertification.Asymptotic.EulerMoments.criticalDegree_log_bracket],
      [`LocalCertification.Asymptotic.blaschkeCoeff_hasSum_root_moment,
       `LocalCertification.Asymptotic.blaschkeDual_hasSum_reproduction,
       `LocalCertification.Asymptotic.gamma_blaschke_lower, `LocalCertification.Asymptotic.sharp_order_and_inversion]),
    (`LocalCertification.Certificates.stagedOutput_correct,
      [`LocalCertification.Certificates.stagedSearch_terminates, `LocalCertification.Certificates.stagedFind_first,
       `LocalCertification.Certificates.stagedData_exhaustive, `LocalCertification.Certificates.canonical_certificate_exists,
       `LocalCertification.Certificates.canonicalRawCheck_optimality, `LocalCertification.Certificates.CanonicalCandidate.optimality,
       `LocalCertification.Certificates.CanonicalCandidate.canonicalCheck_general,
       `LocalCertification.Certificates.CanonicalCandidate.tail_iff,
       `LocalCertification.Certificates.CanonicalCandidate.Q_positive_multiple,
       `LocalCertification.Certificates.CanonicalCandidate.beta_gt_one],
      [`LocalCertification.Certificates.searchCertificate, `LocalCertification.Certificates.searchCertificate_correct,
       `LocalCertification.Certificates.certificateAt_exists, `LocalCertification.Certificates.certificateCheck_exists])]
  for (root, required, forbidden) in suites do
    let mut todo := [root]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      let some val := ci.value? (allowOpaque := true) | continue
      for d in val.getUsedConstants do
        if d.toString.startsWith "LocalCertification." then todo := d :: todo
    for n in required do
      unless seen.contains n do throwError "Required actual proof-use missing: {root} -> {n}"
    for n in forbidden do
      if seen.contains n then throwError "Old endpoint shortcut: {root} -> {n}"
    logInfo m!"INDEPENDENT_PROOF_USE_PASS {root} ({seen.size} own declarations traversed)"
    logInfo (releaseRouteRecord root.toString true (required.map toString) (forbidden.map toString))



