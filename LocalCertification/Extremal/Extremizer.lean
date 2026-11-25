import LocalCertification.Extremal.OnePointModel
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open scoped BigOperators Topology OnePoint
open Filter Polynomial Set
noncomputable section
namespace LocalCertification.Extremal

/-- The actual OnePoint functions as a linear map to the sup-norm space. -/
def continuousNodeMap (q : ℝ) (hq : 1 < q) (r : ℕ) :
    CoeffSpace r →ₗ[ℝ] C(OnePoint ℕ, ℝ) where
  toFun c := ⟨nodeModelLinearMap q r c, by
    rw [nodeModelLinearMap_apply]
    exact polynomialNode_continuous q hq _ _⟩
  map_add' a b := ContinuousMap.ext (fun x => congrFun ((nodeModelLinearMap q r).map_add a b) x)
  map_smul' a b := ContinuousMap.ext (fun x => congrFun ((nodeModelLinearMap q r).map_smul a b) x)

theorem continuousNodeMap_injective (q : ℝ) (hq : 1 < q) (r : ℕ) :
    Function.Injective (continuousNodeMap q hq r) := by
  intro a b hab
  apply nodeModelLinearMap_injective q hq r
  exact congrArg (fun f : C(OnePoint ℕ, ℝ) => (f : OnePoint ℕ → ℝ)) hab

/-- All positive-integer and infinity constraints, with no finite truncation. -/
def feasible (q : ℝ) (r : ℕ) : Set (CoeffSpace r) :=
  {c | ∀ x, |polynomialNode q c.1 (coefficientPolynomial c) x| ≤ 1}

def extrapolation (r : ℕ) : CoeffSpace r →ₗ[ℝ] ℝ := pairing (extrapolationDictionary r)

theorem extrapolation_formula {r : ℕ} (c : CoeffSpace r) :
    extrapolation r c = c.1 + (coefficientPolynomial c).eval 0 := by
  rw [extrapolation, pairing_comm, pairing_extrapolation]
  rfl

theorem feasible_eq_preimage (q : ℝ) (hq : 1 < q) (r : ℕ) :
    feasible q r = (continuousNodeMap q hq r) ⁻¹' Metric.closedBall 0 1 := by
  ext c
  change (∀ x, |polynomialNode q c.1 (coefficientPolynomial c) x| ≤ 1) ↔
    dist (continuousNodeMap q hq r c) 0 ≤ 1
  rw [dist_zero_right, ContinuousMap.norm_le _ zero_le_one]
  simp only [continuousNodeMap, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousMap.coe_mk, nodeModelLinearMap_apply, Real.norm_eq_abs]

theorem feasible_compact (q : ℝ) (hq : 1 < q) (r : ℕ) : IsCompact (feasible q r) := by
  rw [feasible_eq_preimage q hq r]
  obtain ⟨K, hK, hanti⟩ := (continuousNodeMap q hq r).injective_iff_antilipschitz.mp
    (continuousNodeMap_injective q hq r)
  apply Metric.isCompact_of_isClosed_isBounded
  · exact Metric.isClosed_closedBall.preimage (continuousNodeMap q hq r).continuous_of_finiteDimensional
  · exact hanti.isBounded_preimage Metric.isBounded_closedBall

theorem zero_mem_feasible (q : ℝ) (r : ℕ) : (0 : CoeffSpace r) ∈ feasible q r := by
  intro x
  rw [← pairing_dictionary]
  simp [pairing]

theorem exists_extremizer (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃ c ∈ feasible q r, ∀ d ∈ feasible q r, extrapolation r d ≤ extrapolation r c := by
  exact (feasible_compact q hq r).exists_isMaxOn ⟨0, zero_mem_feasible q r⟩
    (extrapolation r).continuous_of_finiteDimensional.continuousOn

/-- The supremum of extrapolation over the full family of sample constraints. -/
def extremalValue (q : ℝ) (r : ℕ) : ℝ := sSup (extrapolation r '' feasible q r)

theorem extremalValue_attained (q : ℝ) (hq : 1 < q) (r : ℕ) :
    ∃ c ∈ feasible q r, extrapolation r c = extremalValue q r := by
  obtain ⟨c, hc, hmax⟩ := exists_extremizer q hq r
  refine ⟨c, hc, ?_⟩
  have hg : IsGreatest (extrapolation r '' feasible q r) (extrapolation r c) :=
    ⟨⟨c, hc, rfl⟩, by rintro _ ⟨d, hd, rfl⟩; exact hmax d hd⟩
  exact hg.csSup_eq.symm

theorem extrapolation_le_extremalValue (q : ℝ) (hq : 1 < q) (r : ℕ)
    {c : CoeffSpace r} (hc : c ∈ feasible q r) : extrapolation r c ≤ extremalValue q r := by
  obtain ⟨d, hd, hmax⟩ := exists_extremizer q hq r
  exact le_csSup ⟨extrapolation r d, by rintro _ ⟨e, he, rfl⟩; exact hmax e he⟩ ⟨c, hc, rfl⟩


/-- The explicit degree-zero feasible function 2q*q^{-w}-1. -/
def basicCandidate (q : ℝ) (r : ℕ) : CoeffSpace r :=
  (-1, Polynomial.toFn (r+1) (Polynomial.C (2*q)))

theorem basicCandidate_polynomial (q : ℝ) (r : ℕ) :
    coefficientPolynomial (basicCandidate q r) = Polynomial.C (2*q) := by
  apply polynomial_reconstruction
  simp only [Polynomial.natDegree_C, Nat.zero_le]

theorem basicCandidate_feasible (q : ℝ) (hq : 1 < q) (r : ℕ) :
    basicCandidate q r ∈ feasible q r := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  intro x
  change |polynomialNode q (-1) (coefficientPolynomial (basicCandidate q r)) x| ≤ 1
  rw [basicCandidate_polynomial]
  induction x using OnePoint.rec with
  | infty => simp
  | coe k =>
    rw [polynomialNode_nat, Polynomial.eval_C]
    have he : (q⁻¹)^(k+1) * (2*q) = 2*(q⁻¹)^k := by
      calc
        _ = 2*(q⁻¹)^k*(q⁻¹*q) := by rw [pow_succ]; ring
        _ = _ := by rw [inv_mul_cancel₀ (ne_of_gt hq0), mul_one]
    rw [he, abs_le]
    have hl : 0 ≤ (q⁻¹)^k := pow_nonneg (inv_nonneg.mpr hq0.le) k
    have hu : (q⁻¹)^k ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hq0.le)
      (le_of_lt ((inv_lt_one₀ hq0).mpr hq))
    constructor <;> linarith

theorem basicCandidate_extrapolation (q : ℝ) (r : ℕ) :
    extrapolation r (basicCandidate q r) = 2*q-1 := by
  rw [extrapolation_formula, basicCandidate_polynomial, Polynomial.eval_C]
  change -1 + 2*q = 2*q-1
  ring

theorem extremalValue_lower (q : ℝ) (hq : 1 < q) (r : ℕ) :
    2*q-1 ≤ extremalValue q r := by
  simpa only [basicCandidate_extrapolation] using
    extrapolation_le_extremalValue q hq r (basicCandidate_feasible q hq r)

theorem one_lt_extremalValue (q : ℝ) (hq : 1 < q) (r : ℕ) :
    1 < extremalValue q r := by
  have h := extremalValue_lower q hq r
  linarith

end LocalCertification.Extremal
