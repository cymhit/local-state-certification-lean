import LocalCertification.Certificates.PolynomialTail
import Mathlib.Analysis.Polynomial.Basic

set_option autoImplicit false
open scoped BigOperators Topology
open Polynomial Filter
noncomputable section
namespace LocalCertification.Certificates

/-- Positive leading coefficient gives eventual positivity, also at actual degree zero. -/
theorem polynomial_eventually_positive (p : ℚ[X]) (hp : 0 < p.leadingCoeff) :
    ∀ᶠ M : ℕ in atTop, 0 < p.eval (M : ℚ) := by
  by_cases hd : p.natDegree = 0
  · have he := Polynomial.eq_C_of_natDegree_eq_zero hd
    have hpos : 0 < p.coeff 0 := by simpa only [Polynomial.leadingCoeff, hd] using hp
    apply Filter.Eventually.of_forall
    intro M
    rw [he, Polynomial.eval_C]
    exact hpos
  · have he := (p.tendsto_atTop_of_leadingCoeff_nonneg
      (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)) hp.le).eventually_gt_atTop 0
    exact tendsto_natCast_atTop_atTop.eventually he

/-- Every Hasse derivative up to the actual degree has positive leading coefficient. -/
theorem hasseDeriv_leading_positive (p : ℚ[X]) (hp : 0 < p.leadingCoeff)
    (k : ℕ) (hk : k ≤ p.natDegree) : 0 < (p.hasseDeriv k).leadingCoeff := by
  simp only [Polynomial.leadingCoeff, Polynomial.natDegree_hasseDeriv,
    Polynomial.hasseDeriv_coeff, Nat.sub_add_cancel hk]
  exact mul_pos (by exact_mod_cast Nat.choose_pos hk) hp

/-- The finite shifted-array test eventually succeeds for every positive-leading polynomial. -/
theorem shifted_coefficients_eventually_nonnegative (p : ℚ[X]) (hp : 0 < p.leadingCoeff) :
    ∀ᶠ M : ℕ in atTop, coefficientsNonnegative (shiftedPolynomial p M) := by
  have he : ∀ᶠ M : ℕ in atTop, ∀ k ∈ Finset.range (p.natDegree+1),
      0 < (p.hasseDeriv k).eval (M : ℚ) := by
    rw [Filter.eventually_all_finset]
    intro k hk
    exact polynomial_eventually_positive _
      (hasseDeriv_leading_positive p hp k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  filter_upwards [he] with M hM
  intro k hk
  have hd : k ≤ p.natDegree := by
    have h := Polynomial.le_natDegree_of_mem_supp _ hk
    simpa only [shiftedPolynomial, ← Polynomial.taylor_apply, Polynomial.natDegree_taylor] using h
  change 0 ≤ (Polynomial.taylor (M : ℚ) p).coeff k
  rw [Polynomial.taylor_coeff]
  exact (hM k (Finset.mem_range.mpr (Nat.lt_succ_of_le hd))).le

/-- The difference has the original actual degree and positive leading coefficient (q-1)*lc. -/
theorem weightedDifference_degree_leading (q : ℚ) (hq : 1 < q)
    (p : ℚ[X]) (hp : 0 < p.leadingCoeff) :
    (weightedDifference q p).natDegree = p.natDegree ∧
      (weightedDifference q p).leadingCoeff = (q-1)*p.leadingCoeff := by
  have he : p.comp (X+1) = Polynomial.taylor (1 : ℚ) p := by simp only [Polynomial.taylor_apply, map_one]
  have hd : (weightedDifference q p).natDegree ≤ p.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    simp only [weightedDifference, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt hN, mul_zero, he]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa only [Polynomial.natDegree_taylor] using hN), sub_zero]
  have hc : (weightedDifference q p).coeff p.natDegree = (q-1)*p.leadingCoeff := by
    simp only [weightedDifference, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_natDegree, he, Polynomial.coeff_taylor_natDegree]
    ring
  have hpos : 0 < (q-1)*p.leadingCoeff := mul_pos (sub_pos.mpr hq) hp
  have hdegree := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hd (hc.trans_ne hpos.ne')
  refine ⟨hdegree,?_⟩
  simpa only [Polynomial.leadingCoeff, hdegree] using hc

/-- Both finite coefficient arrays eventually pass. The threshold uses the true degree, not an assumed top degree. -/
theorem tailCheck_eventually (q : ℚ) (hq : 1 < q) (p : ℚ[X]) (hp : 0 < p.leadingCoeff) :
    ∀ᶠ M : ℕ in atTop, tailCheck q p M := by
  have hR : 0 < (weightedDifference q p).leadingCoeff := by
    rw [(weightedDifference_degree_leading q hq p hp).2]
    exact mul_pos (sub_pos.mpr hq) hp
  filter_upwards [shifted_coefficients_eventually_nonnegative p hp,
    shifted_coefficients_eventually_nonnegative (weightedDifference q p) hR] with M h1 h2
  exact ⟨h1,h2⟩

/-- Searching shifts from any finite starting point necessarily reaches a passing finite test. -/
theorem exists_tailCheck_after (q : ℚ) (hq : 1 < q) (p : ℚ[X])
    (hp : 0 < p.leadingCoeff) (J : ℕ) : ∃ M : ℕ, J ≤ M ∧ tailCheck q p M := by
  exact ((eventually_ge_atTop J).and (tailCheck_eventually q hq p hp)).exists

/-- A negative leading coefficient really violates the infinite constraint, arbitrarily far out. -/
theorem negative_leading_rejected (q : ℚ) (hq : 0 < q) (h : ℚ) (hh : |h|=1)
    (p : ℚ[X]) (hp : p.leadingCoeff < 0) (J : ℕ) :
    ∃ w : ℕ, J ≤ w ∧ 1 < |orientedCandidateValue q h p w| := by
  have hneg := polynomial_eventually_positive (-p) (by simpa only [Polynomial.leadingCoeff_neg] using neg_pos.mpr hp)
  obtain ⟨w,hw,hpneg⟩ := ((eventually_ge_atTop J).and hneg).exists
  have hv : p.eval (w : ℚ) < 0 := by simpa only [Polynomial.eval_neg, neg_pos] using hpneg
  have ha : weightedPolynomial q p w < 0 := mul_neg_of_pos_of_neg (pow_pos (inv_pos.mpr hq) w) hv
  refine ⟨w,hw,?_⟩
  simp only [orientedCandidateValue, abs_mul, hh, one_mul]
  rw [abs_of_pos (by linarith)]
  linarith

end LocalCertification.Certificates
