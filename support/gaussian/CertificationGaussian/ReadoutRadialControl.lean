import CertificationGaussian.CardinalityReadoutMoments
import CertificationGaussian.TailAsymptotics

noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian

/-- The actual common-radius Markov prefactor for any fixed inverse natural power threshold. -/
theorem radial_power_prefactor_le {x D : ℝ} (hx : 1≤x) (hD : 0<D) (k : ℕ) :
    5*(x^2-1)^2*Real.sqrt D⁻¹/(x^k)⁻¹ ≤ 5*x^(4+k)/Real.sqrt D := by
  have hs : (x^2-1)^2≤x^4 := by nlinarith [sq_nonneg (x^2-1)]
  rw [Real.sqrt_inv,div_inv_eq_mul]
  calc
    _ ≤ 5*x^4*(Real.sqrt D)⁻¹*x^k := by gcongr
    _ = _ := by rw [pow_add]; ring

/-- Every fixed power threshold has a cubic exponential bound on the one actual common radius. -/
theorem quditRadius_power_eventually_cubic {d : ℕ} (hd : 2≤d) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^k)⁻¹≤|gaussianRadius (QuditIndex d n) x-1|} ≤
        ENNReal.ofReal (Real.exp (-(Real.log d/4)*(n:ℝ)^3)) := by
  filter_upwards [eventually_polynomial_gaussian_cubic hd (show (0:ℝ)≤5 by norm_num) (4+k),
    eventually_ge_atTop 2] with n hb hn
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hD : (0:ℝ)<(d:ℝ)^n := by positivity
  have ht := gaussianRadialFluctuation_abs_tail (QuditIndex d n) ((n:ℝ)^2) (by nlinarith)
    (((n:ℝ)^k)⁻¹) (by positivity)
  simp only [gaussianRadialFluctuation,qudit_card,Nat.cast_pow] at ht
  exact ht.trans ((ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow (by positivity) (radial_power_prefactor_le (by linarith) hD k) (by positivity))).trans
      (ENNReal.ofReal_le_ofReal hb))

/-- A deterministic scalar estimate for the inverse of a radius within delta of one. -/
theorem inverse_radius_near_one {t δ : ℝ} (hδ : 0≤δ) (hδ2 : δ≤1/2) (ht : |t-1|≤δ) :
    0<t ∧ 0≤t⁻¹ ∧ t⁻¹≤2 ∧ |t⁻¹-1|≤2*δ := by
  have htlo : 1-δ≤t := by have h := (abs_le.mp ht).1; linarith
  have htpos : 0<t := by linarith
  have hinv : 0≤t⁻¹ := inv_nonneg.mpr htpos.le
  have hmul : t*t⁻¹=1 := mul_inv_cancel₀ htpos.ne'
  have hinv2 : t⁻¹≤2 := by nlinarith
  have he : t⁻¹-1= -(t-1)*t⁻¹ := by nlinarith
  refine ⟨htpos,hinv,hinv2,?_⟩
  rw [he,abs_mul,abs_neg,abs_of_nonneg hinv]
  exact (mul_le_mul_of_nonneg_right ht hinv).trans (by nlinarith)

/-- The exact scorebounds radial threshold is at most one half from n=2 onwards. -/
theorem readout_radius_threshold_le_half {n : ℕ} (hn : 2≤n) (r : ℕ) :
    ((n:ℝ)^(r+4))⁻¹≤1/2 := by
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hp : (2:ℝ)≤(n:ℝ)^(r+4) := hn'.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ)≤n by linarith) (show 1≤r+4 by omega))
  rw [← one_div]
  exact (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)^(r+4))).mpr (by nlinarith)

/-- On the actual common-radius good event, the same alpha in the full-second-moment identity is controlled and the Gaussian vector is nonzero. -/
theorem quditReadout_good_radius {d n : ℕ} (hn : 2≤n) (r : ℕ)
    (x : Fin 2 × QuditIndex d n → ℝ)
    (hx : |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹) :
    (WithLp.toLp 2 (complexCoordinate x) : EuclideanSpace ℂ (QuditIndex d n))≠0 ∧
    0≤readoutRadialAlpha ((d:ℝ)^n) (complexCoordinate x) ∧
    readoutRadialAlpha ((d:ℝ)^n) (complexCoordinate x)≤2 ∧
    |readoutRadialAlpha ((d:ℝ)^n) (complexCoordinate x)-1|≤2*((n:ℝ)^(r+4))⁻¹ := by
  have hrad : gaussianRadius (QuditIndex d n) x=
      ‖(WithLp.toLp 2 (complexCoordinate x) : EuclideanSpace ℂ (QuditIndex d n))‖^2/(d:ℝ)^n := by
    simpa only [qudit_card,Nat.cast_pow,complexGaussianLift] using
      gaussianRadius_eq_norm_sq (QuditIndex d n) x
  have hh := inverse_radius_near_one (by positivity : (0:ℝ)≤((n:ℝ)^(r+4))⁻¹)
    (readout_radius_threshold_le_half hn r) hx
  have hne : (WithLp.toLp 2 (complexCoordinate x) : EuclideanSpace ℂ (QuditIndex d n))≠0 := by
    intro hz
    rw [hz,norm_zero,zero_pow (by decide),zero_div] at hrad
    linarith [hh.1]
  have ha : readoutRadialAlpha ((d:ℝ)^n) (complexCoordinate x)=
      (gaussianRadius (QuditIndex d n) x)⁻¹ := by
    rw [readoutRadialAlpha_eq_inverse_radius,← hrad]
  simpa only [ha] using And.intro hne hh.2

end CertificationGaussian
