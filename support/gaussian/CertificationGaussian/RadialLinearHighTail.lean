import CertificationGaussian.RadialLinearHighGaussian
import CertificationGaussian.RadialHighTail

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Fixed polynomial factors preserve an explicit half of a positive exponential rate. -/
theorem radialLinear_polynomial_exp_absorb (C a : ℝ) (k : ℕ) (ha : 0<a) :
    ∀ᶠ n : ℕ in atTop,C*(n:ℝ)^k*Real.exp (-a*n)≤Real.exp (-(a/2)*n) := by
  filter_upwards [eventually_polynomial_le_exp C k (by linarith : 0<a/2)] with n hn
  calc
    _ ≤ Real.exp ((a/2)*n)*Real.exp (-a*n) := mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The actual first linear high-block Gaussian event at the unchanged n^-3 tolerance has exponential probability. -/
theorem radialLinearFirstHigh_gaussian_tail (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
        (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialLinearFirstHighWeights d n r ε lam k0) x‖}≤
          ENNReal.ofReal (Real.exp (-(radialLinearHighRate d ε/4)*n)) := by
  have hr := radialLinearHighRate_pos d hd ε hε hgap
  filter_upwards [radialLinearFirstHigh_gaussian_expectation d r hd ε hε hhalf hgap lam k0 hcard,
    radialLinear_polynomial_exp_absorb 1 (radialLinearHighRate d ε/2) 3 (by linarith),
    eventually_ge_atTop 1] with n hn hp hn1
  intro W h0 hW hHS
  let : IsProbabilityMeasure (pairedGaussian (QuditIndex d n)) := by unfold pairedGaussian; infer_instance
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a := radialLinearFirstHighWeights d n r ε lam k0
  have h := integrable_norm_tail_markov (pairedGaussian (QuditIndex d n)) (unitaryGaussianCentered G a)
    (unitaryGaussianCentered_integrable G a) ((n:ℝ)^3)⁻¹ (by positivity)
  refine h.trans (ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_right (hn W h0 hW hHS)
    (by positivity)).trans ?_))
  have he : 1*Real.exp (-(radialLinearHighRate d ε/2)*n)/((n:ℝ)^3)⁻¹=
      1*(n:ℝ)^3*Real.exp (-(radialLinearHighRate d ε/2)*n) := by field_simp
  have hdiv : radialLinearHighRate d ε/2/2=radialLinearHighRate d ε/4 := by ring
  refine le_trans (le_of_eq ?_) (show _≤_ from (by simpa only [hdiv] using hp))
  simpa only [one_mul] using he

/-- The actual second linear high-block Gaussian event at the unchanged n^-3 tolerance has exponential probability. -/
theorem radialLinearSecondHigh_gaussian_tail (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
        (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialLinearSecondHighWeights d n r ε lam k0) x‖}≤
          ENNReal.ofReal (Real.exp (-(radialLinearHighRate d ε/4)*n)) := by
  have hr := radialLinearHighRate_pos d hd ε hε hgap
  filter_upwards [radialLinearSecondHigh_gaussian_expectation d r hd ε hε hhalf hgap lam k0 hcard,
    radialLinear_polynomial_exp_absorb 2 (radialLinearHighRate d ε/2) 3 (by linarith),
    eventually_ge_atTop 1] with n hn hp hn1
  intro W h0 hW hHS
  let : IsProbabilityMeasure (pairedGaussian (QuditIndex d n)) := by unfold pairedGaussian; infer_instance
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a := radialLinearSecondHighWeights d n r ε lam k0
  have h := integrable_norm_tail_markov (pairedGaussian (QuditIndex d n)) (unitaryGaussianCentered G a)
    (unitaryGaussianCentered_integrable G a) ((n:ℝ)^3)⁻¹ (by positivity)
  refine h.trans (ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_right (hn W h0 hW hHS)
    (by positivity)).trans ?_))
  have he : 2*Real.exp (-(radialLinearHighRate d ε/2)*n)/((n:ℝ)^3)⁻¹=
      2*(n:ℝ)^3*Real.exp (-(radialLinearHighRate d ε/2)*n) := by field_simp
  have hdiv : radialLinearHighRate d ε/2/2=radialLinearHighRate d ε/4 := by ring
  refine le_trans (le_of_eq ?_) (show _≤_ from (by simpa only [hdiv] using hp))
  simpa only [one_mul] using he

/-- Same-sample joint event for both original high blocks; no independence is required. -/
theorem radialLinearHigh_gaussian_joint_tail (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      pairedGaussian (QuditIndex d n) {x |
        ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
          (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (radialLinearFirstHighWeights d n r ε lam k0) x‖ ∨
        ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
          (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (radialLinearSecondHighWeights d n r ε lam k0) x‖}≤
        ENNReal.ofReal (2*Real.exp (-(radialLinearHighRate d ε/4)*n)) := by
  filter_upwards [radialLinearFirstHigh_gaussian_tail d r hd ε hε hhalf hgap lam k0 hcard,
    radialLinearSecondHigh_gaussian_tail d r hd ε hε hhalf hgap lam k0 hcard] with n h1 h2
  intro W h0 hW hHS
  rw [Set.ofPred_or]
  refine (measure_union_le _ _).trans ((add_le_add (h1 W h0 hW hHS) (h2 W h0 hW hHS)).trans_eq ?_)
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
  congr 1
  ring

end CertificationGaussian
