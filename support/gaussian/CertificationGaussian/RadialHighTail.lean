import CertificationGaussian.RadialHighGaussian

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian

/-- Markov applied to an actually integrable norm on a probability space, with an ENNReal event bound. -/
theorem integrable_norm_tail_markov {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → E) (hf : Integrable f μ) (t : ℝ) (ht : 0<t) :
    μ {x | t<‖f x‖}≤ENNReal.ofReal ((∫ x,‖f x‖∂μ)/t) := by
  have hm := mul_meas_ge_le_integral_of_nonneg (μ:=μ)
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hf.norm t
  have hs : {x | t<‖f x‖} ⊆ {x | t≤‖f x‖} := by
    intro x hx
    change t<‖f x‖ at hx
    change t≤‖f x‖
    exact hx.le
  have hr : μ.real {x | t<‖f x‖}≤(∫ x,‖f x‖∂μ)/t :=
    (measureReal_mono hs).trans
      ((le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hm))
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal hr

/-- The true first high Gaussian norm event at n^-3 has probability at most C*n^-8. -/
theorem radialFirstHigh_gaussian_tail {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
        (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialFirstHighWeights d r lam k0) x‖} ≤
          ENNReal.ofReal (radialHighGaussianConstant d r lam*((n:ℝ)^8)⁻¹) := by
  filter_upwards [radialFirstHigh_gaussian_expectation d r hd lam k0 hcard,
    eventually_ge_atTop 1] with n hn hn1
  intro W h0 hW hHS
  let : IsProbabilityMeasure (pairedGaussian (QuditIndex d n)) := by unfold pairedGaussian; infer_instance
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a := radialFirstHighWeights (S:=Fin n) d r lam k0
  have h := integrable_norm_tail_markov (pairedGaussian (QuditIndex d n)) (unitaryGaussianCentered G a)
    (unitaryGaussianCentered_integrable G a) ((n:ℝ)^3)⁻¹ (by positivity)
  refine h.trans (ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_right (hn W h0 hW hHS)
    (by positivity)).trans_eq ?_))
  field_simp

/-- The true second high Gaussian event retains the exact factor2 and the squared original coefficients. -/
theorem radialSecondHigh_gaussian_tail {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      pairedGaussian (QuditIndex d n) {x | ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
        (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialSecondHighWeights d r lam k0) x‖} ≤
          ENNReal.ofReal ((2*radialHighGaussianConstant d r (fun j => (lam j)^2))*((n:ℝ)^8)⁻¹) := by
  filter_upwards [radialSecondHigh_gaussian_expectation d r hd lam k0 hcard,
    eventually_ge_atTop 1] with n hn hn1
  intro W h0 hW hHS
  let : IsProbabilityMeasure (pairedGaussian (QuditIndex d n)) := by unfold pairedGaussian; infer_instance
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a := radialSecondHighWeights (S:=Fin n) d r lam k0
  have h := integrable_norm_tail_markov (pairedGaussian (QuditIndex d n)) (unitaryGaussianCentered G a)
    (unitaryGaussianCentered_integrable G a) ((n:ℝ)^3)⁻¹ (by positivity)
  refine h.trans (ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_right (hn W h0 hW hHS)
    (by positivity)).trans_eq ?_))
  field_simp

/-- Both true high-block events are controlled on the same Gaussian sample, with no independence premise. -/
theorem radialHigh_gaussian_joint_tail {K : Type*} [Fintype K] [DecidableEq K]
    (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      pairedGaussian (QuditIndex d n) {x |
        ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
          (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (radialFirstHighWeights d r lam k0) x‖ ∨
        ((n:ℝ)^3)⁻¹<‖unitaryGaussianCentered
          (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (radialSecondHighWeights d r lam k0) x‖} ≤
        ENNReal.ofReal ((radialHighGaussianConstant d r lam+
          2*radialHighGaussianConstant d r (fun j => (lam j)^2))*((n:ℝ)^8)⁻¹) := by
  have hC := (radialHighGaussianConstant_pos d r hd lam).le
  have hC2 := (radialHighGaussianConstant_pos d r hd (fun j => (lam j)^2)).le
  filter_upwards [radialFirstHigh_gaussian_tail d r hd lam k0 hcard,
    radialSecondHigh_gaussian_tail d r hd lam k0 hcard] with n h1 h2
  intro W h0 hW hHS
  rw [Set.ofPred_or]
  refine (measure_union_le _ _).trans ((add_le_add (h1 W h0 hW hHS) (h2 W h0 hW hHS)).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end CertificationGaussian
