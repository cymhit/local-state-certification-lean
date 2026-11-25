import CertificationGaussian.RadialProjection
import CertificationGaussian.Consumers.NetProbability

noncomputable section
open MeasureTheory Metric Filter Set
open scoped BigOperators ENNReal Topology
namespace CertificationGaussian

/-- The single common radial good event supplies positivity and a uniform reciprocal bound. -/
theorem radial_good_inverse {x t : ℝ} (hx : 2 ≤ x) (ht : |t-1| ≤ (x^2)⁻¹) :
    0 < t ∧ 1/t ≤ 1+1/x := by
  have hx0 : 0 < x := by linarith
  let w := 1/x
  have hw0 : 0 < w := by dsimp [w]; positivity
  have hw : w ≤ 1/2 := by
    dsimp [w]
    apply (div_le_iff₀ hx0).mpr
    linarith
  have hrad : |t-1| ≤ w^2 := by simpa only [w, div_pow, one_pow, one_div, inv_pow] using ht
  have htlo : 1-w^2 ≤ t := by have h := (abs_le.mp hrad).1; linarith
  have hw2 : w^2 ≤ w/2 := by nlinarith
  have hw3 : w^3 ≤ w/4 := by
    have h := mul_le_mul_of_nonneg_left hw2 hw0.le
    nlinarith
  have ht0 : 0 < t := by nlinarith
  have hprod : 1 ≤ t*(1+w) := by
    have h := mul_le_mul_of_nonneg_right htlo (show 0 ≤ 1+w by positivity)
    nlinarith
  refine ⟨ht0, (div_le_iff₀ ht0).mpr ?_⟩
  dsimp [w] at hprod
  nlinarith

/-- Scalar bookkeeping from the exact projection identity; no extra radial error is added. -/
theorem score_bound_of_good_quartic_radius {x t q v s : ℝ} (hx : 2 ≤ x) (hv : 0 ≤ v)
    (hs : 0 ≤ s) (hq : |q| ≤ v/x) (ht : |t-1| ≤ (x^2)⁻¹)
    (hscore : s^2 ≤ (q+v)/t^2) : s ≤ Real.sqrt v*(1+1/x)^2 := by
  obtain ⟨ht0, hinv⟩ := radial_good_inverse hx ht
  have hx0 : 0 < x := by linarith
  have hw : 1 ≤ 1+1/x := by
    have h : 0 ≤ 1/x := by positivity
    linarith
  have hq' : q+v ≤ v*(1+1/x) := by
    calc
      _ ≤ v/x+v := add_le_add ((le_abs_self q).trans hq) le_rfl
      _ = _ := by ring
  apply (sq_le_sq₀ hs (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hv, ← pow_mul]
  norm_num only [Nat.reduceMul]
  calc
    _ ≤ (q+v)/t^2 := hscore
    _ ≤ (v*(1+1/x))/t^2 := div_le_div_of_nonneg_right hq' (sq_nonneg _)
    _ = v*(1+1/x)*(1/t)^2 := by ring
    _ ≤ v*(1+1/x)*(1+1/x)^2 := by gcongr
    _ = v*(1+1/x)^3 := by ring
    _ ≤ v*(1+1/x)^4 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hw (by decide)) hv

/-- The deterministic net-to-all-bases numerical factor is 1+16/n for n>=2. -/
theorem score_factor_sixteen {x v s : ℝ} (hx : 2 ≤ x) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (h : s ≤ Real.sqrt v*(1+1/x)^2+Real.sqrt v/x) :
    s^2 ≤ (1+16/x)*v := by
  have hx0 : 0 < x := by linarith
  let w := 1/x
  have hw0 : 0 < w := by dsimp [w]; positivity
  have hw : w ≤ 1/2 := by dsimp [w]; apply (div_le_iff₀ hx0).mpr; linarith
  have hfac : (1+w)^2+w ≤ 1+4*w := by nlinarith
  have hs' : s ≤ Real.sqrt v*(1+4*w) := by
    calc
      _ ≤ Real.sqrt v*((1+w)^2+w) := by convert h using 1; dsimp [w]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
  have hs2 := (sq_le_sq₀ hs (by positivity)).mpr hs'
  have hfac2 : (1+4*w)^2 ≤ 1+16*w := by nlinarith
  calc
    _ ≤ (Real.sqrt v*(1+4*w))^2 := hs2
    _ = v*(1+4*w)^2 := by rw [mul_pow, Real.sq_sqrt hv]
    _ ≤ v*(1+16*w) := mul_le_mul_of_nonneg_left hfac2 hv
    _ = _ := by dsimp [w]; ring

/-- The actual net good event and the one common radial event imply the bound for every product basis. -/
theorem all_product_score_of_net_good {d n : Nat} (hd : 2 ≤ d) (hn : 2 ≤ n)
    (J : Finset Nat) (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1)
    (S : Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (hS : ∀ W ∈ S, W ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (hcover : ∀ U : Fin n → LocalUnitary d, ∃ W ∈ S,
      ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ) (tensorUnitaryMatrix d n U-W)‖ ≤
        n*(d:ℝ)^n*kernelNetMesh d n J θ)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (x : (Fin 2 × QuditIndex d n) → ℝ)
    (hgood : ∀ W ∈ S, |quditQuartic d n J θ W x| ≤ kernelVarianceScale d n J θ/n)
    (hrad : |gaussianRadius (QuditIndex d n) x-1| ≤ ((n:ℝ)^2)⁻¹) :
    ∀ U : Fin n → LocalUnitary d,
      (quditSphereScore d n J θ (tensorUnitaryMatrix d n U)
        (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)))^2 ≤
      (1+16/n)*kernelVarianceScale d n J θ := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have ht := (radial_good_inverse hnR hrad).1
  have hx : complexGaussianLift (QuditIndex d n) x ≠ 0 := by
    intro hz
    rw [gaussianRadius_eq_norm_sq, hz] at ht
    norm_num at ht
  let ψ : EuclideanSpace ℂ (QuditIndex d n) := sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)
  have hψ : ‖ψ‖ = 1 := mem_sphere_zero_iff_norm.mp (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)).property
  have hv := kernelVarianceScale_nonneg d n J θ
  intro U
  obtain ⟨W, hW, hdist⟩ := hcover U
  have hWscore : quditSphereScore d n J θ W ψ ≤
      Real.sqrt (kernelVarianceScale d n J θ)*(1+1/(n:ℝ))^2 :=
    score_bound_of_good_quartic_radius hnR hv
      (sphereScore_nonneg W (signedHammingKernel d n J θ) ψ) (hgood W hW) hrad
      (qudit_direction_score_sq_le hd J hJ θ hθ W (hS W hW) e₀ x hx)
  have hdist' := mul_le_mul_of_nonneg_left hdist
    (show 0 ≤ 2*kernelWeightL1 J θ*(d:ℝ)^n by have h := kernelWeightL1_nonneg J θ; positivity)
  rw [kernelNetMesh_transfer_scale hd (by omega) J θ hθ] at hdist'
  have hscore := (quditSphereScore_lipschitz hd J hJ θ (tensorUnitaryMatrix d n U) W
    (tensorUnitaryMatrix_unitary d n U) (hS W hW) ψ hψ).trans (add_le_add hWscore hdist')
  exact score_factor_sixteen hnR hv
    (sphereScore_nonneg (tensorUnitaryMatrix d n U) (signedHammingKernel d n J θ) ψ) hscore

/-- The final good set quantifies over all local unitary choices, not only a finite net. -/
def allProductSphereGood (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ) :
    Set (sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1) :=
  {ψ | ∀ U : Fin n → LocalUnitary d,
    (quditSphereScore d n J θ (tensorUnitaryMatrix d n U) ψ)^2 ≤
      (1+16/n)*kernelVarianceScale d n J θ}

/-- Arbitrary intersections of closed score sublevel sets are closed; no uncountable-sup measurability is assumed. -/
theorem allProductSphereGood_isClosed (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ) :
    IsClosed (allProductSphereGood d n J θ) := by
  have he : allProductSphereGood d n J θ = ⋂ U : Fin n → LocalUnitary d,
      {ψ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 |
        (quditSphereScore d n J θ (tensorUnitaryMatrix d n U) ψ)^2 ≤
          (1+16/n)*kernelVarianceScale d n J θ} := by ext ψ; simp [allProductSphereGood]
  rw [he]
  apply isClosed_iInter
  intro U
  apply isClosed_le
  · exact ((sphereScore_continuous (tensorUnitaryMatrix d n U) (signedHammingKernel d n J θ)).comp continuous_subtype_val).pow 2
  · exact continuous_const

/-- The actual canonical sphere probability of failure for any product basis is cubically small. -/
theorem allProductSphereGood_exception_two {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ N : Nat, ∀ n ≥ N,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (allProductSphereGood d n J θ)ᶜ ≤
      2*ENNReal.ofReal (Real.exp (-(Real.log d/8)*(n:ℝ)^3)) := by
  obtain ⟨K, _, N, hN⟩ := Consumers.actual_net_and_radius_package hd J θ hθ
  refine ⟨max N (max 2 (J.sup id)), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hJ : ∀ k ∈ J, k ≤ n := by
    intro k hk
    have hk' : k ≤ J.sup id := Finset.le_sup (f := id) hk
    omega
  obtain ⟨S, hS, _, hcover, hprob⟩ := hN n ((le_max_left _ _).trans hn)
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty (E := EuclideanSpace ℂ (QuditIndex d n))).mpr (show (0:ℝ) ≤ 1 by norm_num)
  let e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1 := ⟨z, hz⟩
  have hm : Measurable (fun x : (Fin 2 × QuditIndex d n) → ℝ =>
      sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)) :=
    (sphereDirection_measurable e₀).comp (complexGaussianLift_continuous _).measurable
  rw [← complexGaussian_direction_map (QuditIndex d n) e₀]
  rw [Measure.map_apply hm (allProductSphereGood_isClosed d n J θ).measurableSet.compl]
  apply (measure_mono ?_).trans hprob
  intro x hx
  by_contra hnot
  have hb := not_or.mp hnot
  have hgood : ∀ W ∈ S, |quditQuartic d n J θ W x| ≤ kernelVarianceScale d n J θ/n := by
    intro W hW
    exact (lt_of_not_ge (fun h => hb.1 ⟨W, hW, h⟩)).le
  have hrad : |gaussianRadius (QuditIndex d n) x-1| ≤ ((n:ℝ)^2)⁻¹ := (lt_of_not_ge hb.2).le
  exact hx (all_product_score_of_net_good hd hn2 J hJ θ hθ S hS hcover e₀ x hgood hrad)

/-- Absorb the two exceptional sources into a slightly smaller cubic exponential rate. -/
theorem eventually_two_mul_exp_cubic {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n : Nat in atTop,
      2*Real.exp (-a*(n:ℝ)^3) ≤ Real.exp (-(a/2)*(n:ℝ)^3) := by
  filter_upwards [eventually_polynomial_le_exp 2 0 (show 0 < a/2 by positivity),
    eventually_ge_atTop 1] with n hn hn1
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hn3 : (n:ℝ) ≤ (n:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hnR (show 1≤3 by decide)
  have hmul := mul_le_mul_of_nonneg_left hn3 (show 0 ≤ a/2 by positivity)
  calc
    _ ≤ Real.exp ((a/2)*n)*Real.exp (-a*(n:ℝ)^3) := by
      exact mul_le_mul_of_nonneg_right (by simpa using hn) (Real.exp_nonneg _)
    _ = Real.exp ((a/2)*n-a*(n:ℝ)^3) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- The uniform product-basis score bound on the standard sphere, with C=16 and c=log(d)/16. -/
theorem uniform_product_score_standard_sphere {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ N : Nat, ∀ n ≥ N,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (allProductSphereGood d n J θ)ᶜ ≤
      ENNReal.ofReal (Real.exp (-(Real.log d/16)*(n:ℝ)^3)) := by
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  have ha : 0 < Real.log d/8 := div_pos (Real.log_pos hdR) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := allProductSphereGood_exception_two hd J θ hθ
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (eventually_two_mul_exp_cubic ha)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  apply (hN₁ n ((le_max_left _ _).trans hn)).trans
  have h := ENNReal.ofReal_le_ofReal (hN₂ n ((le_max_right _ _).trans hn))
  have he : (Real.log d/8)/2 = Real.log d/16 := by ring
  simpa only [he, ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat] using h

end CertificationGaussian
