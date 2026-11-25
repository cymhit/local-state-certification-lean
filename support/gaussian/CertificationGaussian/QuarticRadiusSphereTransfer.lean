import CertificationGaussian.SphereTransfer
import CertificationGaussian.SphereScoreL1
import CertificationGaussian.PackingNetAsymptotics
import CertificationGaussian.ReadoutRadialControl
import CertificationGaussian.Consumers.PackingNetProbability
noncomputable section
open MeasureTheory Metric Filter Set
open scoped BigOperators ENNReal Topology
namespace CertificationGaussian
theorem inverse_fourth_power_le_inverse_square {x : ℝ} (hx : 2 ≤ x) :
    (x^4)⁻¹ ≤ (x^2)⁻¹ := by
  have hx0 : 0 < x := by linarith
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ (by linarith : 1 ≤ x) (by decide : 2 ≤ 4)

/-- The exact paper common-radius lower bound is positive. -/
theorem quarticRadius_denominator_pos {x : ℝ} (hx : 2 ≤ x) :
    0 < 1-(x^4)⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hx4 : 1 < x^4 := by nlinarith [sq_nonneg (x^2-2)]
  have hi : (x^4)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).mpr hx4
  linarith

/-- Exact paper normalization bound, retaining sqrt(1+1/n)/(1-n^-4). -/
theorem score_bound_with_quartic_radius_denominator {x t q v s : ℝ}
    (hx : 2 ≤ x) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hq : |q| ≤ v/x) (ht : |t-1| ≤ (x^4)⁻¹)
    (hscore : s^2 ≤ (q+v)/t^2) :
    s ≤ Real.sqrt v * Real.sqrt (1+1/x)/(1-(x^4)⁻¹) := by
  have hx0 : 0 < x := by linarith
  have hb := quarticRadius_denominator_pos hx
  have htlo : 1-(x^4)⁻¹ ≤ t := by have h := (abs_le.mp ht).1; linarith
  have ht0 : 0 < t := hb.trans_le htlo
  have hq' : q+v ≤ v*(1+1/x) := by
    calc
      _ ≤ v/x+v := add_le_add ((le_abs_self q).trans hq) le_rfl
      _ = _ := by ring
  apply (sq_le_sq₀ hs (by positivity)).mp
  rw [div_pow, mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (by positivity : 0 ≤ 1+1/x)]
  calc
    _ ≤ (q+v)/t^2 := hscore
    _ ≤ (v*(1+1/x))/t^2 := div_le_div_of_nonneg_right hq' (sq_nonneg _)
    _ ≤ _ := by gcongr

theorem quarticRadius_score_factor_le {x : ℝ} (hx : 2 ≤ x) :
    Real.sqrt (1+1/x)/(1-(x^4)⁻¹) ≤ (1+1/x)^2 := by
  have hx0 : 0 < x := by linarith
  have hb := quarticRadius_denominator_pos hx
  have he : |(1-(x^4)⁻¹)-1| ≤ (x^2)⁻¹ := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
    exact inverse_fourth_power_le_inverse_square hx
  have hi := (radial_good_inverse hx he).2
  have hr : Real.sqrt (1+1/x) ≤ 1+1/x := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [show 0 ≤ 1/x by positivity]
  calc
    _ = Real.sqrt (1+1/x)*(1/(1-(x^4)⁻¹)) := by ring
    _ ≤ (1+1/x)*(1+1/x) := mul_le_mul hr hi (by positivity) (by positivity)
    _ = _ := by ring

/-- Sharp mesh and one n^-4 radial event transfer the actual net to every continuous product basis. -/
theorem all_product_score_bound_quartic_radius {d n : Nat} (hd : 2 ≤ d) (hn : 2 ≤ n)
    (J : Finset Nat) (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1)
    (S : Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (hS : ∀ W ∈ S, W ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (hcover : ∀ U : Fin n → LocalUnitary d, ∃ W ∈ S,
      ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ) (tensorUnitaryMatrix d n U-W)‖ ≤
        n*kernelPackingMesh d n J θ)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (x : (Fin 2 × QuditIndex d n) → ℝ)
    (hgood : ∀ W ∈ S, |quditQuartic d n J θ W x| ≤ kernelVarianceScale d n J θ/n)
    (hrad : |gaussianRadius (QuditIndex d n) x-1| ≤ ((n:ℝ)^4)⁻¹) :
    ∀ U : Fin n → LocalUnitary d,
      (quditSphereScore d n J θ (tensorUnitaryMatrix d n U)
        (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)))^2 ≤
      (Real.sqrt (1+1/(n:ℝ))/(1-((n:ℝ)^4)⁻¹)+1/(n:ℝ))^2 *
        kernelVarianceScale d n J θ := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have ht := (radial_good_inverse hnR (hrad.trans (inverse_fourth_power_le_inverse_square hnR))).1
  have hx : complexGaussianLift (QuditIndex d n) x ≠ 0 := by
    intro hz
    rw [gaussianRadius_eq_norm_sq, hz] at ht
    norm_num at ht
  let ψ : EuclideanSpace ℂ (QuditIndex d n) := sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)
  have hψ : ‖ψ‖ = 1 := mem_sphere_zero_iff_norm.mp (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)).property
  have hv := kernelVarianceScale_nonneg d n J θ
  intro U
  obtain ⟨W, hW, hdist⟩ := hcover U
  have hpaper := score_bound_with_quartic_radius_denominator hnR hv
      (sphereScore_nonneg W (signedHammingKernel d n J θ) ψ) (hgood W hW) hrad
      (qudit_direction_score_sq_le hd J hJ θ hθ W (hS W hW) e₀ x hx)
  have hdist' := mul_le_mul_of_nonneg_left hdist
    (show 0 ≤ 2*kernelWeightL1 J θ*Real.sqrt ((d:ℝ)^n) by have h := kernelWeightL1_nonneg J θ; positivity)
  rw [kernelPackingMesh_transfer_scale hd (by omega) J θ hθ] at hdist'
  have hscore := (quditSphereScore_lipschitz_via_l1 hd J hJ θ (tensorUnitaryMatrix d n U) W
    (tensorUnitaryMatrix_unitary d n U) (hS W hW) ψ hψ).trans (add_le_add hpaper hdist')
  have hs : quditSphereScore d n J θ (tensorUnitaryMatrix d n U) ψ ≤
      Real.sqrt (kernelVarianceScale d n J θ) *
        (Real.sqrt (1+1/(n:ℝ))/(1-((n:ℝ)^4)⁻¹)+1/(n:ℝ)) := by
    convert hscore using 1 <;> ring
  have hb := quarticRadius_denominator_pos hnR
  have hn0 : (0:ℝ) < n := by linarith
  have hs2 := (sq_le_sq₀
    (sphereScore_nonneg (tensorUnitaryMatrix d n U) (signedHammingKernel d n J θ) ψ)
    (show 0 ≤ Real.sqrt (kernelVarianceScale d n J θ) *
      (Real.sqrt (1+1/(n:ℝ))/(1-((n:ℝ)^4)⁻¹)+1/(n:ℝ)) by positivity)).mpr hs
  simpa only [mul_pow, Real.sq_sqrt hv, mul_comm, quditSphereScore, ψ] using hs2

/-- Sharp mesh and one n^-4 radial event transfer the actual net to every continuous product basis. -/
theorem all_product_score_of_net_good_quartic_radius {d n : Nat} (hd : 2 ≤ d) (hn : 2 ≤ n)
    (J : Finset Nat) (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1)
    (S : Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (hS : ∀ W ∈ S, W ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (hcover : ∀ U : Fin n → LocalUnitary d, ∃ W ∈ S,
      ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ) (tensorUnitaryMatrix d n U-W)‖ ≤
        n*kernelPackingMesh d n J θ)
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (x : (Fin 2 × QuditIndex d n) → ℝ)
    (hgood : ∀ W ∈ S, |quditQuartic d n J θ W x| ≤ kernelVarianceScale d n J θ/n)
    (hrad : |gaussianRadius (QuditIndex d n) x-1| ≤ ((n:ℝ)^4)⁻¹) :
    ∀ U : Fin n → LocalUnitary d,
      (quditSphereScore d n J θ (tensorUnitaryMatrix d n U)
        (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)))^2 ≤
      (1+16/n)*kernelVarianceScale d n J θ := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hb := quarticRadius_denominator_pos hnR
  have hf := score_factor_sixteen (v := 1)
    (s := Real.sqrt (1+1/(n:ℝ))/(1-((n:ℝ)^4)⁻¹)+1/(n:ℝ))
    hnR (by norm_num) (by positivity) (by
      simp only [Real.sqrt_one, one_mul]
      linarith only [quarticRadius_score_factor_le hnR])
  simp only [mul_one] at hf
  intro U
  exact (all_product_score_bound_quartic_radius hd hn J hJ θ hθ S hS hcover e₀ x hgood hrad U).trans
    (mul_le_mul_of_nonneg_right hf (kernelVarianceScale_nonneg d n J θ))

/-- The actual canonical sphere probability of failure for any product basis is cubically small. -/
theorem allProductSphereGood_exception_two_quartic_radius {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ N : Nat, ∀ n ≥ N,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (allProductSphereGood d n J θ)ᶜ ≤
      2*ENNReal.ofReal (Real.exp (-(Real.log d/8)*(n:ℝ)^3)) := by
  obtain ⟨K, _, N, hN⟩ := Consumers.actual_net_and_radius_package_via_frobenius_packing hd J θ hθ
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
  have hrad : |gaussianRadius (QuditIndex d n) x-1| ≤ ((n:ℝ)^4)⁻¹ := (lt_of_not_ge hb.2).le
  exact hx (all_product_score_of_net_good_quartic_radius hd hn2 J hJ θ hθ S hS hcover e₀ x hgood hrad)

/-- The uniform product-basis score bound on the standard sphere, with C=16 and c=log(d)/16. -/
theorem uniform_product_score_standard_sphere_via_packing {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ N : Nat, ∀ n ≥ N,
      canonicalSphereMeasure (EuclideanSpace ℂ (QuditIndex d n)) (allProductSphereGood d n J θ)ᶜ ≤
      ENNReal.ofReal (Real.exp (-(Real.log d/16)*(n:ℝ)^3)) := by
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  have ha : 0 < Real.log d/8 := div_pos (Real.log_pos hdR) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := allProductSphereGood_exception_two_quartic_radius hd J θ hθ
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (eventually_two_mul_exp_cubic ha)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  apply (hN₁ n ((le_max_left _ _).trans hn)).trans
  have h := ENNReal.ofReal_le_ofReal (hN₂ n ((le_max_right _ _).trans hn))
  have he : (Real.log d/8)/2 = Real.log d/16 := by ring
  simpa only [he, ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat] using h


end CertificationGaussian
