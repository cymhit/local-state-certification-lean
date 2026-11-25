import CertificationGaussian.PackingNetAsymptotics
import CertificationGaussian.ReadoutRadialControl

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal
namespace CertificationGaussian.Consumers

/-- One actual product net and the one shared radial event have a joint cubic exceptional bound. -/
theorem actual_net_and_radius_package_via_frobenius_packing {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : Nat, ∀ n ≥ N,
      ∃ S : Finset (Matrix (QuditIndex d n) (QuditIndex d n) ℂ),
        (∀ W ∈ S, W ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) ∧
        (S.card:ℝ) ≤ Real.exp (K*(n:ℝ)^2) ∧
        (∀ U : Fin n → LocalUnitary d, ∃ W ∈ S,
          ‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ) (tensorUnitaryMatrix d n U-W)‖ ≤
            n*kernelPackingMesh d n J θ) ∧
        (pairedGaussian (QuditIndex d n))
          ({x | ∃ W ∈ S, kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ W x|} ∪
            {x | ((n:ℝ)^4)⁻¹ ≤ |gaussianRadius (QuditIndex d n) x - 1|}) ≤
        2*ENNReal.ofReal (Real.exp (-(Real.log d/8)*(n:ℝ)^3)) := by
  obtain ⟨K, hK, N₁, hN₁⟩ := actual_kernel_net_cubic_via_frobenius_packing hd J θ hθ
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (quditRadius_power_eventually_cubic hd 4)
  refine ⟨K, hK, max N₁ N₂, ?_⟩
  intro n hn
  obtain ⟨_, S, hS, hcard, hcover, hprob⟩ := hN₁ n ((le_max_left _ _).trans hn)
  have hr := hN₂ n ((le_max_right _ _).trans hn)
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  have hlog := Real.log_pos hdR
  have hexp : ENNReal.ofReal (Real.exp (-(Real.log d/4)*(n:ℝ)^3)) ≤
      ENNReal.ofReal (Real.exp (-(Real.log d/8)*(n:ℝ)^3)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hn3 : 0 ≤ (n:ℝ)^3 := by positivity
    nlinarith [mul_nonneg hlog.le hn3]
  refine ⟨S, hS, hcard, hcover, ?_⟩
  calc
    _ ≤ (pairedGaussian (QuditIndex d n))
        {x | ∃ W ∈ S, kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ W x|} +
        (pairedGaussian (QuditIndex d n))
        {x | ((n:ℝ)^4)⁻¹ ≤ |gaussianRadius (QuditIndex d n) x - 1|} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(Real.log d/8)*(n:ℝ)^3)) +
        ENNReal.ofReal (Real.exp (-(Real.log d/8)*(n:ℝ)^3)) := add_le_add hprob (hr.trans hexp)
    _ = _ := (two_mul _).symm

end CertificationGaussian.Consumers
