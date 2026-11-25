import CertificationGaussian.TailAsymptotics

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal
namespace CertificationGaussian.Consumers

/-- c and N are chosen before n and before every basis; the radius event is shared by all bases. -/
theorem actual_cubic_tail_package {d : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : Nat, ∀ n ≥ N,
      (pairedGaussian (QuditIndex d n))
        {x | ((n:ℝ)^2)⁻¹ ≤ |gaussianRadius (QuditIndex d n) x - 1|} ≤
        ENNReal.ofReal (Real.exp (-c*(n:ℝ)^3)) ∧
      ∀ U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ,
        U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) →
        (pairedGaussian (QuditIndex d n))
          {x | kernelVarianceScale d n J θ / n ≤ |quditQuartic d n J θ U x|} ≤
        ENNReal.ofReal (Real.exp (-c*(n:ℝ)^3)) := by
  have hdR : (1:ℝ) < d := by exact_mod_cast (show 1<d by omega)
  refine ⟨Real.log d / 4, div_pos (Real.log_pos hdR) (by norm_num), ?_⟩
  exact Filter.eventually_atTop.mp ((quditRadius_eventually_cubic hd).and
    (quditQuartic_eventually_cubic hd J θ hθ))

/-- A genuine signed kernel with a negative coefficient consumes the same cubic probability package. -/
theorem signed_kernel_cubic_tail :
    ∀ᶠ n : Nat in atTop, ∀ U : Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ,
      U ∈ unitary (Matrix (QuditIndex 2 n) (QuditIndex 2 n) ℂ) →
      (pairedGaussian (QuditIndex 2 n))
        {x | kernelVarianceScale 2 n {1,2} (fun k => if k=1 then 2 else -1) / n ≤
          |quditQuartic 2 n {1,2} (fun k => if k=1 then 2 else -1) U x|} ≤
      ENNReal.ofReal (Real.exp (-(Real.log 2 / 4)*(n:ℝ)^3)) :=
  quditQuartic_eventually_cubic (by norm_num) {1,2} (fun k => if k=1 then 2 else -1) (by norm_num)

end CertificationGaussian.Consumers
