import CertificationGaussian.SphereScore
noncomputable section
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem basisProbability_l1_difference_bound (U V : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (hV : V ∈ unitary (Matrix I I ℂ))
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) :
    (∑ i, |basisProbability U ψ i-basisProbability V ψ i|) ≤
      2*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
  let a := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.conjTranspose ψ
  let b := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) V.conjTranspose ψ
  have ha : ‖a‖ = 1 := (basis_action_norm U hU ψ).trans hψ
  have hb : ‖b‖ = 1 := (basis_action_norm V hV ψ).trans hψ
  have hc (i : I) : |basisProbability U ψ i-basisProbability V ψ i| ≤
      ‖a i-b i‖*(‖a i‖+‖b i‖) := by
    change |‖a i‖^2-‖b i‖^2| ≤ _
    rw [show ‖a i‖^2-‖b i‖^2 = (‖a i‖-‖b i‖)*(‖a i‖+‖b i‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
  have hsum : ∑ i, (‖a i‖+‖b i‖)^2 ≤ 4 := by
    calc
      _ ≤ ∑ i, 2*(‖a i‖^2+‖b i‖^2) := Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg (‖a i‖-‖b i‖)])
      _ = 2*(‖a‖^2+‖b‖^2) := by rw [← Finset.mul_sum, Finset.sum_add_distrib, ← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq]
      _ = 4 := by rw [ha, hb]; norm_num
  have he : a-b = Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U.conjTranspose-V.conjTranspose) ψ := by simp [a, b, map_sub]
  have hab : ‖a-b‖ ≤ ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
    rw [he]
    simpa only [hψ, mul_one, basis_action_difference_norm] using
      (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U.conjTranspose-V.conjTranspose)).le_opNorm ψ
  calc
    _ ≤ ∑ i, ‖a i-b i‖*(‖a i‖+‖b i‖) := Finset.sum_le_sum (fun i _ => hc i)
    _ ≤ Real.sqrt (∑ i, ‖a i-b i‖^2)*Real.sqrt (∑ i, (‖a i‖+‖b i‖)^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ ‖a-b‖*2 := by
      have heq : (∑ i, ‖a i-b i‖^2) = ‖a-b‖^2 := by rw [EuclideanSpace.norm_sq_eq]; rfl
      rw [heq, Real.sqrt_sq (norm_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (Real.sqrt_le_sqrt hsum).trans_eq (by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)])
    _ ≤ _ := by linarith

/-- Euclidean probability distance is bounded by the paper's L1 estimate. -/
theorem basisProbability_norm_difference_via_l1 (U V : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (hV : V ∈ unitary (Matrix I I ℂ))
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) :
    ‖(WithLp.toLp 2 (basisProbability U ψ-basisProbability V ψ) : EuclideanSpace ℝ I)‖ ≤
      2*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
  apply le_trans _ (basisProbability_l1_difference_bound U V hU hV ψ hψ)
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [sq_abs, PiLp.toLp_apply, Pi.sub_apply] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i => |basisProbability U ψ i-basisProbability V ψ i|) (fun _ _ => abs_nonneg _)

theorem sphereScore_lipschitz_via_l1 (U V : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (hV : V ∈ unitary (Matrix I I ℂ))
    (R : Matrix I I ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hR : ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R‖ ≤ L)
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) :
    sphereScore U R ψ ≤ sphereScore V R ψ +
      2*L*Real.sqrt (Fintype.card I)*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
  have he : processedProbability U R ψ-processedProbability V R ψ =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R
        (WithLp.toLp 2 (basisProbability U ψ-basisProbability V ψ)) := by
    simp only [processedProbability, sub_sub_sub_cancel_right]
    exact (map_sub _ _ _).symm
  have hdiff : ‖processedProbability U R ψ-processedProbability V R ψ‖ ≤
      L*(2*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖) := by
    rw [he]
    exact ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R).le_opNorm _).trans
      (mul_le_mul hR (basisProbability_norm_difference_via_l1 U V hU hV ψ hψ) (norm_nonneg _) hL)
  have hnorm : ‖processedProbability U R ψ‖ ≤ ‖processedProbability V R ψ‖ +
      L*(2*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖) := by
    calc
      _ = ‖processedProbability V R ψ + (processedProbability U R ψ-processedProbability V R ψ)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl hdiff)
  calc
    _ ≤ Real.sqrt (Fintype.card I)*(‖processedProbability V R ψ‖ +
        L*(2*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖)) :=
      mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
    _ = _ := by unfold sphereScore; ring

theorem sphereScore_abs_lipschitz_via_l1 (U V : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (hV : V ∈ unitary (Matrix I I ℂ))
    (R : Matrix I I ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hR : ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R‖ ≤ L)
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) :
    |sphereScore U R ψ-sphereScore V R ψ| ≤
      2*L*Real.sqrt (Fintype.card I)*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
  have h₁ := sphereScore_lipschitz_via_l1 U V hU hV R hL hR ψ hψ
  have h₂ := sphereScore_lipschitz_via_l1 V U hV hU R hL hR ψ hψ
  have he : ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (V-U)‖ =
      ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
    rw [← neg_sub U V, map_neg, norm_neg]
  rw [he] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem quditSphereScore_lipschitz_via_l1 {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U V : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (hV : V ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) (hψ : ‖ψ‖ = 1) :
    quditSphereScore d n J θ U ψ ≤ quditSphereScore d n J θ V ψ +
      2*kernelWeightL1 J θ*Real.sqrt ((d:ℝ)^n)*‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ) (U-V)‖ := by
  simpa only [quditSphereScore, qudit_card, Nat.cast_pow] using
    sphereScore_lipschitz_via_l1 U V hU hV (signedHammingKernel d n J θ) (kernelWeightL1_nonneg J θ)
      (signedHammingKernel_operator_norm hd J hJ θ) ψ hψ

end CertificationGaussian
