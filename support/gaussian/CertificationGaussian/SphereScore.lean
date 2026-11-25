import CertificationGaussian.SphereTransport
import CertificationGaussian.KernelOperator

noncomputable section
open MeasureTheory Metric
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual Born probabilities of the conjugate-transpose basis action. -/
def basisProbability (U : Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) (i : I) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.conjTranspose ψ i‖^2

@[fun_prop] theorem basisProbability_continuous (U : Matrix I I ℂ) : Continuous (basisProbability U) := by
  unfold basisProbability
  fun_prop

theorem basisProbability_apply (U : Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) (i : I) :
    basisProbability U ψ i = Complex.normSq (U.conjTranspose.mulVec (WithLp.ofLp ψ) i) := by
  rw [basisProbability, Complex.sq_norm]
  rfl

theorem basis_action_norm (U : Matrix I I ℂ) (hU : U ∈ unitary (Matrix I I ℂ)) (ψ : EuclideanSpace ℂ I) :
    ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.conjTranspose ψ‖ = ‖ψ‖ :=
  (matrixUnitaryRealIsometry U.conjTranspose (Unitary.star_mem hU)).norm_map ψ

theorem basisProbability_sum (U : Matrix I I ℂ) (hU : U ∈ unitary (Matrix I I ℂ)) (ψ : EuclideanSpace ℂ I) :
    ∑ i, basisProbability U ψ i = ‖ψ‖^2 := by
  rw [← basis_action_norm U hU ψ, EuclideanSpace.norm_sq_eq]
  rfl

/-- The adjoint action has the same genuine Euclidean operator distance. -/
theorem basis_action_difference_norm (U V : Matrix I I ℂ) :
    ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U.conjTranspose-V.conjTranspose)‖ =
      ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
  rw [← Matrix.conjTranspose_sub]
  change ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (star (U-V))‖ = _
  rw [map_star]
  exact norm_star (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V))

/-- A simple coordinate estimate is enough for the finer product-net mesh. -/
theorem basisProbability_coordinate_difference (U V : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (hV : V ∈ unitary (Matrix I I ℂ))
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) (i : I) :
    |basisProbability U ψ i-basisProbability V ψ i| ≤
      2*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
  let a := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.conjTranspose ψ
  let b := Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) V.conjTranspose ψ
  have ha : ‖a i‖ ≤ 1 := by
    exact (PiLp.norm_apply_le a i).trans_eq ((basis_action_norm U hU ψ).trans hψ)
  have hb : ‖b i‖ ≤ 1 := by
    exact (PiLp.norm_apply_le b i).trans_eq ((basis_action_norm V hV ψ).trans hψ)
  have hab : ‖a i-b i‖ ≤ ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
    have he : a-b = Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U.conjTranspose-V.conjTranspose) ψ := by
      simp [a, b, map_sub]
    calc
      _ ≤ ‖a-b‖ := PiLp.norm_apply_le (a-b) i
      _ ≤ ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
        rw [he]
        have h := (Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U.conjTranspose-V.conjTranspose)).le_opNorm ψ
        simpa only [hψ, mul_one, basis_action_difference_norm] using h
  change |‖a i‖^2-‖b i‖^2| ≤ _
  rw [show ‖a i‖^2-‖b i‖^2 = (‖a i‖-‖b i‖)*(‖a i‖+‖b i‖) by ring, abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖a i-b i‖ * 2 := mul_le_mul (abs_norm_sub_norm_le _ _) (by linarith)
      (by positivity) (norm_nonneg _)
    _ ≤ _ := by nlinarith [hab]

omit [DecidableEq I] in
/-- A coordinate bound gives a Euclidean bound with the explicit square-root dimension factor. -/
theorem real_vector_norm_le_of_abs_le (f : I → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, |f i| ≤ C) : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ I)‖ ≤ Real.sqrt (Fintype.card I)*C := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _i : I, C^2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs, PiLp.toLp_apply] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (h i)
    _ = _ := by simp

theorem basisProbability_norm_difference (U V : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (hV : V ∈ unitary (Matrix I I ℂ))
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) :
    ‖(WithLp.toLp 2 (basisProbability U ψ-basisProbability V ψ) : EuclideanSpace ℝ I)‖ ≤
      2*Real.sqrt (Fintype.card I)*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
  have h := real_vector_norm_le_of_abs_le (basisProbability U ψ-basisProbability V ψ)
    (show 0 ≤ 2*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ by positivity)
    (basisProbability_coordinate_difference U V hU hV ψ hψ)
  convert h using 1; ring

/-- The actual processed probability minus the uniform vector. -/
def processedProbability (U : Matrix I I ℂ) (R : Matrix I I ℝ) (ψ : EuclideanSpace ℂ I) :
    EuclideanSpace ℝ I :=
  Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R (WithLp.toLp 2 (basisProbability U ψ)) -
    WithLp.toLp 2 (fun _ => (Fintype.card I : ℝ)⁻¹)

def sphereScore (U : Matrix I I ℂ) (R : Matrix I I ℝ) (ψ : EuclideanSpace ℂ I) : ℝ :=
  Real.sqrt (Fintype.card I)*‖processedProbability U R ψ‖

@[fun_prop] theorem sphereScore_continuous (U : Matrix I I ℂ) (R : Matrix I I ℝ) :
    Continuous (sphereScore U R) := by
  unfold sphereScore processedProbability
  fun_prop

theorem sphereScore_nonneg (U : Matrix I I ℂ) (R : Matrix I I ℝ) (ψ : EuclideanSpace ℂ I) :
    0 ≤ sphereScore U R ψ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

theorem sphereScore_sq (U : Matrix I I ℂ) (R : Matrix I I ℝ) (ψ : EuclideanSpace ℂ I) :
    (sphereScore U R ψ)^2 = (Fintype.card I:ℝ)*
      ∑ i, (R.mulVec (basisProbability U ψ) i-(Fintype.card I:ℝ)⁻¹)^2 := by
  rw [sphereScore, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), EuclideanSpace.real_norm_sq_eq]
  rfl

/-- A coarse 2*L*D Lipschitz bound, explicitly in the genuine Euclidean operator metric. -/
theorem sphereScore_lipschitz (U V : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (hV : V ∈ unitary (Matrix I I ℂ))
    (R : Matrix I I ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hR : ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R‖ ≤ L)
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1) :
    sphereScore U R ψ ≤ sphereScore V R ψ +
      2*L*(Fintype.card I:ℝ)*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by
  have he : processedProbability U R ψ-processedProbability V R ψ =
      Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R
        (WithLp.toLp 2 (basisProbability U ψ-basisProbability V ψ)) := by
    simp only [processedProbability, sub_sub_sub_cancel_right]
    exact (map_sub _ _ _).symm
  have hdiff : ‖processedProbability U R ψ-processedProbability V R ψ‖ ≤
      L*(2*Real.sqrt (Fintype.card I)*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖) := by
    rw [he]
    exact ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) R).le_opNorm _).trans
      (mul_le_mul hR (basisProbability_norm_difference U V hU hV ψ hψ) (norm_nonneg _) hL)
  have hnorm : ‖processedProbability U R ψ‖ ≤ ‖processedProbability V R ψ‖ +
      L*(2*Real.sqrt (Fintype.card I)*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖) := by
    calc
      _ = ‖processedProbability V R ψ + (processedProbability U R ψ-processedProbability V R ψ)‖ := by
        congr 1
        abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl hdiff)
  calc
    _ ≤ Real.sqrt (Fintype.card I)*(‖processedProbability V R ψ‖ +
        L*(2*Real.sqrt (Fintype.card I)*‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖)) :=
      mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
    _ = sphereScore V R ψ + 2*L*(Real.sqrt (Fintype.card I))^2*
        ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) (U-V)‖ := by unfold sphereScore; ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]

def quditSphereScore (d n : Nat) (J : Finset Nat) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ) := sphereScore U (signedHammingKernel d n J θ)

theorem quditSphereScore_lipschitz {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U V : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (hV : V ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) (hψ : ‖ψ‖ = 1) :
    quditSphereScore d n J θ U ψ ≤ quditSphereScore d n J θ V ψ +
      2*kernelWeightL1 J θ*(d:ℝ)^n*‖Matrix.toEuclideanCLM (n := QuditIndex d n) (𝕜 := ℂ) (U-V)‖ := by
  simpa only [quditSphereScore, qudit_card, Nat.cast_pow] using
    sphereScore_lipschitz U V hU hV (signedHammingKernel d n J θ) (kernelWeightL1_nonneg J θ)
      (signedHammingKernel_operator_norm hd J hJ θ) ψ hψ

end CertificationGaussian
