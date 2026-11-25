import CertificationGaussian.SphereScore
import CertificationGaussian.Radial

noncomputable section
open MeasureTheory Metric
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem sum_mulVec_eq_sum (R : Matrix I I ℝ) (hcol : ∀ j, ∑ i, R i j = 1) (y : I → ℝ) :
    ∑ i, R.mulVec y i = ∑ i, y i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hcol, one_mul]

omit [DecidableEq I] in
theorem sum_sq_mulVec (R : Matrix I I ℝ) (hR : ∀ i j, R i j = R j i) (y : I → ℝ) :
    ∑ i, (R.mulVec y i)^2 = ∑ i, ∑ j, (R*R) i j*y i*y j := by
  have hT : R.transpose = R := by ext i j; exact hR j i
  calc
    _ = (R.mulVec y) ⬝ᵥ (R.mulVec y) := by simp only [dotProduct, pow_two]
    _ = y ⬝ᵥ R.transpose.mulVec (R.mulVec y) := (Matrix.dotProduct_transpose_mulVec R y (R.mulVec y)).symm
    _ = y ⬝ᵥ (R*R).mulVec y := by rw [hT, Matrix.mulVec_mulVec]
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

omit [DecidableEq I] in
/-- Exact removal of the constant component; the discarded term is nonnegative. -/
theorem sum_centered_sq (z : I → ℝ) (b : ℝ) (hsum : ∑ i, z i = (Fintype.card I:ℝ)*b) :
    ∑ i, (z i-b)^2 = (∑ i, (z i)^2)-(Fintype.card I:ℝ)*b^2 := by
  have he (i : I) : (z i-b)^2 = (z i)^2-2*b*z i+b^2 := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [DecidableEq I] in
theorem gaussianQuartic_add_eq_norm_square (U : Matrix I I ℂ) (R : Matrix I I ℝ)
    (hR : ∀ i j, R i j = R j i) (v : ℝ) (x : (Fin 2 × I) → ℝ) :
    gaussianQuartic U R v x+v = (Fintype.card I:ℝ)⁻¹ *
      ∑ i, (R.mulVec (gaussianOutcome U.conjTranspose x) i)^2 := by
  rw [sum_sq_mulVec R hR]
  unfold gaussianQuartic
  ring

theorem basisProbability_real_smul (U : Matrix I I ℂ) (ψ : EuclideanSpace ℂ I) (r : ℝ) (i : I) :
    basisProbability U (r • ψ) i = r^2*basisProbability U ψ i := by
  have he : Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.conjTranspose (r • ψ) =
      r • Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.conjTranspose ψ :=
    ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) U.conjTranspose).restrictScalars ℝ).map_smul r ψ
  simp only [basisProbability, he, PiLp.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem basisProbability_direction (U : Matrix I I ℂ) (e₀ : sphere (0 : EuclideanSpace ℂ I) 1)
    (z : EuclideanSpace ℂ I) (hz : z ≠ 0) (i : I) :
    basisProbability U (sphereDirection e₀ z) i = basisProbability U z i / ‖z‖^2 := by
  rw [sphereDirection_coe, ite_eq_right hz, basisProbability_real_smul]
  ring

theorem basisProbability_gaussianLift (U : Matrix I I ℂ) (x : (Fin 2 × I) → ℝ) (i : I) :
    basisProbability U (complexGaussianLift I x) i = gaussianOutcome U.conjTranspose x i+1 := by
  rw [basisProbability_apply]
  simp only [complexGaussianLift, WithLp.ofLp_toLp, gaussianOutcome, sub_add_cancel]

omit [DecidableEq I] in
theorem mulVec_radial_centered (R : Matrix I I ℝ) (hrow : ∀ i, ∑ j, R i j = 1)
    (y : I → ℝ) {D t : ℝ} (hD : D ≠ 0) (ht : t ≠ 0) (i : I) :
    R.mulVec (fun j => (y j+1)/(D*t)) i-D⁻¹ = (R.mulVec y i-(t-1))/(D*t) := by
  simp only [Matrix.mulVec, dotProduct, mul_div, mul_add, mul_one]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hrow]
  field_simp
  ring

variable [Nonempty I]

omit [DecidableEq I] in
theorem gaussianRadius_pos_of_nonzero (x : (Fin 2 × I) → ℝ) (hx : complexGaussianLift I x ≠ 0) :
    0 < gaussianRadius I x := by
  rw [gaussianRadius_eq_norm_sq]
  have hD : (0:ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)) hD

theorem basisProbability_gaussian_direction (U : Matrix I I ℂ)
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) (x : (Fin 2 × I) → ℝ)
    (hx : complexGaussianLift I x ≠ 0) :
    basisProbability U (sphereDirection e₀ (complexGaussianLift I x)) =
      fun i => (gaussianOutcome U.conjTranspose x i+1)/((Fintype.card I:ℝ)*gaussianRadius I x) := by
  funext i
  rw [basisProbability_direction U e₀ _ hx, basisProbability_gaussianLift]
  have hD : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (Fintype.card I:ℝ)*gaussianRadius I x = ‖complexGaussianLift I x‖^2 := by
    rw [gaussianRadius_eq_norm_sq]
    field_simp
  rw [he]

theorem gaussianOutcome_sum (U : Matrix I I ℂ) (hU : U ∈ unitary (Matrix I I ℂ))
    (x : (Fin 2 × I) → ℝ) :
    ∑ i, gaussianOutcome U.conjTranspose x i = (Fintype.card I:ℝ)*(gaussianRadius I x-1) := by
  have he (i : I) : gaussianOutcome U.conjTranspose x i = basisProbability U (complexGaussianLift I x) i-1 := by
    rw [basisProbability_gaussianLift]
    ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, basisProbability_sum U hU]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [gaussianRadius_eq_norm_sq]
  have hD : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- Exact radial projection: the constant component is subtracted, never bounded by an extra triangle term. -/
theorem gaussian_direction_score_identity (U : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (R : Matrix I I ℝ)
    (hR : ∀ i j, R i j = R j i) (hrow : ∀ i, ∑ j, R i j = 1) (hcol : ∀ j, ∑ i, R i j = 1)
    (e₀ : sphere (0 : EuclideanSpace ℂ I) 1) (x : (Fin 2 × I) → ℝ)
    (hx : complexGaussianLift I x ≠ 0) :
    (sphereScore U R (sphereDirection e₀ (complexGaussianLift I x)))^2 =
      (gaussianQuartic U R 0 x-(gaussianRadius I x-1)^2)/(gaussianRadius I x)^2 := by
  have hD : (Fintype.card I:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht := (gaussianRadius_pos_of_nonzero x hx).ne'
  have hsum : ∑ i, R.mulVec (gaussianOutcome U.conjTranspose x) i =
      (Fintype.card I:ℝ)*(gaussianRadius I x-1) := by
    rw [sum_mulVec_eq_sum R hcol, gaussianOutcome_sum U hU]
  have hcenter := sum_centered_sq (R.mulVec (gaussianOutcome U.conjTranspose x)) (gaussianRadius I x-1) hsum
  have hQ : gaussianQuartic U R 0 x = (Fintype.card I:ℝ)⁻¹ *
      ∑ i, (R.mulVec (gaussianOutcome U.conjTranspose x) i)^2 := by
    simpa only [add_zero] using gaussianQuartic_add_eq_norm_square U R hR 0 x
  rw [sphereScore_sq, basisProbability_gaussian_direction U e₀ x hx]
  simp_rw [mulVec_radial_centered R hrow _ hD ht, div_pow]
  rw [← Finset.sum_div, hcenter, hQ]
  field_simp

/-- The projection identity for the signed Hamming kernel and its centered quartic. -/
theorem qudit_direction_score_identity {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (x : (Fin 2 × QuditIndex d n) → ℝ) (hx : complexGaussianLift (QuditIndex d n) x ≠ 0) :
    (quditSphereScore d n J θ U (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)))^2 =
      (quditQuartic d n J θ U x+kernelVarianceScale d n J θ-
        (gaussianRadius (QuditIndex d n) x-1)^2)/(gaussianRadius (QuditIndex d n) x)^2 := by
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hrow : ∀ i, ∑ j, signedHammingKernel d n J θ i j = 1 := by
    intro i
    rw [signedHammingKernel_row_sum hd J hJ θ, hθ]
  have hcol : ∀ j, ∑ i, signedHammingKernel d n J θ i j = 1 := by
    intro j
    calc
      _ = ∑ i, signedHammingKernel d n J θ j i :=
        Finset.sum_congr rfl (fun i _ => signedHammingKernel_symm d n J θ i j)
      _ = 1 := hrow j
  have h := gaussian_direction_score_identity U hU (signedHammingKernel d n J θ)
    (signedHammingKernel_symm d n J θ) hrow hcol e₀ x hx
  simpa only [quditSphereScore, quditQuartic, gaussianQuartic, sub_zero, sub_add_cancel] using h

/-- The discarded constant term only improves the upper bound. -/
theorem qudit_direction_score_sq_le {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ) (hθ : ∑ k ∈ J, θ k = 1)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ))
    (e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1)
    (x : (Fin 2 × QuditIndex d n) → ℝ) (hx : complexGaussianLift (QuditIndex d n) x ≠ 0) :
    (quditSphereScore d n J θ U (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)))^2 ≤
      (quditQuartic d n J θ U x+kernelVarianceScale d n J θ)/(gaussianRadius (QuditIndex d n) x)^2 := by
  rw [qudit_direction_score_identity hd J hJ θ hθ U hU e₀ x hx]
  exact div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) (sq_nonneg _)

end CertificationGaussian
