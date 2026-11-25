import CertificationGaussian.GaussianRotation

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CertificationGaussian
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The quadratic expression in the centered squared complex-coordinate moduli. -/
def complexCenteredQuadratic (B : Matrix I I ℝ) (z : I → ℂ) : ℝ :=
  ∑ i, ∑ j, B i j * (Complex.normSq (z i) - 1) * (Complex.normSq (z j) - 1)

omit [DecidableEq I] in
@[fun_prop] theorem complexCenteredQuadratic_continuous (B : Matrix I I ℝ) :
    Continuous (complexCenteredQuadratic B) := by
  unfold complexCenteredQuadratic
  fun_prop

omit [DecidableEq I] in
theorem complexCenteredQuadratic_coordinates (B : Matrix I I ℝ) (x : (Fin 2 × I) → ℝ) :
    complexCenteredQuadratic B (complexCoordinate x) = blockQuadratic B (blockCoordinates I x) := by
  simp only [complexCenteredQuadratic, complexCoordinate_normSq, add_sub_cancel_right,
    blockQuadratic]

/-- Integrals of any continuous observable obey the actual proved unitary law. -/
theorem complexCoordinate_integral_unitary (A : Matrix I I ℂ)
    (hA : A ∈ unitary (Matrix I I ℂ)) (f : (I → ℂ) → ℝ) (hf : Continuous f) :
    ∫ x, f (A.mulVec (complexCoordinate x)) ∂pairedGaussian I =
      ∫ x, f (complexCoordinate x) ∂pairedGaussian I := by
  have hm : Measurable (fun x : (Fin 2 × I) → ℝ => A.mulVec (complexCoordinate x)) := by
    unfold complexCoordinate Matrix.mulVec dotProduct
    fun_prop
  have hm' : Measurable (complexCoordinate : ((Fin 2 × I) → ℝ) → I → ℂ) := by
    unfold complexCoordinate
    fun_prop
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable,
    complexCoordinate_unitary_map A hA, integral_map hm'.aemeasurable hf.aestronglyMeasurable]

/-- Transport the existing quartic itself, and continuous functions of it, to independent pairs. -/
theorem gaussianQuartic_integral_transport (U : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (R : Matrix I I ℝ) (v : ℝ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ x, f (gaussianQuartic U R v x) ∂pairedGaussian I =
      ∫ z, f ((Fintype.card I : ℝ)⁻¹ * blockQuadratic (R*R) z - v) ∂blockGaussian I := by
  change (∫ x, (fun w => f ((Fintype.card I : ℝ)⁻¹ * complexCenteredQuadratic (R*R) w - v))
    (U.conjTranspose.mulVec (complexCoordinate x)) ∂pairedGaussian I) = _
  rw [complexCoordinate_integral_unitary U.conjTranspose (Unitary.star_mem hU)
    (fun w => f ((Fintype.card I : ℝ)⁻¹ * complexCenteredQuadratic (R*R) w - v)) (by fun_prop)]
  simp_rw [complexCenteredQuadratic_coordinates]
  exact (blockCoordinates_preserving I).integral_comp'
    (fun z : I → ℝ × ℝ => f ((Fintype.card I : ℝ)⁻¹ * blockQuadratic (R*R) z - v))

theorem gaussianQuartic_mean (U : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (R : Matrix I I ℝ) (v : ℝ) :
    ∫ x, gaussianQuartic U R v x ∂pairedGaussian I =
      (Fintype.card I : ℝ)⁻¹ * Matrix.trace (R*R) - v := by
  rw [gaussianQuartic_integral_transport U hU R v (fun x : ℝ => x) continuous_id]
  rw [integral_sub ((blockQuadratic_integrable _).const_mul _) (integrable_const _),
    integral_const_mul, blockQuadratic_mean]
  simp

/-- Actual second moment of the centered quartic, with its centering constant determined by trace. -/
theorem gaussianQuartic_centered_second (U : Matrix I I ℂ)
    (hU : U ∈ unitary (Matrix I I ℂ)) (R : Matrix I I ℝ)
    (hR : ∀ i j, R i j = R j i) :
    ∫ x, (gaussianQuartic U R ((Fintype.card I : ℝ)⁻¹ * Matrix.trace (R*R)) x)^2
      ∂pairedGaussian I =
      (2 * Matrix.trace (R^4) + 6 * ∑ i, ((R*R) i i)^2) / (Fintype.card I : ℝ)^2 := by
  rw [gaussianQuartic_integral_transport U hU R _ (fun x => x^2) (by fun_prop)]
  have he (z : I → ℝ × ℝ) :
      ((Fintype.card I : ℝ)⁻¹ * blockQuadratic (R*R) z -
        (Fintype.card I : ℝ)⁻¹ * Matrix.trace (R*R))^2 =
      ((Fintype.card I : ℝ)⁻¹)^2 * (blockQuadratic (R*R) z - Matrix.trace (R*R))^2 := by ring
  simp_rw [he, integral_const_mul, blockQuadratic_centered_second (R*R) (square_matrix_symm R hR)]
  have hp : (R*R)*(R*R) = R^4 := by
    rw [show (4 : Nat) = 2+2 from rfl, pow_add, pow_two]
  rw [hp]
  simp only [div_eq_mul_inv, inv_pow]
  ring

/-- The signed Hamming quartic has mean zero under the paired Gaussian law. -/
theorem quditQuartic_mean_zero {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) :
    ∫ x, quditQuartic d n J θ U x ∂pairedGaussian (QuditIndex d n) = 0 := by
  have hD : (d^n : ℝ) ≠ 0 := by positivity
  rw [quditQuartic, gaussianQuartic_mean U hU, qudit_card,
    signedHammingKernel_sq_trace hd J hJ θ]
  push_cast
  field_simp
  ring

/-- The second moment of the quartic for an arbitrary unitary basis. -/
theorem quditQuartic_second_moment {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) :
    ∫ x, (quditQuartic d n J θ U x)^2 ∂pairedGaussian (QuditIndex d n) =
      (2 * Matrix.trace ((signedHammingKernel d n J θ)^4) +
        6 * (d^n : ℝ) * (kernelVarianceScale d n J θ)^2) / (d^n : ℝ)^2 := by
  have hD : (d^n : ℝ) ≠ 0 := by positivity
  have hv : kernelVarianceScale d n J θ =
      (Fintype.card (QuditIndex d n) : ℝ)⁻¹ *
        Matrix.trace (signedHammingKernel d n J θ * signedHammingKernel d n J θ) := by
    rw [qudit_card, signedHammingKernel_sq_trace hd J hJ θ]
    push_cast
    field_simp
  unfold quditQuartic
  conv_lhs => arg 2; ext x; rw [hv]
  rw [gaussianQuartic_centered_second U hU _ (signedHammingKernel_symm d n J θ)]
  simp_rw [signedHammingKernel_sq_diag hd J hJ θ]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, qudit_card, Nat.cast_pow]
  ring

/-- A uniform second-moment bound for arbitrary real signed shell weights. -/
theorem quditQuartic_second_moment_le {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) :
    ∫ x, (quditQuartic d n J θ U x)^2 ∂pairedGaussian (QuditIndex d n) ≤
      8 * (kernelWeightL1 J θ)^2 * kernelVarianceScale d n J θ / (d^n : ℝ) := by
  rw [quditQuartic_second_moment hd J hJ θ U hU]
  have hD : (0 : ℝ) < (d:ℝ)^n := by positivity
  have hv := kernelVarianceScale_nonneg d n J θ
  have hvL := kernelVarianceScale_le_weight_sq hd J hJ θ
  have ht := signedHammingKernel_trace_four_le hd J hJ θ
  push_cast at ht
  have hvs : (kernelVarianceScale d n J θ)^2 ≤
      (kernelWeightL1 J θ)^2 * kernelVarianceScale d n J θ := by
    nlinarith [mul_le_mul_of_nonneg_right hvL hv]
  have hn : 2 * Matrix.trace ((signedHammingKernel d n J θ)^4) +
      6 * (d:ℝ)^n * (kernelVarianceScale d n J θ)^2 ≤
      8 * (kernelWeightL1 J θ)^2 * (d:ℝ)^n * kernelVarianceScale d n J θ := by
    nlinarith [mul_le_mul_of_nonneg_left hvs (le_of_lt hD)]
  calc
    _ ≤ (8 * (kernelWeightL1 J θ)^2 * (d:ℝ)^n * kernelVarianceScale d n J θ) /
        ((d:ℝ)^n)^2 := div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ = _ := by field_simp

omit [DecidableEq I] in
@[fun_prop] theorem gaussianQuartic_continuous (U : Matrix I I ℂ)
    (R : Matrix I I ℝ) (v : ℝ) : Continuous (gaussianQuartic U R v) := by
  simpa only [eval_quartic] using (quarticPoly U R v).continuous_eval

/-- Formal variance of the centered actual Model function. -/
theorem quditQuartic_variance {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) :
    variance (quditQuartic d n J θ U) (pairedGaussian (QuditIndex d n)) =
      (2 * Matrix.trace ((signedHammingKernel d n J θ)^4) +
        6 * (d^n : ℝ) * (kernelVarianceScale d n J θ)^2) / (d^n : ℝ)^2 := by
  have hm : Measurable (quditQuartic d n J θ U) := (gaussianQuartic_continuous U _ _).measurable
  rw [variance_eq_integral hm.aemeasurable,
    quditQuartic_mean_zero hd J hJ θ U hU]
  simp only [sub_zero]
  exact quditQuartic_second_moment hd J hJ θ U hU

/-- Restoring the subtracted constant recovers the original uncentered Q_U. -/
theorem quditEnergy_mean {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) :
    ∫ x, gaussianQuartic U (signedHammingKernel d n J θ) 0 x
      ∂pairedGaussian (QuditIndex d n) = kernelVarianceScale d n J θ := by
  have hD : (d^n : ℝ) ≠ 0 := by positivity
  rw [gaussianQuartic_mean U hU, qudit_card, signedHammingKernel_sq_trace hd J hJ θ]
  simp only [sub_zero]
  push_cast
  field_simp

/-- The exact note variance is for Q_U as well as its centered version Q_U - v_n. -/
theorem quditEnergy_variance {d n : Nat} (hd : 2 ≤ d) (J : Finset Nat)
    (hJ : ∀ k ∈ J, k ≤ n) (θ : Nat → ℝ)
    (U : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)
    (hU : U ∈ unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ)) :
    variance (gaussianQuartic U (signedHammingKernel d n J θ) 0)
      (pairedGaussian (QuditIndex d n)) =
      (2 * Matrix.trace ((signedHammingKernel d n J θ)^4) +
        6 * (d^n : ℝ) * (kernelVarianceScale d n J θ)^2) / (d^n : ℝ)^2 := by
  rw [variance_eq_integral (gaussianQuartic_continuous U _ _).measurable.aemeasurable,
    quditEnergy_mean hd J hJ θ U hU]
  have he (x : (Fin 2 × QuditIndex d n) → ℝ) :
      gaussianQuartic U (signedHammingKernel d n J θ) 0 x - kernelVarianceScale d n J θ =
        quditQuartic d n J θ U x := by simp only [gaussianQuartic, quditQuartic, sub_zero]
  simp_rw [he]
  exact quditQuartic_second_moment hd J hJ θ U hU

end CertificationGaussian
