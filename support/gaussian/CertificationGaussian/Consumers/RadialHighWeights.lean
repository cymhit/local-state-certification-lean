import CertificationGaussian.RadialHighWeights

noncomputable section
open scoped BigOperators
namespace CertificationGaussian.Consumers

/-- A fixed constant precedes all weights for both original sequences; signed coefficients are unrestricted. -/
theorem radial_sequences_uniformly_bounded (d r : ℕ) (hd : 1≤d) (lam : ℕ → ℝ) :
    (∃ C : ℝ,0<C ∧ ∀ w : ℕ,|radialFirstCoefficient d r lam w|≤C) ∧
    (∃ C : ℝ,0<C ∧ ∀ w : ℕ,|radialSecondCoefficient d r lam w|≤C) :=
  ⟨radialFirstCoefficient_bounded d r hd lam,radialSecondCoefficient_bounded d r hd lam⟩

/-- The actual truncated full two-level label family has the predicted polynomially small supremum norm. -/
theorem signed_high_weight_norm (n : ℕ) (hn : 1≤n) :
    ‖radialFirstHighWeights (S:=Fin n) 2 1 (fun j => if j=0 then 1 else -2) (0:Fin 4)‖ ≤
      5*((n:ℝ)^25)⁻¹ := by
  have h := radialFirstHighWeights_norm_le (S:=Fin n) 2 1 (by omega) (by simpa using hn)
    (fun j => if j=0 then 1 else -2) (0:Fin 4)
  norm_num [radialCoefficientPolynomialConstant,Fin.sum_univ_succ] at h ⊢
  exact h

/-- The actual normalized square mass has no exponential dimension loss. -/
theorem signed_high_weight_variance_scale (n : ℕ) (hn : 1≤n) :
    Real.sqrt ((∑ w : Fin n → Fin 4,
      (radialFirstHighWeights 2 1 (fun j => if j=0 then 1 else -2) 0 w)^2)/(2:ℝ)^n) ≤
      Real.sqrt 15*((n:ℝ)^12)⁻¹ := by
  have h := radialFirstHighWeights_sqrt_square_mass (S:=Fin n) 2 1 (by omega) (by simpa using hn)
    (fun j => if j=0 then 1 else -2) (0:Fin 4) (by norm_num)
  norm_num [radialCoefficientPolynomialConstant,complementLambdaCoefficient,Fin.sum_univ_succ] at h ⊢
  exact h

/-- The second operator uses the original squared coefficients and its factor two. -/
theorem signed_second_high_weight_variance_scale (n : ℕ) (hn : 1≤n) :
    Real.sqrt ((∑ w : Fin n → Fin 4,
      (radialSecondHighWeights 2 1 (fun j => if j=0 then 1 else -2) 0 w)^2)/(2:ℝ)^n) ≤
      2*Real.sqrt 45*((n:ℝ)^12)⁻¹ := by
  have h := radialSecondHighWeights_sqrt_square_mass (S:=Fin n) 2 1 (by omega) (by simpa using hn)
    (fun j => if j=0 then 1 else -2) (0:Fin 4) (by norm_num)
  norm_num [radialCoefficientPolynomialConstant,complementLambdaCoefficient,Fin.sum_univ_succ] at h ⊢
  exact h

/-- The Gaussian centering scalar for the same actual signed high operator has at most linear growth. -/
theorem signed_high_weight_mean (n : ℕ) (hn : 1≤n) :
    |(∑ w : Fin n → Fin 4,radialFirstHighWeights 2 1 (fun j => if j=0 then 1 else -2) 0 w)/(2:ℝ)^n|≤3*n := by
  have h := radialFirstHighWeights_mean_abs_le (S:=Fin n) 2 1 (by omega) (by simpa using hn)
    (fun j => if j=0 then 1 else -2) (0:Fin 4) (by norm_num)
  norm_num [complementLambdaCoefficient,Fin.sum_univ_succ] at h ⊢
  exact h

/-- The empty-site family has no high labels, and its actual high coefficient function vanishes. -/
theorem high_weights_empty_sites (d r : ℕ) (lam : ℕ → ℝ) :
    radialFirstHighWeights (S:=Fin 0) d r lam (0:Fin 4)=0 := by
  funext w
  simp [radialFirstHighWeights,radialBellSupport]

/-- Zero original coefficients give zero actual truncated weights. -/
theorem high_weights_zero_coefficients (d n r : ℕ) :
    radialFirstHighWeights (S:=Fin n) d r (fun _ => 0) (0:Fin 4)=0 := by
  funext w
  simp [radialFirstHighWeights,radialFirstCoefficient]

/-- The original cutoff does not assume a support count beyond the physical site count. -/
theorem high_weights_cutoff_above_sites (d n r : ℕ) (lam : ℕ → ℝ)
    (h : n≤radialWeightCutoff d r n) :
    radialFirstHighWeights (S:=Fin n) d r lam (0:Fin 4)=0 := by
  funext w
  have hw : (radialBellSupport 0 w).card≤n := by simpa using Finset.card_le_univ (radialBellSupport 0 w)
  simp only [radialFirstHighWeights,Fintype.card_fin,Pi.zero_apply]
  exact ite_eq_right (by omega)

end CertificationGaussian.Consumers
