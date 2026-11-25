import CertificationGaussian.ReadoutRadialSpectrum
import CertificationGaussian.Consumers.RadialHighGaussian

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian.Consumers

/-- Actual first and quadratic auxiliary readout moments agree for full Haar and finite Pauli records. -/
theorem haar_pauli_readout_moments_agree (n r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    (rectangularEuclideanCLM (cardinalityReadoutMean 2 (haarBasisRecords 2) id r lam ((2:ℝ)^n) ψ.ofLp)=
      rectangularEuclideanCLM (cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord r lam
        ((2:ℝ)^n) ψ.ofLp)) ∧
    (rectangularEuclideanCLM (cardinalityReadoutAuxiliary 2 (haarBasisRecords 2) id r lam ((2:ℝ)^n) ψ.ofLp)=
      rectangularEuclideanCLM (cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord r lam
        ((2:ℝ)^n) ψ.ofLp)) := by
  have h0 := completePhaseBellFamily_identity
  have hHS := completePhaseBellFamily_hilbertSchmidt
  constructor
  · simpa only [Fintype.card_fin,Nat.cast_ofNat] using (cardinalityHaar_mean_spectrum 2 completePhaseBellFamily 0 h0 hHS (by norm_num) r lam ψ).trans
      (cardinalityPauli_mean_spectrum completePhaseBellFamily 0 h0 hHS (by norm_num) r lam ψ).symm
  · simpa only [Fintype.card_fin,Nat.cast_ofNat] using (cardinalityHaar_auxiliary_spectrum 2 completePhaseBellFamily 0 h0 hHS (by norm_num) r lam ψ).trans
      (cardinalityPauli_auxiliary_spectrum completePhaseBellFamily 0 h0 hHS (by norm_num) r lam ψ).symm

/-- A nontrivial signed two-site fixture has h=-3 and nu=9, not the sum of absolute weights. -/
theorem signed_readout_spectral_centers :
    cardinalityReadoutTraceScale 2 2 1 signedHighRadialWeights= -3 ∧
    cardinalityReadoutTraceScale 2 2 1 (fun j => (signedHighRadialWeights j)^2)=9 := by
  norm_num [cardinalityReadoutTraceScale,signedHighRadialWeights,Fin.sum_univ_succ,Nat.choose]

/-- The genuine signed Haar B for two sites is the actual orbit sum plus 3I. -/
theorem signed_haar_readout_first (ψ : EuclideanSpace ℂ (QuditIndex 2 2)) :
    rectangularEuclideanCLM (cardinalityReadoutMean 2 (haarBasisRecords 2) id 1 signedHighRadialWeights 4 ψ.ofLp)=
      unitarySphereConjugation
        (fun w : Fin 2 → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
        (fun w => radialFirstCoefficient 2 1 signedHighRadialWeights (radialBellSupport 0 w).card) ψ+
        (3:ℂ) • rectangularEuclideanCLM (1:Matrix (QuditIndex 2 2) (QuditIndex 2 2) ℂ) := by
  have h := cardinalityHaar_mean_spectrum 2 completePhaseBellFamily 0 completePhaseBellFamily_identity
    completePhaseBellFamily_hilbertSchmidt (by norm_num) 1 signedHighRadialWeights ψ
  norm_num only [Fintype.card_fin,show (2:ℝ)^2=4 by norm_num] at h
  rw [h,unitarySphereCentered,radialFirstCoefficient_complex_mean 2 1 (by omega)
    signedHighRadialWeights 0 (by norm_num),Fintype.card_fin,signed_readout_spectral_centers.1]
  simp only [Complex.ofReal_neg,Complex.ofReal_ofNat,rectangularEuclideanCLM,map_smul,map_neg,
    neg_smul,sub_neg_eq_add]

/-- The genuine signed Pauli S has the doubled squared-coefficient spectrum, with center 18I. -/
theorem signed_pauli_readout_second_auxiliary (ψ : EuclideanSpace ℂ (QuditIndex 2 2)) :
    rectangularEuclideanCLM (cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord 1
      signedHighRadialWeights 4 ψ.ofLp)=
      unitarySphereConjugation
        (fun w : Fin 2 → Fin 4 => wickTensorMatrix (fun s => completePhaseBellFamily (w s)))
        (fun w => radialSecondCoefficient 2 1 signedHighRadialWeights (radialBellSupport 0 w).card) ψ-
        (18:ℂ) • rectangularEuclideanCLM (1:Matrix (QuditIndex 2 2) (QuditIndex 2 2) ℂ) := by
  have h := cardinalityPauli_auxiliary_spectrum completePhaseBellFamily 0 completePhaseBellFamily_identity
    completePhaseBellFamily_hilbertSchmidt (by norm_num) 1 signedHighRadialWeights ψ
  norm_num only [Fintype.card_fin,show (2:ℝ)^2=4 by norm_num] at h
  rw [h,unitarySphereCentered,radialSecondCoefficient_complex_mean 2 1 (by omega)
    signedHighRadialWeights 0 (by norm_num),Fintype.card_fin,signed_readout_spectral_centers.2]
  norm_num only [show (2:ℝ)*9=18 by norm_num,Complex.ofReal_ofNat]
  simp only [rectangularEuclideanCLM,map_smul]

/-- No sites and local dimension one are genuine instances of the actual readout identity. -/
theorem no_sites_dimension_one_spectrum (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex 1 0)) :
    rectangularEuclideanCLM (cardinalityReadoutMean 1 (haarBasisRecords 1) id r lam 1 ψ.ofLp)=
      unitarySphereCentered (fun _w : Fin 0 → Fin 1 =>
        wickTensorMatrix (fun _s : Fin 0 => (1:Matrix (Fin 1) (Fin 1) ℂ)))
        (fun w => radialFirstCoefficient 1 r lam (radialBellSupport 0 w).card) ψ := by
  apply cardinalityHaar_mean_spectrum 1 (fun _ : Fin 1 => 1) 0 rfl
  · intro u v
    fin_cases u
    fin_cases v
    norm_num [Matrix.trace,Matrix.diag_apply]
  · norm_num

end CertificationGaussian.Consumers
