import CertificationGaussian.ReadoutChoiAction
import CertificationGaussian.RadialCoefficientMass

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator
namespace CertificationGaussian

/-- The original first radial weight mean is the actual signed readout trace center. -/
theorem radialFirstCoefficient_complex_mean {S K : Type*} [Fintype S] [DecidableEq S]
    [Fintype K] [DecidableEq K] (d r : ℕ) (hd : 0<d) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    (∑ w : S → K,(radialFirstCoefficient d r lam (radialBellSupport k0 w).card:ℂ))/
      (Fintype.card (S → Fin d):ℂ)=(cardinalityReadoutTraceScale d (Fintype.card S) r lam:ℂ) := by
  have h := congrArg Complex.ofReal (radialFirstCoefficient_sum (S:=S) d r lam k0 hcard)
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast] at h
  rw [h]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  have hD : (d:ℂ)^(Fintype.card S)≠0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hd)
  field_simp

/-- The original second weight mean is precisely twice the true squared-kernel trace scale. -/
theorem radialSecondCoefficient_complex_mean {S K : Type*} [Fintype S] [DecidableEq S]
    [Fintype K] [DecidableEq K] (d r : ℕ) (hd : 0<d) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=d^2) :
    (∑ w : S → K,(radialSecondCoefficient d r lam (radialBellSupport k0 w).card:ℂ))/
      (Fintype.card (S → Fin d):ℂ)=
      (2*cardinalityReadoutTraceScale d (Fintype.card S) r (fun j => (lam j)^2):ℝ) := by
  simp only [radialSecondCoefficient,Complex.ofReal_mul,Complex.ofReal_ofNat,
    ← Finset.mul_sum,mul_div_assoc,radialFirstCoefficient_complex_mean d r hd _ k0 hcard]

/-- The genuine B operator equals the original full c-weighted orbit sum with its actual h center. -/
theorem cardinalityReadoutMean_spectrum {S K Ω : Type*} [Fintype S] [DecidableEq S]
    [Fintype K] [DecidableEq K] [MeasurableSpace Ω] [TopologicalSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [SecondCountableTopology Ω]
    (d : ℕ) (hd : 0<d) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (hmean : ∀ a b : Fin d,(d:ℂ)*(∫ ω,recordedProjector d (record ω) a b∂μ)=
      (1:Matrix (Fin d) (Fin d) ℂ) a b)
    (hentry : ∀ i a j b : Fin d,
      ((d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*recordedProjector d (record ω) j i∂μ)=
        radialChoiA0 d (i,a) (j,b)) ∧
      ((d:ℂ)*(∫ ω,recordedProjector d (record ω) a b*(1-recordedProjector d (record ω)) j i∂μ)=
        (d:ℂ)*radialChoiR0 d (i,a) (j,b)))
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (S → Fin d)) :
    rectangularEuclideanCLM (cardinalityReadoutMean d μ record r lam ((d:ℝ)^(Fintype.card S)) ψ.ofLp)=
      unitarySphereCentered (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
        (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ := by
  have hnorm := productRecordedProjector_mean (S:=S) d μ record hr hmean
  have hb := readoutMeanOperator_choi (Measure.pi (fun _ : S => μ))
    (productRecordedProjector d record) (cardinalityReadoutKernel d record r lam)
    (productRecordedProjector_continuous d record hr) (finiteComplementKernel_continuous d record hr _ _)
    (cardinalityReadoutTraceScale d (Fintype.card S) r lam)
    (by simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using hnorm) ψ.ofLp
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] at hb
  rw [cardinalityReadoutChoi_eq d μ record hr hentry r lam,
    ← radialFirstCoefficient_bell_matrix d hd W k0 h0 hHS hcard r lam] at hb
  change rectangularEuclideanCLM (readoutMeanOperator _ _ _ _ _ _ _)=_
  have hsub (A B : Matrix (S → Fin d) (S → Fin d) ℂ) :
      rectangularEuclideanCLM (A-B)=rectangularEuclideanCLM A-rectangularEuclideanCLM B := by
    simp only [rectangularEuclideanCLM,map_sub]
  rw [hb,hsub,choiVectorAction_weightedBell_clm]
  unfold unitarySphereCentered
  rw [radialFirstCoefficient_complex_mean d r hd lam k0 hcard]
  congr 1

/-- Actual full-Haar B, with the required twirl and normalization supplied by the genuine complete record law. -/
theorem cardinalityHaar_mean_spectrum {S K : Type*} [Fintype S] [DecidableEq S]
    [Fintype K] [DecidableEq K] (d : ℕ) [NeZero d]
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (S → Fin d)) :
    rectangularEuclideanCLM (cardinalityReadoutMean d (haarBasisRecords d) id r lam
      ((d:ℝ)^(Fintype.card S)) ψ.ofLp)=
      unitarySphereCentered (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
        (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ :=
  cardinalityReadoutMean_spectrum d (Nat.pos_of_ne_zero (NeZero.ne d)) (haarBasisRecords d) id continuous_id
    (haarBasisRecords_projector_mean d) (haarBasisRecords_choi_entries d) W k0 h0 hHS hcard r lam ψ

/-- Actual finite-Pauli B has the identical original radial spectrum. -/
theorem cardinalityPauli_mean_spectrum {S K : Type*} [Fintype S] [DecidableEq S]
    [Fintype K] [DecidableEq K]
    (W : K → Matrix (Fin 2) (Fin 2) ℂ) (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0)
    (hcard : Fintype.card K=4) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (S → Fin 2)) :
    rectangularEuclideanCLM (cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord r lam
      ((2:ℝ)^(Fintype.card S)) ψ.ofLp)=
      unitarySphereCentered (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
        (fun w => radialFirstCoefficient 2 r lam (radialBellSupport k0 w).card) ψ :=
  cardinalityReadoutMean_spectrum 2 (by norm_num) pauliBasisRecords pauliFullRecord continuous_of_discreteTopology
    pauliBasisRecords_projector_mean pauliBasisRecords_choi_entries W k0 h0 hHS (by simpa using hcard) r lam ψ

/-- Squaring the actual cardinality kernel makes the auxiliary operator exactly twice the first moment for lambda squared. -/
theorem cardinalityReadoutAuxiliary_eq_two_mean {S Ω : Type*} [Fintype S] [DecidableEq S]
    [MeasurableSpace Ω] (d : ℕ) (μ : Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (r : ℕ) (lam : ℕ → ℝ)
    (qscale : ℝ) (z : (S → Fin d) → ℂ) :
    cardinalityReadoutAuxiliary d μ record r lam qscale z=
      (2:ℂ) • cardinalityReadoutMean d μ record r (fun j => (lam j)^2) qscale z := by
  unfold cardinalityReadoutAuxiliary cardinalityReadoutMean readoutAuxiliaryOperator
    readoutMeanOperator readoutCenteredScore
  simp_rw [cardinalityReadoutKernel_sq,mul_smul]
  rw [integral_smul,smul_comm]

/-- Real rescaling of the actual centered sphere operator, including its true scalar center. -/
theorem unitarySphereCentered_weight_smul {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    (W : K → Matrix I I ℂ) (a : K → ℝ) (c : ℝ) (ψ : EuclideanSpace ℂ I) :
    unitarySphereCentered W (fun w => c*a w) ψ=(c:ℂ) • unitarySphereCentered W a ψ := by
  have hk : unitaryWeightedRankOne W (fun w => c*a w) ψ.ofLp=
      (c:ℂ) • unitaryWeightedRankOne W a ψ.ofLp := by
    unfold unitaryWeightedRankOne
    simp only [Complex.ofReal_mul,mul_smul,← Finset.smul_sum]
    exact smul_comm _ _ _
  have hm : rectangularEuclideanCLM
      (((∑ w,((c*a w:ℝ):ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ))=
      (c:ℂ) • rectangularEuclideanCLM
        (((∑ w,(a w:ℂ))/(Fintype.card I:ℂ)) • (1:Matrix I I ℂ)) := by
    simp only [Complex.ofReal_mul,← Finset.mul_sum,mul_div_assoc,mul_smul,
      rectangularEuclideanCLM,map_smul]
  unfold unitarySphereCentered unitarySphereConjugation
  rw [hk,hm,smul_sub,smul_comm (Fintype.card I:ℂ) (c:ℂ)]
  simp only [rectangularEuclideanCLM,map_smul]

/-- Actual Haar S has exactly the original e=2c(lambda squared) spectrum, including the 2 nu center. -/
theorem cardinalityHaar_auxiliary_spectrum {S K : Type*} [Fintype S] [DecidableEq S]
    [Fintype K] [DecidableEq K] (d : ℕ) [NeZero d]
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (S → Fin d)) :
    rectangularEuclideanCLM (cardinalityReadoutAuxiliary d (haarBasisRecords d) id r lam
      ((d:ℝ)^(Fintype.card S)) ψ.ofLp)=
      unitarySphereCentered (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
        (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ := by
  rw [cardinalityReadoutAuxiliary_eq_two_mean]
  have hs (M : Matrix (S → Fin d) (S → Fin d) ℂ) :
      rectangularEuclideanCLM ((2:ℂ) • M)=(2:ℂ) • rectangularEuclideanCLM M := by
    simp only [rectangularEuclideanCLM,map_smul]
  rw [hs,cardinalityHaar_mean_spectrum d W k0 h0 hHS hcard r (fun j => (lam j)^2) ψ]
  exact (unitarySphereCentered_weight_smul _ _ 2 ψ).symm

/-- Actual finite-Pauli S, with no residual local moment or spectral-identity premise. -/
theorem cardinalityPauli_auxiliary_spectrum {S K : Type*} [Fintype S] [DecidableEq S]
    [Fintype K] [DecidableEq K]
    (W : K → Matrix (Fin 2) (Fin 2) ℂ) (k0 : K) (h0 : W k0=1)
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0)
    (hcard : Fintype.card K=4) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (S → Fin 2)) :
    rectangularEuclideanCLM (cardinalityReadoutAuxiliary 2 pauliBasisRecords pauliFullRecord r lam
      ((2:ℝ)^(Fintype.card S)) ψ.ofLp)=
      unitarySphereCentered (fun w : S → K => wickTensorMatrix (fun s => W (w s)))
        (fun w => radialSecondCoefficient 2 r lam (radialBellSupport k0 w).card) ψ := by
  rw [cardinalityReadoutAuxiliary_eq_two_mean]
  have hs (M : Matrix (S → Fin 2) (S → Fin 2) ℂ) :
      rectangularEuclideanCLM ((2:ℂ) • M)=(2:ℂ) • rectangularEuclideanCLM M := by
    simp only [rectangularEuclideanCLM,map_smul]
  rw [hs,cardinalityPauli_mean_spectrum W k0 h0 hHS hcard r (fun j => (lam j)^2) ψ]
  exact (unitarySphereCentered_weight_smul _ _ 2 ψ).symm

end CertificationGaussian
