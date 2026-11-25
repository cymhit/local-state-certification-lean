import LocalCertification.Quantum.PauliProductMeasurement
import LocalCertification.Protocol.IndependentRecords
import CertificationGaussian.CardinalityReadoutMoments
import Mathlib.Probability.Moments.Variance

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Matrix CertificationGaussian
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Quantum

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The actual finite-dimensional complex trace functional used to commute moments and integrals. -/
def matrixTraceLeftCLM (R : Matrix I I ℂ) : Matrix I I ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((Matrix.traceLinearMap I ℂ ℂ).comp (LinearMap.mulLeft ℂ R))

@[simp] theorem matrixTraceLeftCLM_apply (R A : Matrix I I ℂ) :
    matrixTraceLeftCLM R A = Matrix.trace (R * A) := rfl

variable {H : Type*} [MeasurableSpace H] {d n : ℕ}

/-- The same complete-reference law as in the proved actual Born density. -/
def completeBornReference (d n : ℕ) [NeZero d] (μ : Measure H) :
    Measure (H × QuditIndex d n) :=
  let _ : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  μ.prod (finiteUniformMeasure (QuditIndex d n))

instance completeBornReference_probability [NeZero d] (μ : Measure H) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (completeBornReference d n μ) := by
  unfold completeBornReference
  infer_instance

omit [MeasurableSpace H] in
/-- The global QIT POVM effect is exactly the original product of recorded projectors. -/
theorem productRecordEffect_eq (setting : H → Fin n → LocalUnitary d)
    (z : H × QuditIndex d n) :
    (productBasisPOVM d n (setting z.1)).effects z.2 =
      productRecordedProjector d id (fun i => (setting z.1 i, z.2 i)) := by
  rw [productBasisPOVM_effect]
  ext a b
  change (∏ i, (basisPOVM (setting z.1 i)).effects (z.2 i) (a i) (b i)) =
    ∏ i, recordedProjector d (setting z.1 i, z.2 i) (a i) (b i)
  apply Finset.prod_congr rfl
  intro i _
  rw [basisPOVM_recordedProjector d (setting z.1 i, z.2 i)]

variable [TopologicalSpace H] [BorelSpace H]

omit [MeasurableSpace H] [BorelSpace H] in
/-- Continuity includes the full basis label and the finite outcome word. -/
theorem productRecordEffect_continuous (setting : H → Fin n → LocalUnitary d)
    (hs : Continuous setting) :
    Continuous (fun z : H × QuditIndex d n => (productBasisPOVM d n (setting z.1)).effects z.2) := by
  simp_rw [productRecordEffect_eq]
  apply (productRecordedProjector_continuous d id continuous_id).comp
  apply continuous_pi
  intro i
  exact ((continuous_apply i).comp (hs.comp continuous_fst)).prodMk
    ((continuous_apply i).comp continuous_snd)

omit [MeasurableSpace H] [BorelSpace H] in
/-- The true mixed-state Born probability is continuous on this full record space. -/
theorem productBorn_complete_continuous (ρ : QIT.State (QuditIndex d n))
    (setting : H → Fin n → LocalUnitary d) (hs : Continuous setting) :
    Continuous (fun z : H × QuditIndex d n => productBorn d n (setting z.1) ρ z.2) := by
  apply continuous_prod_of_discrete_right.mpr
  intro x
  exact (productBorn_continuous d n ρ x).comp hs

/-- Every real or complex actual score integral equals its D*p reference integral. -/
theorem completeBornRecordLaw_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NeZero d] (ρ : QIT.State (QuditIndex d n))
    (setting : H → Fin n → LocalUnitary d) (hs : Continuous setting)
    (μ : Measure H) [IsProbabilityMeasure μ] (f : H × QuditIndex d n → E) :
    ∫ z, f z ∂completeBornRecordLaw ρ setting hs.measurable μ =
      ∫ z, ((d : ℝ)^n * productBorn d n (setting z.1) ρ z.2) • f z
        ∂completeBornReference d n μ := by
  have hd := completeBornRecordLaw_density ρ setting hs.measurable μ
  change (completeBornReference d n μ).withDensity _ = _ at hd
  have hc : Continuous (fun z : H × QuditIndex d n =>
      (d : ℝ)^n * productBorn d n (setting z.1) ρ z.2) :=
    continuous_const.mul (productBorn_complete_continuous ρ setting hs)
  rw [← hd, integral_withDensity_eq_integral_toReal_smul
    hc.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal
    (mul_nonneg (by positivity : 0 ≤ (d : ℝ)^n) (productBorn_nonneg d n _ ρ _))]

/-- The full complex trace, not only its real part, is the actual product Born probability. -/
theorem productBorn_complex_trace (ρ : QIT.State (QuditIndex d n))
    (U : Fin n → LocalUnitary d) (x : QuditIndex d n) :
    (productBorn d n U ρ x : ℂ) = Matrix.trace (ρ.matrix * (productBasisPOVM d n U).effects x) :=
  basisBorn_complex_trace ⟨tensorUnitaryMatrix d n U, tensorUnitaryMatrix_unitary d n U⟩ ρ x

variable [CompactSpace H]

/-- Actual mixed-state mean of any continuous complex score equals its reference moment trace. -/
theorem completeBornRecordLaw_complex_mean [NeZero d] (ρ : QIT.State (QuditIndex d n))
    (setting : H → Fin n → LocalUnitary d) (hs : Continuous setting)
    (μ : Measure H) [IsProbabilityMeasure μ] (f : H × QuditIndex d n → ℂ) (hf : Continuous f) :
    ∫ z, f z ∂completeBornRecordLaw ρ setting hs.measurable μ =
      Matrix.trace (ρ.matrix * ((d : ℝ)^n • ∫ z,
        f z • (productBasisPOVM d n (setting z.1)).effects z.2 ∂completeBornReference d n μ)) := by
  rw [completeBornRecordLaw_integral ρ setting hs μ f]
  let F : H × QuditIndex d n → Matrix (QuditIndex d n) (QuditIndex d n) ℂ :=
    fun z => f z • (productBasisPOVM d n (setting z.1)).effects z.2
  have hF : Continuous F := hf.smul (productRecordEffect_continuous setting hs)
  have hi : Integrable F (completeBornReference d n μ) := hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (z : H × QuditIndex d n) :
      ((d : ℝ)^n * productBorn d n (setting z.1) ρ z.2) • f z =
        ((d : ℝ)^n : ℂ) * matrixTraceLeftCLM ρ.matrix (F z) := by
    simp only [F, matrixTraceLeftCLM_apply, Matrix.mul_smul, Matrix.trace_smul,
      smul_eq_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow, productBorn_complex_trace]
    ring
  simp_rw [he]
  rw [integral_const_mul, (matrixTraceLeftCLM ρ.matrix).integral_comp_comm hi,
    matrixTraceLeftCLM_apply]
  simp only [F, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul, Complex.ofReal_pow]

/-- The real score mean is the real trace of the same actual operator. -/
theorem completeBornRecordLaw_mean [NeZero d] (ρ : QIT.State (QuditIndex d n))
    (setting : H → Fin n → LocalUnitary d) (hs : Continuous setting)
    (μ : Measure H) [IsProbabilityMeasure μ] (f : H × QuditIndex d n → ℝ) (hf : Continuous f) :
    ∫ z, f z ∂completeBornRecordLaw ρ setting hs.measurable μ =
      (Matrix.trace (ρ.matrix * ((d : ℝ)^n • ∫ z,
        (f z : ℂ) • (productBasisPOVM d n (setting z.1)).effects z.2
          ∂completeBornReference d n μ))).re := by
  have h := completeBornRecordLaw_complex_mean ρ setting hs μ (fun z => (f z : ℂ))
    (Complex.continuous_ofReal.comp hf)
  rw [integral_complex_ofReal] at h
  exact congrArg Complex.re h

/-- Real score square-integrability is supplied by the actual finite Born law and compact continuity. -/
theorem completeBornRecordLaw_memLp [NeZero d] (ρ : QIT.State (QuditIndex d n))
    (setting : H → Fin n → LocalUnitary d) (hs : Continuous setting)
    (μ : Measure H) [IsProbabilityMeasure μ] (f : H × QuditIndex d n → ℝ) (hf : Continuous f) :
    MemLp f 2 (completeBornRecordLaw ρ setting hs.measurable μ) :=
  hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The actual variance is bounded by the actual second-moment trace for every mixed state. -/
theorem completeBornRecordLaw_variance_le [NeZero d] (ρ : QIT.State (QuditIndex d n))
    (setting : H → Fin n → LocalUnitary d) (hs : Continuous setting)
    (μ : Measure H) [IsProbabilityMeasure μ] (f : H × QuditIndex d n → ℝ) (hf : Continuous f) :
    variance f (completeBornRecordLaw ρ setting hs.measurable μ) ≤
      (Matrix.trace (ρ.matrix * ((d : ℝ)^n • ∫ z,
        ((f z : ℂ)^2) • (productBasisPOVM d n (setting z.1)).effects z.2
          ∂completeBornReference d n μ))).re := by
  have h := variance_le_expectation_sq (completeBornRecordLaw_memLp ρ setting hs μ f hf).aestronglyMeasurable
  have hm := completeBornRecordLaw_mean ρ setting hs μ (fun z => (f z)^2) (hf.pow 2)
  simp only [Complex.ofReal_pow] at hm
  exact h.trans_eq hm

end LocalCertification.Quantum

namespace LocalCertification.Quantum
variable {H : Type*} [MeasurableSpace H] {d n : ℕ}

/-- Zipping all local labels and outcomes preserves the full record, including the empty word. -/
def localRecordEquiv (H : Type*) [MeasurableSpace H] (d n : ℕ) :
    ((Fin n → H) × QuditIndex d n) ≃ᵐ (Fin n → (H × Fin d)) where
  toFun z i := (z.1 i, z.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv z := by cases z; rfl
  right_inv z := by funext i; exact Prod.mk.eta
  measurable_toFun := LocalCertification.Protocol.completeRecords_measurable
  measurable_invFun := (measurable_pi_iff.mpr fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
    (measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i))

/-- The uniform finite outcome law in the actual protocol is the original reference law. -/
theorem finiteUniformMeasure_eq_uniformOutcome (d : ℕ) [NeZero d] [Nonempty (Fin d)] :
    finiteUniformMeasure (Fin d) = uniformFiniteOutcome d := by
  apply Measure.ext_of_singleton
  intro x
  rw [finiteUniformMeasure_atom]
  simp [uniformFiniteOutcome, Measure.smul_apply]

/-- The genuine complete reference law becomes the original product of local full records. -/
theorem localRecordEquiv_reference [NeZero d] (ν : Measure H) [IsProbabilityMeasure ν] :
    (completeBornReference d n (Measure.pi (fun _ : Fin n => ν))).map (localRecordEquiv H d n) =
      Measure.pi (fun _ : Fin n => ν.prod (uniformFiniteOutcome d)) := by
  let : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hk : LocalCertification.Protocol.finiteProductKernel (ι := Fin n)
      (Kernel.const H (uniformFiniteOutcome d)) =
      Kernel.const (Fin n → H) (Measure.pi (fun _ : Fin n => uniformFiniteOutcome d)) := by
    apply Kernel.ext
    intro z
    rfl
  have he := LocalCertification.Protocol.independent_complete_records (ι := Fin n) ν
    (Kernel.const H (uniformFiniteOutcome d))
  rw [hk, Measure.compProd_const] at he
  simp only [Measure.compProd_const] at he
  change ((completeBornReference d n (Measure.pi (fun _ : Fin n => ν))).map
    (fun z => fun i => (z.1 i, z.2 i))) = _
  simpa only [completeBornReference, finiteUniformMeasure_words] using he

/-- Real coefficients and the proved Hermitian kernel make the original centered score exactly real. -/
theorem readoutCenteredScore_ofReal_re {Ω I : Type*} [Fintype I] [DecidableEq I]
    (H : Ω → Matrix I I ℂ) (hH : ∀ ω, (H ω).IsHermitian)
    (h qscale : ℝ) (z : I → ℂ) (ω : Ω) :
    ((readoutCenteredScore H h qscale z ω).re : ℂ) = readoutCenteredScore H h qscale z ω := by
  have he : star (readoutCenteredScore H h qscale z ω) = readoutCenteredScore H h qscale z ω := by
    rw [readoutCenteredScore, star_sub, star_mul, sphereQuadraticForm_star, (hH ω).eq]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  have hi := congrArg Complex.im he
  simp only [Complex.star_def, Complex.conj_im] at hi
  have hz : (readoutCenteredScore H h qscale z ω).im = 0 := by linarith
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hz.symm

/-- The actual real cardinality score, with the original signed kernel and sphere normalization. -/
def cardinalityScore {Ω : Type*} (d n r : ℕ)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) (ω : Fin n → Ω) : ℝ :=
  (readoutCenteredScore (cardinalityReadoutKernel d record r lam)
    (cardinalityReadoutTraceScale d n r lam) ((d : ℝ)^n) ψ.ofLp ω).re

/-- Passing to a real score has not changed the paper's complex quadratic expression. -/
theorem cardinalityScore_ofReal {Ω : Type*} (d n r : ℕ)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex d n)) (ω : Fin n → Ω) :
    (cardinalityScore d n r record lam ψ ω : ℂ) =
      readoutCenteredScore (cardinalityReadoutKernel d record r lam)
        (cardinalityReadoutTraceScale d n r lam) ((d : ℝ)^n) ψ.ofLp ω :=
  readoutCenteredScore_ofReal_re _ (finiteComplementKernel_isHermitian d record _ _) _ _ _ ω

/-- Continuity holds for the same real score on the complete local record. -/
theorem cardinalityScore_continuous {Ω : Type*} [TopologicalSpace Ω]
    (d n r : ℕ) (record : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous record)
    (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    Continuous (cardinalityScore d n r record lam ψ) :=
  Complex.continuous_re.comp (readoutCenteredScore_continuous _
    (finiteComplementKernel_continuous d record hr _ _) _ _ _)


/-- One local label chooses one full local basis; all sites use that same physical controller. -/
def localProductSetting (setting : H → LocalUnitary d) (u : Fin n → H) : Fin n → LocalUnitary d :=
  fun i => setting (u i)

/-- The original cardinality score as a function of the complete global protocol record. -/
def cardinalityBornScore (setting : H → LocalUnitary d) (r : ℕ) (lam : ℕ → ℝ)
    (ψ : EuclideanSpace ℂ (QuditIndex d n))
    (z : (Fin n → H) × QuditIndex d n) : ℝ :=
  cardinalityScore d n r (fun p : H × Fin d => (setting p.1, p.2)) lam ψ (localRecordEquiv H d n z)

variable [TopologicalSpace H]

omit [MeasurableSpace H] in
theorem localProductSetting_continuous (setting : H → LocalUnitary d) (hs : Continuous setting) :
    Continuous (localProductSetting (n := n) setting) :=
  continuous_pi (fun i => hs.comp (continuous_apply i))

theorem localRecordEquiv_continuous : Continuous (localRecordEquiv H d n) :=
  continuous_pi (fun i => ((continuous_apply i).comp continuous_fst).prodMk
    ((continuous_apply i).comp continuous_snd))

theorem cardinalityBornScore_continuous (setting : H → LocalUnitary d) (hs : Continuous setting)
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    Continuous (cardinalityBornScore setting r lam ψ) :=
  (cardinalityScore_continuous d n r _ ((hs.comp continuous_fst).prodMk continuous_snd) lam ψ).comp
    localRecordEquiv_continuous

variable [BorelSpace H] [CompactSpace H] [SecondCountableTopology H] [NeZero d]

/-- Actual complete Born moments are expressed on the original product of local reference records. -/
theorem localRecord_complex_mean (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (ρ : QIT.State (QuditIndex d n))
    (f : (Fin n → (H × Fin d)) → ℂ) (hf : Continuous f) :
    ∫ z, f (localRecordEquiv H d n z)
      ∂completeBornRecordLaw ρ (localProductSetting setting)
        (localProductSetting_continuous setting hs).measurable (Measure.pi (fun _ : Fin n => ν)) =
      Matrix.trace (ρ.matrix * ((d : ℝ)^n • ∫ ω,
        f ω • productRecordedProjector d (fun p : H × Fin d => (setting p.1, p.2)) ω
        ∂Measure.pi (fun _ : Fin n => ν.prod (uniformFiniteOutcome d)))) := by
  have he (z : (Fin n → H) × QuditIndex d n) :
      (productBasisPOVM d n (localProductSetting setting z.1)).effects z.2 =
        productRecordedProjector d (fun p : H × Fin d => (setting p.1, p.2)) (localRecordEquiv H d n z) := by
    rw [productRecordEffect_eq]
    rfl
  have hfglobal : Continuous (fun z : (Fin n → H) × QuditIndex d n => f (localRecordEquiv H d n z)) :=
    hf.comp localRecordEquiv_continuous
  rw [completeBornRecordLaw_complex_mean ρ (localProductSetting setting)
    (localProductSetting_continuous setting hs) (Measure.pi (fun _ : Fin n => ν))
    (fun z => f (localRecordEquiv H d n z)) hfglobal]
  simp_rw [he]
  have ht := integral_map_equiv (μ := completeBornReference d n (Measure.pi (fun _ : Fin n => ν)))
    (localRecordEquiv H d n) (fun ω =>
      f ω • productRecordedProjector d (fun p : H × Fin d => (setting p.1, p.2)) ω)
  rw [localRecordEquiv_reference ν] at ht
  rw [← ht]

/-- The same actual real cardinality score has mean Tr(rho B), with the original B and no spectral premise. -/
theorem cardinalityBornScore_mean (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (ρ : QIT.State (QuditIndex d n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    ∫ z, cardinalityBornScore setting r lam ψ z
      ∂completeBornRecordLaw ρ (localProductSetting setting)
        (localProductSetting_continuous setting hs).measurable (Measure.pi (fun _ : Fin n => ν)) =
      (Matrix.trace (ρ.matrix * cardinalityReadoutMean d (ν.prod (uniformFiniteOutcome d))
        (fun p : H × Fin d => (setting p.1, p.2)) r lam ((d : ℝ)^n) ψ.ofLp)).re := by
  have hr : Continuous (fun p : H × Fin d => (setting p.1, p.2)) :=
    (hs.comp continuous_fst).prodMk continuous_snd
  have h := localRecord_complex_mean setting hs ν ρ
    (fun ω => (cardinalityScore d n r _ lam ψ ω : ℂ))
    (Complex.continuous_ofReal.comp (cardinalityScore_continuous d n r _ hr lam ψ))
  rw [integral_complex_ofReal] at h
  simp_rw [cardinalityScore_ofReal] at h
  simpa only [Complex.ofReal_re, cardinalityBornScore, cardinalityReadoutMean, Fintype.card_fin, readoutMeanOperator] using
    congrArg Complex.re h

/-- The actual squared score has mean Tr(rho M), where M is the full second moment, not the auxiliary S. -/
theorem cardinalityBornScore_second (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (ρ : QIT.State (QuditIndex d n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    ∫ z, (cardinalityBornScore setting r lam ψ z)^2
      ∂completeBornRecordLaw ρ (localProductSetting setting)
        (localProductSetting_continuous setting hs).measurable (Measure.pi (fun _ : Fin n => ν)) =
      (Matrix.trace (ρ.matrix * cardinalityReadoutSecond d (ν.prod (uniformFiniteOutcome d))
        (fun p : H × Fin d => (setting p.1, p.2)) r lam ((d : ℝ)^n) ψ.ofLp)).re := by
  have hr : Continuous (fun p : H × Fin d => (setting p.1, p.2)) :=
    (hs.comp continuous_fst).prodMk continuous_snd
  have h := localRecord_complex_mean setting hs ν ρ
    (fun ω => ((cardinalityScore d n r _ lam ψ ω)^2 : ℝ))
    (Complex.continuous_ofReal.comp ((cardinalityScore_continuous d n r _ hr lam ψ).pow 2))
  rw [integral_complex_ofReal] at h
  simp_rw [Complex.ofReal_pow, cardinalityScore_ofReal] at h
  simpa only [Complex.ofReal_re, cardinalityBornScore, cardinalityReadoutSecond, Fintype.card_fin, readoutSecondOperator] using
    congrArg Complex.re h

omit [NeZero d] in
/-- All actual mixed-state score laws satisfy the square-integrability premise of the implemented block test. -/
theorem cardinalityBornScore_memLp (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (ρ : QIT.State (QuditIndex d n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    MemLp (cardinalityBornScore setting r lam ψ) 2
      (completeBornRecordLaw ρ (localProductSetting setting)
        (localProductSetting_continuous setting hs).measurable (Measure.pi (fun _ : Fin n => ν))) :=
  (cardinalityBornScore_continuous setting hs r lam ψ).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The actual cardinality score variance is controlled by its full M operator for every mixed state. -/
theorem cardinalityBornScore_variance_le (setting : H → LocalUnitary d) (hs : Continuous setting)
    (ν : Measure H) [IsProbabilityMeasure ν] (ρ : QIT.State (QuditIndex d n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    variance (cardinalityBornScore setting r lam ψ)
      (completeBornRecordLaw ρ (localProductSetting setting)
        (localProductSetting_continuous setting hs).measurable (Measure.pi (fun _ : Fin n => ν))) ≤
      (Matrix.trace (ρ.matrix * cardinalityReadoutSecond d (ν.prod (uniformFiniteOutcome d))
        (fun p : H × Fin d => (setting p.1, p.2)) r lam ((d : ℝ)^n) ψ.ofLp)).re :=
  (variance_le_expectation_sq (cardinalityBornScore_memLp setting hs ν ρ r lam ψ).aestronglyMeasurable).trans_eq
    (cardinalityBornScore_second setting hs ν ρ r lam ψ)

end LocalCertification.Quantum

namespace LocalCertification.Quantum
variable {d n : ℕ}

/-- The actual physical experiment chooses one independent full Haar basis at each site,
then measures the possibly entangled mixed state in that product basis. -/
def haarProductBornLaw (d n : ℕ) (ρ : QIT.State (QuditIndex d n)) :
    Measure ((Fin n → LocalUnitary d) × QuditIndex d n) :=
  completeBornRecordLaw ρ (localProductSetting id)
    (localProductSetting_continuous id continuous_id).measurable
    (Measure.pi (fun _ : Fin n => complexUnitaryHaar (Fin d)))

instance haarProductBornLaw_probability (d n : ℕ) (ρ : QIT.State (QuditIndex d n)) :
    IsProbabilityMeasure (haarProductBornLaw d n ρ) := by
  unfold haarProductBornLaw
  infer_instance

/-- Full-Haar actual Born mean, including signed coefficients and all mixed states. -/
theorem haarCardinalityBornScore_mean [NeZero d] (ρ : QIT.State (QuditIndex d n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    ∫ z, cardinalityBornScore (id : LocalUnitary d → LocalUnitary d) r lam ψ z
      ∂haarProductBornLaw d n ρ =
      (Matrix.trace (ρ.matrix * cardinalityReadoutMean d (haarBasisRecords d) id r lam
        ((d : ℝ)^n) ψ.ofLp)).re := by
  exact cardinalityBornScore_mean id continuous_id (complexUnitaryHaar (Fin d)) ρ r lam ψ

/-- Full-Haar actual second moment, with the original full M rather than its auxiliary S. -/
theorem haarCardinalityBornScore_second [NeZero d] (ρ : QIT.State (QuditIndex d n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    ∫ z, (cardinalityBornScore (id : LocalUnitary d → LocalUnitary d) r lam ψ z)^2
      ∂haarProductBornLaw d n ρ =
      (Matrix.trace (ρ.matrix * cardinalityReadoutSecond d (haarBasisRecords d) id r lam
        ((d : ℝ)^n) ψ.ofLp)).re := by
  exact cardinalityBornScore_second id continuous_id (complexUnitaryHaar (Fin d)) ρ r lam ψ

theorem haarCardinalityBornScore_memLp (ρ : QIT.State (QuditIndex d n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    MemLp (cardinalityBornScore (id : LocalUnitary d → LocalUnitary d) r lam ψ) 2
      (haarProductBornLaw d n ρ) :=
  cardinalityBornScore_memLp id continuous_id (complexUnitaryHaar (Fin d)) ρ r lam ψ

theorem haarCardinalityBornScore_variance_le [NeZero d] (ρ : QIT.State (QuditIndex d n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    variance (cardinalityBornScore (id : LocalUnitary d → LocalUnitary d) r lam ψ)
      (haarProductBornLaw d n ρ) ≤
      (Matrix.trace (ρ.matrix * cardinalityReadoutSecond d (haarBasisRecords d) id r lam
        ((d : ℝ)^n) ψ.ofLp)).re :=
  cardinalityBornScore_variance_le id continuous_id (complexUnitaryHaar (Fin d)) ρ r lam ψ

/-- Three actual Pauli bases, with their labels retained and their true conditional Born outcomes. -/
theorem pauliCardinalityBornScore_mean (ρ : QIT.State (QuditIndex 2 n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    ∫ z, cardinalityBornScore pauliBasisUnitary r lam ψ z ∂pauliProductBornLaw n ρ =
      (Matrix.trace (ρ.matrix * cardinalityReadoutMean 2 pauliBasisRecords pauliFullRecord r lam
        ((2 : ℝ)^n) ψ.ofLp)).re :=
  cardinalityBornScore_mean pauliBasisUnitary continuous_of_discreteTopology
    (uniformFiniteOutcome 3) ρ r lam ψ

/-- Pauli outcomes may be entangled; this is the true complete-record second moment for every rho. -/
theorem pauliCardinalityBornScore_second (ρ : QIT.State (QuditIndex 2 n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    ∫ z, (cardinalityBornScore pauliBasisUnitary r lam ψ z)^2 ∂pauliProductBornLaw n ρ =
      (Matrix.trace (ρ.matrix * cardinalityReadoutSecond 2 pauliBasisRecords pauliFullRecord r lam
        ((2 : ℝ)^n) ψ.ofLp)).re :=
  cardinalityBornScore_second pauliBasisUnitary continuous_of_discreteTopology
    (uniformFiniteOutcome 3) ρ r lam ψ

theorem pauliCardinalityBornScore_memLp (ρ : QIT.State (QuditIndex 2 n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    MemLp (cardinalityBornScore pauliBasisUnitary r lam ψ) 2 (pauliProductBornLaw n ρ) :=
  cardinalityBornScore_memLp pauliBasisUnitary continuous_of_discreteTopology
    (uniformFiniteOutcome 3) ρ r lam ψ

theorem pauliCardinalityBornScore_variance_le (ρ : QIT.State (QuditIndex 2 n))
    (r : ℕ) (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex 2 n)) :
    variance (cardinalityBornScore pauliBasisUnitary r lam ψ) (pauliProductBornLaw n ρ) ≤
      (Matrix.trace (ρ.matrix * cardinalityReadoutSecond 2 pauliBasisRecords pauliFullRecord r lam
        ((2 : ℝ)^n) ψ.ofLp)).re :=
  cardinalityBornScore_variance_le pauliBasisUnitary continuous_of_discreteTopology
    (uniformFiniteOutcome 3) ρ r lam ψ

end LocalCertification.Quantum
