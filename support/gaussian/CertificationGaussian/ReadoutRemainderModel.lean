import CertificationGaussian.GaussianRecordFubini

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexConjugate
namespace CertificationGaussian

@[fun_prop] theorem complexGaussianNormalMatrix_continuous {Ω I : Type*}
    [TopologicalSpace Ω] [Fintype I] [DecidableEq I]
    (A B : Ω → Matrix I I ℂ) (hA : Continuous A) (hB : Continuous B) (z : I → ℂ) :
    Continuous (fun ω => complexGaussianNormalMatrix (A ω) (B ω) z) := by
  simp only [complexGaussianNormalMatrix,sphereQuadraticForm,Matrix.trace,Matrix.diag,
    Matrix.add_apply,Matrix.mul_apply]
  fun_prop

/-- The Bochner integral of the normal-ordered matrix remainder D∫P_s W_z(H_s,H_s). -/
def normalReadoutRemainder {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (μ : Measure Ω) (D : ℝ) (P H : Ω → Matrix I I ℂ) (z : I → ℂ) : Matrix I I ℂ :=
  D • ∫ ω,complexGaussianNormalMatrix (H ω) (H ω) z • P ω ∂μ

section CompactRecords
variable {Ω I : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
    [CompactSpace Ω] [Fintype I] [DecidableEq I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] in
/-- Each actual remainder integrand is continuous on the compact complete-record space. -/
@[fun_prop] theorem normalReadoutRemainder_integrand_continuous
    (P H : Ω → Matrix I I ℂ) (hP : Continuous P) (hH : Continuous H) (z : I → ℂ) :
    Continuous (fun ω => complexGaussianNormalMatrix (H ω) (H ω) z • P ω) := by fun_prop

theorem normalReadoutRemainder_integrand_integrable
    (P H : Ω → Matrix I I ℂ) (hP : Continuous P) (hH : Continuous H) (z : I → ℂ) :
    Integrable (fun ω => complexGaussianNormalMatrix (H ω) (H ω) z • P ω) μ :=
  (normalReadoutRemainder_integrand_continuous P H hP hH z).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Continuous pointwise Hermitian matrices have a Hermitian genuine Bochner average. -/
theorem hermitian_matrix_integral (F : Ω → Matrix I I ℂ) (hF : Continuous F)
    (h : ∀ ω,(F ω).IsHermitian) : (∫ ω,F ω∂μ).IsHermitian := by
  apply Matrix.ext
  intro i j
  change star ((∫ ω,F ω∂μ) j i)=(∫ ω,F ω∂μ) i j
  rw [matrix_entry_integral μ F hF j i,matrix_entry_integral μ F hF i j]
  change conj (∫ ω,F ω j i∂μ)=∫ ω,F ω i j∂μ
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => congrArg (fun M : Matrix I I ℂ => M i j) (h ω).eq)

/-- Hermitian P and H make the actual Z_z Hermitian, including arbitrary signed real normalization. -/
theorem normalReadoutRemainder_isHermitian (D : ℝ) (P H : Ω → Matrix I I ℂ)
    (hP : Continuous P) (hH : Continuous H) (hPH : ∀ ω,(P ω).IsHermitian)
    (hHH : ∀ ω,(H ω).IsHermitian) (z : I → ℂ) :
    (normalReadoutRemainder μ D P H z).IsHermitian := by
  apply Matrix.IsHermitian.smul _ (show IsSelfAdjoint D from rfl)
  apply hermitian_matrix_integral μ _ (normalReadoutRemainder_integrand_continuous P H hP hH z)
  intro ω
  exact (hPH ω).smul (complexGaussianNormalMatrix_star_of_hermitian _ _ (hHH ω) (hHH ω) z)

end CompactRecords

@[fun_prop] theorem localReadoutFactor_continuous (d : ℕ) (a : Bool) :
    Continuous (localReadoutFactor d a) := by
  cases a
  · change Continuous (recordedProjector d)
    fun_prop
  · change Continuous (fun ω => 1-recordedProjector d ω)
    fun_prop

section ProductRecords
variable {S K Ω : Type*} [Fintype S] [DecidableEq S] [Fintype K]

omit [DecidableEq S] in
@[fun_prop] theorem productRecordedProjector_continuous [TopologicalSpace Ω]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r) :
    Continuous (productRecordedProjector (S:=S) d r) := by
  unfold productRecordedProjector wickTensorMatrix
  fun_prop

@[fun_prop] theorem productReadoutFactor_continuous [TopologicalSpace Ω]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r) (A : Finset S) :
    Continuous (productReadoutFactor d r A) := by
  unfold productReadoutFactor wickTensorMatrix
  fun_prop

@[fun_prop] theorem finiteComplementKernel_continuous [TopologicalSpace Ω]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : K → Finset S) (c : K → ℝ) : Continuous (finiteComplementKernel d r A c) := by
  unfold finiteComplementKernel
  fun_prop

/-- The projector associated with a complete product record is positive semidefinite. -/
theorem productRecordedProjector_posSemidef (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (ω : S → Ω) :
    (productRecordedProjector d r ω).PosSemidef :=
  wickTensorMatrix_posSemidef _ (fun s => recordedProjector_posSemidef d (r (ω s)))

theorem productReadoutFactor_posSemidef (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (A : Finset S) (ω : S → Ω) :
    (productReadoutFactor d r A ω).PosSemidef :=
  wickTensorMatrix_posSemidef _ (fun s => localReadoutFactor_posSemidef d _ (r (ω s)))

/-- Signed real coefficients preserve Hermiticity; they are not assumed nonnegative. -/
theorem finiteComplementKernel_isHermitian (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (A : K → Finset S) (c : K → ℝ) (ω : S → Ω) :
    (finiteComplementKernel d r A c ω).IsHermitian := by
  unfold finiteComplementKernel Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact ((productReadoutFactor_posSemidef d r (A k) ω).isHermitian.smul
    (show IsSelfAdjoint (c k:ℂ) from by simp [IsSelfAdjoint])).eq

/-- The paper's actual finite-complement remainder on the same product record measure and global coordinates. -/
def finiteComplementRemainder [MeasurableSpace Ω] (d : ℕ) (μ : Measure Ω)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (A : K → Finset S) (c : K → ℝ)
    (z : (S → Fin d) → ℂ) : Matrix (S → Fin d) (S → Fin d) ℂ :=
  normalReadoutRemainder (Measure.pi (fun _ : S => μ)) ((d:ℝ)^(Fintype.card S))
    (productRecordedProjector d r) (finiteComplementKernel d r A c) z

/-- Every actual finite-complement Z_z is Hermitian under the original full-record product probability. -/
theorem finiteComplementRemainder_isHermitian [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] [CompactSpace Ω] [SecondCountableTopology Ω]
    (d : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : K → Finset S) (c : K → ℝ) (z : (S → Fin d) → ℂ) :
    (finiteComplementRemainder d μ r A c z).IsHermitian :=
  normalReadoutRemainder_isHermitian _ _ _ _
    (productRecordedProjector_continuous d r hr) (finiteComplementKernel_continuous d r hr A c)
    (fun ω => (productRecordedProjector_posSemidef d r ω).isHermitian)
    (finiteComplementKernel_isHermitian d r A c) z

end ProductRecords
end CertificationGaussian
