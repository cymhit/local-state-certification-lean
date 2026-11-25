import CertificationGaussian.FiniteWickInclusionExclusionBounds
import CertificationGaussian.ProductReadoutContraction

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace CertificationGaussian

/-- Exact finite multilinearity of the actual tensor-permutation trace. -/
theorem wickTensorMatrix_weighted_sum_trace {T K I : Type*}
    [Fintype T] [DecidableEq T] [Fintype K] [Fintype I] [DecidableEq I]
    (c : T → K → ℂ) (M : T → K → Matrix I I ℂ) (π : Equiv.Perm T) :
    Matrix.trace (wickTensorMatrix (fun t => ∑ k,c t k • M t k)*wickTensorPermutationMatrix π) =
      ∑ q : T → K,(∏ t,c t (q t))*
        Matrix.trace (wickTensorMatrix (fun t => M t (q t))*wickTensorPermutationMatrix π) := by
  simp only [wickTensorMatrix_permutation_trace,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  simp_rw [Fintype.prod_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Finset.prod_mul_distrib,Finset.mul_sum]

/-- Finite choices preserve all coefficient multiplicities; their total absolute mass is the exact power. -/
theorem finite_choice_coefficient_mass {T K : Type*} [Fintype T] [DecidableEq T] [Fintype K]
    (c : K → ℂ) : (∑ q : T → K,‖∏ t,c (q t)‖)=(∑ k,‖c k‖)^(Fintype.card T) := by
  simp only [norm_prod]
  rw [← Fintype.prod_sum (fun (_ : T) (k : K) => ‖c k‖)]
  simp

/-- The finite coefficient expansion costs precisely its absolute mass, without counting subsets separately. -/
theorem finite_choice_sum_norm_le {T K : Type*} [Fintype T] [DecidableEq T] [Fintype K]
    (c : K → ℂ) (z : (T → K) → ℂ) (E : ℝ) (h : ∀ q,‖z q‖≤E) :
    ‖∑ q : T → K,(∏ t,c (q t))*z q‖≤(∑ k,‖c k‖)^(Fintype.card T)*E := by
  calc
    _ ≤ ∑ q : T → K,‖∏ t,c (q t)‖*‖z q‖ := by
      simpa only [norm_mul] using norm_sum_le Finset.univ (fun q : T → K => (∏ t,c (q t))*z q)
    _ ≤ ∑ q : T → K,‖∏ t,c (q t)‖*E := Finset.sum_le_sum
      (fun q _ => mul_le_mul_of_nonneg_left (h q) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul,finite_choice_coefficient_mass]

section ProductRecords
variable {S K Ω : Type*} [Fintype S] [DecidableEq S] [Fintype K]

/-- The actual finite-complement kernel, allowing signed real coefficients and overlapping/repeated subsets. -/
def finiteComplementKernel (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d)
    (A : K → Finset S) (c : K → ℝ) (ω : S → Ω) : Matrix (S → Fin d) (S → Fin d) ℂ :=
  ∑ k,(c k:ℂ) • productReadoutFactor d r (A k) ω

/-- A fixed actual Wick term of the full kernel, before expanding its eight occurrences. -/
def finiteComplementWickIntegrand (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d)
    (A : K → Finset S) (c : K → ℝ) (π : Equiv.Perm (Fin 4 × Fin 2))
    (x : (S → Ω) × ((S → Ω) × ((S → Ω) × (S → Ω)))) : ℂ :=
  Matrix.trace (productRecordedProjector d r x.1*productRecordedProjector d r x.2.1*
    productRecordedProjector d r x.2.2.1*productRecordedProjector d r x.2.2.2)*
  Matrix.trace (wickTensorMatrix (fun t : Fin 4 × Fin 2 =>
    finiteComplementKernel d r A c (fourRecordAt x t.1))*wickTensorPermutationMatrix π)

/-- Exact expansion over eight labelled subset choices, preserving repeated choices and their coefficients. -/
theorem finiteComplementWickIntegrand_eq_sum (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (A : K → Finset S) (c : K → ℝ)
    (π : Equiv.Perm (Fin 4 × Fin 2))
    (x : (S → Ω) × ((S → Ω) × ((S → Ω) × (S → Ω)))) :
    finiteComplementWickIntegrand d r A c π x =
      ∑ q : (Fin 4 × Fin 2) → K,(∏ t,(c (q t):ℂ))*
        productRecordWickIntegrand d r (fun t => A (q t)) π x := by
  unfold finiteComplementWickIntegrand finiteComplementKernel
  rw [wickTensorMatrix_weighted_sum_trace,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  unfold productRecordWickIntegrand
  ring

variable [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [SecondCountableTopology Ω]

/-- All finite-complement terms are genuinely integrable under the original four global product records. -/
theorem finiteComplementWickIntegrand_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : K → Finset S) (c : K → ℝ) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    Integrable (finiteComplementWickIntegrand d r A c π)
      (fourReadoutLaw (Measure.pi (fun _ : S => μ))) := by
  simp_rw [funext (finiteComplementWickIntegrand_eq_sum d r A c π)]
  exact integrable_finsetSum _ (fun q _ =>
    (productRecordWickIntegrand_integrable μ d r hr (fun t => A (q t)) π).const_mul _)

/-- The actual normalized integral equals the finite weighted sum of actual normalized subset terms. -/
theorem finiteComplementWickIntegral_eq_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : K → Finset S) (c : K → ℝ) (π : Equiv.Perm (Fin 4 × Fin 2)) :
    ((d:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementWickIntegrand d r A c π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => μ))) =
      ∑ q : (Fin 4 × Fin 2) → K,(∏ t,(c (q t):ℂ))*
        (((d:ℂ)^(Fintype.card S))^4*
          (∫ x,productRecordWickIntegrand d r (fun t => A (q t)) π x
            ∂fourReadoutLaw (Measure.pi (fun _ : S => μ)))) := by
  simp_rw [finiteComplementWickIntegrand_eq_sum]
  rw [integral_finsetSum]
  · simp only [integral_const_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  · intro q _
    exact (productRecordWickIntegrand_integrable μ d r hr (fun t => A (q t)) π).const_mul _


/-- The full finite kernel pays exactly the eighth power of its total absolute coefficient mass. -/
theorem finiteComplementWickIntegral_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : K → Finset S) (c : K → ℝ) (π : Equiv.Perm (Fin 4 × Fin 2)) (E : ℝ)
    (h : ∀ q : (Fin 4 × Fin 2) → K,
      ‖((d:ℂ)^(Fintype.card S))^4*
        (∫ x,productRecordWickIntegrand d r (fun t => A (q t)) π x
          ∂fourReadoutLaw (Measure.pi (fun _ : S => μ)))‖≤E) :
    ‖((d:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementWickIntegrand d r A c π x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => μ)))‖≤(∑ k,|c k|)^8*E := by
  rw [finiteComplementWickIntegral_eq_sum μ d r hr]
  have hb := finite_choice_sum_norm_le (T:=Fin 4 × Fin 2) (fun k => (c k:ℂ)) _ E h
  simpa only [Fintype.card_prod,Fintype.card_fin,Complex.norm_real,Real.norm_eq_abs,
    show 4*2=8 by decide] using hb

/-- The original actual Gaussian fourth-block expectation, still inside the original record integral. -/
def finiteComplementGaussianFourthIntegrand (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (A : K → Finset S) (c : K → ℝ)
    (x : (S → Ω) × ((S → Ω) × ((S → Ω) × (S → Ω)))) : ℂ :=
  Matrix.trace (productRecordedProjector d r x.1*productRecordedProjector d r x.2.1*
    productRecordedProjector d r x.2.2.1*productRecordedProjector d r x.2.2.2)*
  ∫ z,∏ b : Fin 4,complexGaussianNormalMatrix
    (finiteComplementKernel d r A c (fourRecordAt x b))
    (finiteComplementKernel d r A c (fourRecordAt x b)) (complexCoordinate z)
      ∂pairedGaussian (S → Fin d)

omit [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω]
  [SecondCountableTopology Ω] in
/-- All Wick premises are supplied by the proved actual complex Gaussian law, not assumed moments. -/
theorem finiteComplementGaussianFourthIntegrand_eq_sum (d : ℕ)
    (r : Ω → ComplexUnitary (Fin d) × Fin d) (A : K → Finset S) (c : K → ℝ)
    (x : (S → Ω) × ((S → Ω) × ((S → Ω) × (S → Ω)))) :
    finiteComplementGaussianFourthIntegrand d r A c x =
      ∑ π ∈ fourBlockDerangements,finiteComplementWickIntegrand d r A c π x := by
  unfold finiteComplementGaussianFourthIntegrand
  rw [complexGaussian_four_matrix_blocks_trace
    (fun t : Fin 4 × Fin 2 => finiteComplementKernel d r A c (fourRecordAt x t.1))]
  exact Finset.mul_sum _ _ _

theorem finiteComplementGaussianFourthIntegrand_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : K → Finset S) (c : K → ℝ) :
    Integrable (finiteComplementGaussianFourthIntegrand d r A c)
      (fourReadoutLaw (Measure.pi (fun _ : S => μ))) := by
  simp_rw [funext (finiteComplementGaussianFourthIntegrand_eq_sum d r A c)]
  exact integrable_finsetSum _ (fun π _ => finiteComplementWickIntegrand_integrable μ d r hr A c π)

/-- The normalized true Gaussian/readout integral is the finite sum of its normalized true Wick integrals. -/
theorem finiteComplementGaussianFourthIntegral_eq_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : ℕ) (r : Ω → ComplexUnitary (Fin d) × Fin d) (hr : Continuous r)
    (A : K → Finset S) (c : K → ℝ) :
    ((d:ℂ)^(Fintype.card S))^4*
      (∫ x,finiteComplementGaussianFourthIntegrand d r A c x
        ∂fourReadoutLaw (Measure.pi (fun _ : S => μ))) =
      ∑ π ∈ fourBlockDerangements,((d:ℂ)^(Fintype.card S))^4*
        (∫ x,finiteComplementWickIntegrand d r A c π x
          ∂fourReadoutLaw (Measure.pi (fun _ : S => μ))) := by
  simp_rw [finiteComplementGaussianFourthIntegrand_eq_sum]
  rw [integral_finsetSum]
  · exact Finset.mul_sum _ _ _
  · intro π _
    exact finiteComplementWickIntegrand_integrable μ d r hr A c π

end ProductRecords

/-- The actual admissible pairing count is at most 8!, with no permutation enumeration. -/
theorem fourBlockWick_sum_norm_le (f : Equiv.Perm (Fin 4 × Fin 2) → ℂ) (E : ℝ)
    (hE : 0≤E) (h : ∀ π∈fourBlockDerangements,‖f π‖≤E) :
    ‖∑ π∈fourBlockDerangements,f π‖≤(Nat.factorial 8:ℝ)*E := by
  calc
    _ ≤ ∑ π∈fourBlockDerangements,‖f π‖ := norm_sum_le _ _
    _ ≤ ∑ _π∈fourBlockDerangements,E := Finset.sum_le_sum h
    _ = (fourBlockDerangements.card : ℝ)*E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast fourBlockDerangements_card_le_eight_factorial) hE
end CertificationGaussian
