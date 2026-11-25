import LocalCertification.Quantum.BornKernel

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Classical
open scoped BigOperators ENNReal
noncomputable section
namespace LocalCertification.Quantum
universe u v

/-- Uniform reference outcomes on the actual finite outcome type. -/
def finiteUniformMeasure (O : Type u) [MeasurableSpace O] [Fintype O] [Nonempty O] : Measure O :=
  (PMF.ofFintype (fun _ : O => (Fintype.card O : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp))).toMeasure

instance finiteUniformMeasure_probability (O : Type u) [MeasurableSpace O] [Fintype O] [Nonempty O] :
    IsProbabilityMeasure (finiteUniformMeasure O) := by unfold finiteUniformMeasure; infer_instance

variable {O : Type u} [MeasurableSpace O] [Fintype O] [Nonempty O] [MeasurableSingletonClass O]

@[simp] theorem finiteUniformMeasure_atom (o : O) :
    finiteUniformMeasure O {o} = (Fintype.card O : ℝ≥0∞)⁻¹ := by
  simp [finiteUniformMeasure]

@[simp] theorem finiteUniformMeasure_atom_real (o : O) :
    (finiteUniformMeasure O {o}).toReal = (Fintype.card O : ℝ)⁻¹ := by
  simp

variable {H : Type v} [MeasurableSpace H]

/-- Actual finite-output kernel sampling equals uniform-reference sampling weighted by cardinality times its atom.
The common label law is arbitrary, with its original sigma algebra and no standard-Borel assumption. -/
theorem finiteKernel_joint_uniform_density (κ : Kernel H O) [IsMarkovKernel κ]
    (μ : Measure H) [IsFiniteMeasure μ] :
    (μ.prod (finiteUniformMeasure O)).withDensity
      (fun p : H × O => ENNReal.ofReal ((Fintype.card O : ℝ)*(κ p.1 {p.2}).toReal)) = μ ⊗ₘ κ := by
  have hac : ∀ᵐ h ∂μ, κ h ≪ Kernel.const H (finiteUniformMeasure O) h := by
    apply Filter.Eventually.of_forall
    intro h
    apply LocalCertification.Information.absolutelyContinuous_of_pos_atoms
    intro o
    simp
  have h := LocalCertification.Information.joint_withDensity κ (Kernel.const H (finiteUniformMeasure O)) μ hac
  have hd : LocalCertification.Information.jointDensity κ (Kernel.const H (finiteUniformMeasure O)) =
      (fun p : H × O => ENNReal.ofReal ((Fintype.card O : ℝ)*(κ p.1 {p.2}).toReal)) := by
    funext p
    simp only [LocalCertification.Information.jointDensity, LocalCertification.Information.atomDensity,
      Kernel.const_apply, finiteUniformMeasure_atom_real, div_inv_eq_mul, mul_comm]
  rwa [Measure.compProd_const, hd] at h

variable {d n : ℕ}

/-- Full basis label and outcome are retained in the actual one-copy joint Born law. -/
def completeBornRecordLaw (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (setting : H → Fin n → CertificationGaussian.LocalUnitary d) (hm : Measurable setting) (μ : Measure H) :
    Measure (H × CertificationGaussian.QuditIndex d n) := μ ⊗ₘ controlledProductBornKernel d n ρ setting hm

instance completeBornRecordLaw_probability (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (setting : H → Fin n → CertificationGaussian.LocalUnitary d) (hm : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ] : IsProbabilityMeasure (completeBornRecordLaw ρ setting hm μ) := by
  unfold completeBornRecordLaw
  infer_instance

/-- Choosing the full basis before the copy leaves its marginal equal to the prescribed state-independent label law. -/
theorem completeBornRecordLaw_fst (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (setting : H → Fin n → CertificationGaussian.LocalUnitary d) (hm : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ] : (completeBornRecordLaw ρ setting hm μ).fst = μ := by
  unfold completeBornRecordLaw
  exact Measure.fst_compProd _ _

/-- A literal basis-label event and outcome have their actual conditional Born integral. -/
theorem completeBornRecordLaw_rectangle (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (setting : H → Fin n → CertificationGaussian.LocalUnitary d) (hm : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ] (B : Set H) (hB : MeasurableSet B)
    (x : CertificationGaussian.QuditIndex d n) :
    completeBornRecordLaw ρ setting hm μ (B ×ˢ {x}) =
      ∫⁻ h in B, ENNReal.ofReal (productBorn d n (setting h) ρ x) ∂μ := by
  rw [completeBornRecordLaw, Measure.compProd_apply_prod hB (measurableSet_singleton x)]
  apply lintegral_congr
  intro h
  simp only [controlledProductBornKernel_apply, productBornMeasure, povmBornMeasure_atom, productBorn]
  simp

/-- The paper's D*p density is proved for the actual QIT product POVM and any state-independent setting law. -/
theorem completeBornRecordLaw_density [NeZero d] (ρ : QIT.State (CertificationGaussian.QuditIndex d n))
    (setting : H → Fin n → CertificationGaussian.LocalUnitary d) (hm : Measurable setting)
    (μ : Measure H) [IsProbabilityMeasure μ] :
    let _ : Nonempty (CertificationGaussian.QuditIndex d n) := ⟨fun _ => ⟨0,Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
    (μ.prod (finiteUniformMeasure (CertificationGaussian.QuditIndex d n))).withDensity
      (fun p : H × CertificationGaussian.QuditIndex d n =>
        ENNReal.ofReal ((d:ℝ)^n * productBorn d n (setting p.1) ρ p.2)) =
      completeBornRecordLaw ρ setting hm μ := by
  dsimp only
  simpa only [CertificationGaussian.qudit_card, Nat.cast_pow, controlledProductBornKernel_apply,
    productBornMeasure_atom_real, completeBornRecordLaw] using
    finiteKernel_joint_uniform_density (controlledProductBornKernel d n ρ setting hm) μ

end LocalCertification.Quantum
