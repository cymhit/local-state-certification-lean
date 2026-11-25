import LocalCertification.Quantum.BornMeasure
import LocalCertification.Probability.BlockAmplification

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal MatrixOrder ComplexOrder
open MeasureTheory ProbabilityTheory Matrix
noncomputable section
namespace LocalCertification.Comparisons

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem target_projector_le_one (ψ : QIT.PureVector I) : ψ.state.matrix ≤ 1 := by
  rw [Matrix.le_iff]
  have h := Matrix.posSemidef_conjTranspose_mul_self (1 - ψ.state.matrix)
  simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    ψ.state_matrix_conjTranspose, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, ψ.state_matrix_mul_self, sub_self,
    sub_zero] using h

/-- The actual global binary projective measurement; it is separate from local protocols. -/
def globalProjectorPOVM (ψ : QIT.PureVector I) : QIT.POVM Bool I :=
  QIT.POVM.binaryOfEffect ψ.state.matrix ψ.state.pos (target_projector_le_one ψ)

@[simp] theorem globalProjectorPOVM_true (ψ : QIT.PureVector I) :
    (globalProjectorPOVM ψ).effects true = ψ.state.matrix := rfl

@[simp] theorem globalProjectorPOVM_false (ψ : QIT.PureVector I) :
    (globalProjectorPOVM ψ).effects false = 1 - ψ.state.matrix := rfl

theorem globalProjector_prob_true (ψ : QIT.PureVector I) (ρ : QIT.State I) :
    ((globalProjectorPOVM ψ).prob ρ true : ℝ) = LocalCertification.Quantum.pureTargetFidelity ψ ρ := by
  rw [QIT.POVM.prob_eq_trace_re, globalProjectorPOVM_true,
    Matrix.trace_mul_comm, LocalCertification.Quantum.pureTargetFidelity]

theorem globalProjector_prob_false (ψ : QIT.PureVector I) (ρ : QIT.State I) :
    ((globalProjectorPOVM ψ).prob ρ false : ℝ) = 1 - LocalCertification.Quantum.pureTargetFidelity ψ ρ := by
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ)) ((globalProjectorPOVM ψ).sum_prob ρ)
  simp only [Fintype.sum_bool, NNReal.coe_add, NNReal.coe_one,
    globalProjector_prob_true] at h
  linarith

def globalProjectorParameter (ψ : QIT.PureVector I) (ρ : QIT.State I) : unitInterval :=
  ⟨LocalCertification.Quantum.pureTargetFidelity ψ ρ, by
    rw [← globalProjector_prob_true]
    exact ⟨(QIT.POVM.prob _ _ _).coe_nonneg, QIT.POVM.prob_le_one _ _ _⟩⟩

def globalProjectorLaw (ψ : QIT.PureVector I) (ρ : QIT.State I) : Measure Bool :=
  LocalCertification.Quantum.povmBornMeasure (globalProjectorPOVM ψ) ρ

instance globalProjectorLaw_probability (ψ : QIT.PureVector I) (ρ : QIT.State I) :
    IsProbabilityMeasure (globalProjectorLaw ψ ρ) := by
  unfold globalProjectorLaw
  infer_instance

theorem globalProjectorLaw_eq_bernoulli (ψ : QIT.PureVector I) (ρ : QIT.State I) :
    globalProjectorLaw ψ ρ = bernoulliMeasure true false (globalProjectorParameter ψ ρ) := by
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  cases b <;>
    simp [globalProjectorLaw, globalProjector_prob_true, globalProjector_prob_false,
      globalProjectorParameter]

def projectorOutcome (b : Bool) : ℝ := if b then 1 else 0

theorem projectorOutcome_mem (b : Bool) : projectorOutcome b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> norm_num [projectorOutcome]

theorem globalProjector_integral (ψ : QIT.PureVector I) (ρ : QIT.State I) :
    (∫ b, projectorOutcome b ∂globalProjectorLaw ψ ρ) =
      LocalCertification.Quantum.pureTargetFidelity ψ ρ := by
  have he : projectorOutcome = Set.indicator {true} (fun _ : Bool => (1 : ℝ)) := by
    funext b
    cases b <;> simp [projectorOutcome]
  rw [he, integral_indicator (measurableSet_singleton true), integral_const]
  simp [globalProjectorLaw, globalProjector_prob_true]

/-- Independent copies of the actual Born readout, for a fixed predetermined sample count. -/
def globalProjectorRecordLaw (ψ : QIT.PureVector I) (ρ : QIT.State I) (m : ℕ) :
    Measure (Fin m → Bool) := Measure.pi (fun _ => globalProjectorLaw ψ ρ)

theorem globalProjector_iid (ψ : QIT.PureVector I) (ρ : QIT.State I) (m : ℕ) :
    iIndepFun (fun i : Fin m => fun x : Fin m → Bool => projectorOutcome (x i))
      (globalProjectorRecordLaw ψ ρ m) :=
  iIndepFun_pi (fun _ => (measurable_of_countable projectorOutcome).aemeasurable)

theorem globalProjector_marginal (ψ : QIT.PureVector I) (ρ : QIT.State I)
    {m : ℕ} (i : Fin m) :
    (globalProjectorRecordLaw ψ ρ m).map (fun x => x i) = globalProjectorLaw ψ ρ :=
  (measurePreserving_eval (fun _ : Fin m => globalProjectorLaw ψ ρ) i).map_eq

end LocalCertification.Comparisons
