import CertificationGaussian.PositiveTensorTrace
import CertificationGaussian.HaarBasisRecords

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker
namespace CertificationGaussian

/-- The actual recorded rank-one projector is positive, for every full basis/outcome record. -/
theorem recordedProjector_posSemidef (d : ℕ) (ω : ComplexUnitary (Fin d) × Fin d) :
    (recordedProjector d ω).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star (fun a => ω.1.val a ω.2)

/-- Its complement is the sum of the remaining basis projectors. -/
theorem recordedComplement_eq_sum (d : ℕ) (ω : ComplexUnitary (Fin d) × Fin d) :
    1-recordedProjector d ω =
      ∑ j ∈ (Finset.univ : Finset (Fin d)).erase ω.2, columnProjector (Fin d) ω.1.val j := by
  have h := Finset.add_sum_erase (Finset.univ : Finset (Fin d))
    (fun j => columnProjector (Fin d) ω.1.val j) (Finset.mem_univ ω.2)
  rw [sum_columnProjector] at h
  change 1-columnProjector (Fin d) ω.1.val ω.2 = _
  rw [← h]
  abel

theorem recordedComplement_posSemidef (d : ℕ) (ω : ComplexUnitary (Fin d) × Fin d) :
    (1-recordedProjector d ω).PosSemidef := by
  rw [recordedComplement_eq_sum]
  exact Matrix.posSemidef_sum _ (fun j _ => Matrix.posSemidef_vecMulVec_self_star (fun a => ω.1.val a j))

/-- False chooses P and true chooses I-P, preserving the actual recorded outcome. -/
def localReadoutFactor (d : ℕ) (ε : Bool) (ω : ComplexUnitary (Fin d) × Fin d) :
    Matrix (Fin d) (Fin d) ℂ := if ε then 1-recordedProjector d ω else recordedProjector d ω

theorem localReadoutFactor_posSemidef (d : ℕ) (ε : Bool) (ω : ComplexUnitary (Fin d) × Fin d) :
    (localReadoutFactor d ε ω).PosSemidef := by
  cases ε
  · exact recordedProjector_posSemidef d ω
  · exact recordedComplement_posSemidef d ω

theorem recordedProjector_trace_one (d : ℕ) (ω : ComplexUnitary (Fin d) × Fin d) :
    Matrix.trace (recordedProjector d ω)=1 := unitary_columnProjector_trace (Fin d) ω.1 ω.2

theorem localReadoutFactor_trace (d : ℕ) (ε : Bool) (ω : ComplexUnitary (Fin d) × Fin d) :
    Matrix.trace (localReadoutFactor d ε ω) = if ε then (d:ℂ)-1 else 1 := by
  cases ε <;> simp [localReadoutFactor,Matrix.trace_sub,recordedProjector_trace_one]

/-- The exact three-factor tensor in one changed site, with both input factors and its output projector. -/
def localChangedSiteIntegrand (d : ℕ) (a b : Bool) (ω : ComplexUnitary (Fin d) × Fin d) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  (localReadoutFactor d a ω ⊗ₖ localReadoutFactor d b ω) ⊗ₖ recordedProjector d ω

theorem localChangedSiteIntegrand_posSemidef (d : ℕ) (a b : Bool) (ω : ComplexUnitary (Fin d) × Fin d) :
    (localChangedSiteIntegrand d a b ω).PosSemidef :=
  ((localReadoutFactor_posSemidef d a ω).kronecker (localReadoutFactor_posSemidef d b ω)).kronecker
    (recordedProjector_posSemidef d ω)

@[fun_prop] theorem localChangedSiteIntegrand_continuous (d : ℕ) (a b : Bool) :
    Continuous (localChangedSiteIntegrand d a b) := by
  apply continuous_pi
  rintro ⟨⟨i1,i2⟩,i3⟩
  apply continuous_pi
  rintro ⟨⟨j1,j2⟩,j3⟩
  cases a <;> cases b <;>
    simp only [localChangedSiteIntegrand,localReadoutFactor,Matrix.kronecker_apply,
      Bool.false_eq_true,ite_false,ite_true,Matrix.sub_apply]
  all_goals fun_prop

theorem localChangedSiteIntegrand_integrable (d : ℕ) [NeZero d] (a b : Bool) :
    Integrable (localChangedSiteIntegrand d a b) (haarBasisRecords d) :=
  (localChangedSiteIntegrand_continuous d a b).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem localChangedSiteIntegrand_trace (d : ℕ) (a b : Bool) (ω : ComplexUnitary (Fin d) × Fin d) :
    Matrix.trace (localChangedSiteIntegrand d a b ω) =
      (if a then (d:ℂ)-1 else 1)*(if b then (d:ℂ)-1 else 1) := by
  simp only [localChangedSiteIntegrand,Matrix.trace_kronecker,localReadoutFactor_trace,
    recordedProjector_trace_one,mul_one]

/-- The actual Haar-basis × uniform-outcome integral, with the required factor d. -/
def haarChangedSiteTensor (d : ℕ) (a b : Bool) :
    Matrix ((Fin d × Fin d) × Fin d) ((Fin d × Fin d) × Fin d) ℂ :=
  (d:ℝ) • ∫ ω, localChangedSiteIntegrand d a b ω ∂haarBasisRecords d

theorem haarChangedSiteTensor_posSemidef (d : ℕ) (a b : Bool) :
    (haarChangedSiteTensor d a b).PosSemidef := by
  unfold haarChangedSiteTensor
  apply Matrix.PosSemidef.smul _ (Nat.cast_nonneg d)
  exact (integral_nonneg (fun ω => (localChangedSiteIntegrand_posSemidef d a b ω).nonneg)).posSemidef

/-- Exact trace of the actual local tensor; no moment/positivity premise is supplied by the consumer. -/
theorem haarChangedSiteTensor_trace (d : ℕ) [NeZero d] (a b : Bool) :
    Matrix.trace (haarChangedSiteTensor d a b) =
      (d:ℂ)*(if a then (d:ℂ)-1 else 1)*(if b then (d:ℂ)-1 else 1) := by
  let L := (Matrix.traceLinearMap ((Fin d × Fin d) × Fin d) ℝ ℂ).toContinuousLinearMap
  have h := L.integral_comp_comm (localChangedSiteIntegrand_integrable d a b)
  change (∫ ω, Matrix.trace (localChangedSiteIntegrand d a b ω) ∂haarBasisRecords d) =
    Matrix.trace (∫ ω, localChangedSiteIntegrand d a b ω ∂haarBasisRecords d) at h
  rw [haarChangedSiteTensor,Matrix.trace_smul,← h]
  simp [localChangedSiteIntegrand_trace,Complex.real_smul]
  ring_nf

/-- The trace of the changed-site tensor is d(d−1)^(a+b). -/
theorem haarChangedSiteTensor_trace_power (d : ℕ) [NeZero d] (a b : Bool) :
    Matrix.trace (haarChangedSiteTensor d a b) = (d:ℂ)*((d:ℂ)-1)^(a.toNat+b.toNat) := by
  rw [haarChangedSiteTensor_trace]
  cases a <;> cases b <;> simp [pow_two,mul_assoc]

/-- All four local input choices have the actual common changed-site trace bound. -/
theorem haarChangedSiteTensor_trace_le (d : ℕ) [NeZero d] (hd : 2 ≤ d) (a b : Bool) :
    (Matrix.trace (haarChangedSiteTensor d a b)).re ≤ (d:ℝ)*((d:ℝ)-1)^2 := by
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 ≤ (d:ℝ)*(((d:ℝ)-1)^2-1) := mul_nonneg (by positivity) (by nlinarith)
  have h2 : 0 ≤ (d:ℝ)*((d:ℝ)-1)*((d:ℝ)-2) :=
    mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  rw [haarChangedSiteTensor_trace]
  cases a <;> cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Complex.mul_re,
    Complex.sub_re,Complex.natCast_re,Complex.one_re,Complex.sub_im,Complex.natCast_im,
    Complex.one_im,mul_zero,sub_zero,mul_one] <;> nlinarith

/-- The actual four-block changed-site tensor contracts against every genuine unitary with cost C_d. -/
theorem haarChangedSite_four_unitary_bound (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (a b : Fin 4 → Bool)
    (U : Matrix (Fin 4 → ((Fin d × Fin d) × Fin d)) (Fin 4 → ((Fin d × Fin d) × Fin d)) ℂ)
    (hU : U ∈ unitary _) :
    ‖Matrix.trace (wickTensorMatrix (fun v : Fin 4 => haarChangedSiteTensor d (a v) (b v))*U)‖ ≤
      (d:ℝ)^4*((d:ℝ)-1)^8 := by
  let K := fun v : Fin 4 => haarChangedSiteTensor d (a v) (b v)
  have hK : ∀ v, (K v).PosSemidef := fun v => haarChangedSiteTensor_posSemidef d (a v) (b v)
  calc
    ‖Matrix.trace (wickTensorMatrix K*U)‖ ≤ (Matrix.trace (wickTensorMatrix K)).re :=
      posSemidef_trace_unitary_le _ _ (wickTensorMatrix_posSemidef K hK) hU
    _ = ∏ v, (Matrix.trace (K v)).re := wickTensorMatrix_trace_re K hK
    _ ≤ ∏ _v : Fin 4, (d:ℝ)*((d:ℝ)-1)^2 := Finset.prod_le_prod₀
      (fun v _ => (RCLike.nonneg_iff.mp (hK v).trace_nonneg).1)
      (fun v _ => haarChangedSiteTensor_trace_le d hd (a v) (b v))
    _ = _ := by simp; ring_nf

end CertificationGaussian
