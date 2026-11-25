import LocalCertification.Quantum.WeylOrbitProjection
import LocalCertification.Quantum.IsometryEnvelopes
import LocalCertification.Quantum.RadialPolynomial
import CertificationGaussian.RadialReadoutPolar

set_option autoImplicit false
open Matrix CertificationGaussian Classical
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
namespace LocalCertification.Quantum
variable {d n : ℕ} [NeZero d]

omit [NeZero d] in
/-- The abstract radial support is exactly the canonical nonidentity Weyl support. -/
theorem radialBellSupport_weyl (w : WeylLabel d n) :
    radialBellSupport (0 : ZMod d × ZMod d) w = weylSupport w := rfl

/-- The tensor family in the radial analysis is the actual canonical qudit Weyl family. -/
theorem wickTensorMatrix_localWeyl (w : WeylLabel d n) :
    wickTensorMatrix (fun s => localWeylFin (w s)) = quditWeyl w := rfl

theorem localWeylFin_unitary (w : ZMod d × ZMod d) :
    localWeylFin w ∈ unitary (Matrix (Fin d) (Fin d) ℂ) :=
  ⟨localWeylFin_adjoint_mul w,localWeylFin_mul_adjoint w⟩

theorem localWeylLabel_card : Fintype.card (ZMod d × ZMod d)=d^2 := by simp [sq]

/-- An alias of the original radial label subtype, not an independently chosen low family. -/
abbrev RadialWeylIndex (d n r : ℕ) [NeZero d] :=
  ↥(radialLowLabels (S:=Fin n) d r (0 : ZMod d × ZMod d))

/-- The radial logarithmic cutoff selects precisely the low-weight Weyl labels at that cutoff. -/
def radialWeylIndexEquiv (d n r : ℕ) [NeZero d] :
    RadialWeylIndex d n r ≃ LowWeylIndex d n (radialWeightCutoff d r n) where
  toFun w := ⟨w.val,by simpa [radialLowLabels,radialBellSupport_weyl,weylWeight] using w.property⟩
  invFun w := ⟨w.val,by simpa [radialLowLabels,radialBellSupport_weyl,weylWeight] using w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def radialWeylIdentity (d n r : ℕ) [NeZero d] : RadialWeylIndex d n r :=
  (radialWeylIndexEquiv d n r).symm (lowWeylIdentity d n (radialWeightCutoff d r n))

@[simp] theorem radialWeylIdentity_val (r : ℕ) :
    (radialWeylIdentity d n r).val = 0 := rfl

theorem radialWeylLow_family (r : ℕ) (w : RadialWeylIndex d n r) :
    radialLowOrbitFamily d n r localWeylFin 0 w =
      lowWeylFamily d n (radialWeightCutoff d r n) (radialWeylIndexEquiv d n r w) := rfl

@[simp] theorem radialWeylLow_identity (r : ℕ) :
    radialLowOrbitFamily d n r localWeylFin 0 (radialWeylIdentity d n r)=1 :=
  quditWeyl_zero

/-- The distinguished coefficient is exactly one; every other actual low column has positive weight. -/
theorem radialWeyl_coefficients (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0=1) (hd : 0<d) :
    radialFirstCoefficient d r lam (radialBellSupport 0 (radialWeylIdentity d n r).val).card=1 ∧
      ∀ w : RadialWeylIndex d n r,w≠radialWeylIdentity d n r →
        LocalCertification.Extremal.lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)≤
          radialFirstCoefficient d r lam (radialBellSupport 0 w.val).card ∧
        radialFirstCoefficient d r lam (radialBellSupport 0 w.val).card≤
          LocalCertification.Extremal.upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam) := by
  constructor
  · simpa [radialBellSupport,radialFirstCoefficient_zero] using h0
  · intro w hw
    apply radialFirstCoefficient_envelope d r hd lam
    change 0<weylWeight w.val
    apply Nat.pos_of_ne_zero
    intro hz
    apply hw
    apply Subtype.ext
    exact (weylWeight_eq_zero w.val).mp hz

/-- A genuine identity column and the actual rectangular perturbation give a target projector bound. -/
theorem isometry_identity_column_error {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (V Q : Matrix I J ℂ) (i : J)
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖=1)
    (hV : rectangularEuclideanCLM V (EuclideanSpace.single i 1)=ψ)
    (hQ : ∀ x,‖rectangularEuclideanCLM Q x‖=‖x‖)
    (t : ℝ) (hD : ‖rectangularEuclideanCLM (V-Q)‖≤t) :
    ‖Q*Matrix.single i i (1:ℂ)*Qᴴ-Matrix.vecMulVec ψ (star ψ)‖≤2*t := by
  let e : EuclideanSpace ℂ J := EuclideanSpace.single i 1
  let q : EuclideanSpace ℂ I := rectangularEuclideanCLM Q e
  have he : ‖e‖=1 := by simp [e]
  have hq : ‖q‖=1 := (hQ e).trans he
  have hsub : rectangularEuclideanCLM (V-Q) e=ψ-q := by
    change Matrix.toEuclideanLin (V-Q) e=ψ-q
    rw [map_sub,LinearMap.sub_apply]
    change rectangularEuclideanCLM V e-rectangularEuclideanCLM Q e=ψ-q
    rw [hV]
  have hdist : ‖q-ψ‖≤t := by
    rw [norm_sub_rev,← hsub]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [he,mul_one]; exact hD)
  have hcol : (fun x => Q x i)=(q : I → ℂ) := by
    funext x
    simp [q,e,rectangularEuclideanCLM,Matrix.toEuclideanLin,Matrix.toLpLin_apply]
  rw [isometry_selected_column,hcol]
  exact (unit_rankOne_matrix_dist_le q ψ hq hψ).trans
    (mul_le_mul_of_nonneg_left hdist (by norm_num))

/-- The same CFC matrix in the actual radial event has the correct physical target column. -/
theorem radialWeyl_target_projector {Ω : Type*} [MeasurableSpace Ω]
    (r : ℕ) (μ : MeasureTheory.Measure Ω)
    (record : Ω → ComplexUnitary (Fin d) × Fin d) (lam : ℕ → ℝ)
    (C₁ C₂ : ℝ) (ψ : QIT.PureVector (QuditIndex d n))
    (h : radialReadoutPolarControl d n r μ record lam localWeylFin 0 C₁ C₂
      (WithLp.toLp 2 ψ.amp)) :
    let Q := matrixPolarCorrection (unitaryOrbitMatrix
      (radialLowOrbitFamily d n r localWeylFin 0) (WithLp.toLp 2 ψ.amp))
    ‖Q*Matrix.single (radialWeylIdentity d n r) (radialWeylIdentity d n r) (1:ℂ)*Qᴴ-
      ψ.state.matrix‖≤2*((n:ℝ)^3)⁻¹ := by
  dsimp only
  apply isometry_identity_column_error
    (unitaryOrbitMatrix (radialLowOrbitFamily d n r localWeylFin 0) (WithLp.toLp 2 ψ.amp))
    _ _ (WithLp.toLp 2 ψ.amp) (pure_amp_norm ψ)
  · ext i
    simp [rectangularEuclideanCLM,Matrix.toEuclideanLin,Matrix.toLpLin_apply,
      unitaryOrbitMatrix]
  · exact h.2.2.1
  · exact h.2.1

end LocalCertification.Quantum
