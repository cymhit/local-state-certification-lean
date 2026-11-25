import LocalCertification.Quantum.MeasurablePOVMCalibration
import LocalCertification.Quantum.ConstantHardPair

/-! The constant-order hard pair under arbitrary measurable POVMs.

The denominator is the original fixed target/uniform mixture. Its reference
density dominates a fixed fraction of the numerator density. Normalization
then bounds chi-square independently of the Hilbert dimension and outcome
space, giving the constant-order information bound for the enlarged model.
-/

set_option autoImplicit false
open MeasureTheory Matrix InformationTheory
open scoped ENNReal
noncomputable section
namespace LocalCertification.Quantum.MeasurablePOVM
variable {d n : Nat} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]

theorem bornDensity_constantLowState
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n))
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) (s : Ω) :
    M.bornDensity (constantLowState ψ b hb0 hb1) s =
      (b/2)*M.bornDensity ψ.state s + (1-b/2) := by
  change M.bornDensity (targetMixture ψ (quditMaximallyMixed d n) (b/2) _ _) s = _
  rw [M.bornDensity_targetMixture]
  change (b/2)*M.bornDensity ψ.state s + (1-b/2)*M.bornDensity
    (QIT.State.maximallyMixed (CertificationGaussian.QuditIndex d n)) s = _
  rw [M.bornDensity_maximallyMixed, mul_one]

theorem bornDensity_constantLowState_domination
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n))
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) (s : Ω) :
    0 < M.bornDensity (constantLowState ψ b hb0 hb1) s ∧
      (b/2)*M.bornDensity ψ.state s ≤ M.bornDensity (constantLowState ψ b hb0 hb1) s := by
  rw [M.bornDensity_constantLowState]
  have hnonneg := M.bornDensity_nonneg ψ.state s
  constructor <;> nlinarith

/-- A true dimension-independent information bound for every measurable POVM,
including joint POVMs. It therefore applies to all allowed local products. -/
theorem constantLowState_born_klDiv
    (M : MeasurablePOVM Ω (CertificationGaussian.QuditIndex d n))
    (ψ : QIT.PureVector (CertificationGaussian.QuditIndex d n))
    (b : ℝ) (hb0 : 0<b) (hb1 : b<1) :
    klDiv (M.born ψ.state) (M.born (constantLowState ψ b hb0 hb1)) ≤
      ENNReal.ofReal (4/b+2) := by
  let ρ := ψ.state
  let σ := constantLowState ψ b hb0 hb1
  let f := M.bornDensity ρ
  let g := M.bornDensity σ
  have hf (s : Ω) : 0 ≤ f s := M.bornDensity_nonneg ρ s
  have hg (s : Ω) : 0 < g s := (M.bornDensity_constantLowState_domination ψ b hb0 hb1 s).1
  have hdom (s : Ω) : (b/2)*f s ≤ g s :=
    (M.bornDensity_constantLowState_domination ψ b hb0 hb1 s).2
  have hpoint (s : Ω) : (f s-g s)^2/g s ≤ (4/b)*f s+2*g s := by
    have hmul := mul_le_mul_of_nonneg_left (hdom s) (hf s)
    have hfg : (f s)^2 ≤ (2/b)*f s*g s := by
      calc
        _ ≤ (2*f s*g s)/b := (le_div_iff₀ hb0).mpr (by nlinarith)
        _ = _ := by ring
    apply (div_le_iff₀ (hg s)).mpr
    have hsq : (f s-g s)^2 ≤ 2*(f s)^2+2*(g s)^2 := by nlinarith [sq_nonneg (f s+g s)]
    calc
      _ ≤ 2*(f s)^2+2*(g s)^2 := hsq
      _ ≤ 2*((2/b)*f s*g s)+2*(g s)^2 :=
        add_le_add (mul_le_mul_of_nonneg_left hfg (by norm_num)) le_rfl
      _ = _ := by ring
  have hi : Integrable (fun s => (4/b)*f s+2*g s) M.traceReference :=
    ((M.bornDensity_integrable ρ).const_mul (4/b)).add ((M.bornDensity_integrable σ).const_mul 2)
  have hnonneg (s : Ω) : 0 ≤ (4/b)*f s+2*g s :=
    add_nonneg (mul_nonneg (div_nonneg (by norm_num) hb0.le) (hf s))
      (mul_nonneg (by norm_num) (hg s).le)
  have hkl := Information.DensityInformation.klDiv_le_reference_chiSquare M.traceReference
    (M.born ρ) (M.born σ) f g (M.bornDensity_measurable ρ) (M.bornDensity_measurable σ)
    hf hg (M.born_eq_withDensity ρ) (M.born_eq_withDensity σ)
  refine hkl.trans ((lintegral_mono (fun s => ENNReal.ofReal_le_ofReal (hpoint s))).trans_eq ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnonneg),
    integral_add ((M.bornDensity_integrable ρ).const_mul (4/b)) ((M.bornDensity_integrable σ).const_mul 2),
    integral_const_mul, integral_const_mul]
  change ENNReal.ofReal ((4/b)*(∫ s, M.bornDensity ρ s ∂M.traceReference)+
    2*(∫ s, M.bornDensity σ s ∂M.traceReference)) = _
  rw [M.integral_bornDensity, M.integral_bornDensity, mul_one, mul_one]

end LocalCertification.Quantum.MeasurablePOVM
