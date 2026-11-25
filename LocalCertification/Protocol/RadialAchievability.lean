import LocalCertification.Quantum.RadialWeylScore
import LocalCertification.Protocol.CardinalityAchievability

set_option autoImplicit false
open Matrix MeasureTheory ProbabilityTheory Filter CertificationGaussian LocalCertification.Quantum LocalCertification.Extremal LocalCertification.Probability
open scoped BigOperators ENNReal Matrix.Norms.L2Operator Topology
noncomputable section
namespace LocalCertification.Protocol
universe u

/-- The full-second scalar is the genuine nonnegative Lambda of the squared original coefficients. -/
theorem squared_traceScale_eq_complementLambda (d n r : ℕ) (lam : ℕ → ℝ) :
    cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)=
      complementLambda d n r (fun j => (lam j)^2) := by
  simp only [cardinalityReadoutTraceScale,complementLambda,abs_sq]

theorem squared_traceScale_nonneg (d n r : ℕ) (hd : 1≤d) (lam : ℕ → ℝ) :
    0≤cardinalityReadoutTraceScale d n r (fun j => (lam j)^2) := by
  have hd' : (0:ℝ)≤(d:ℝ)-1 := by
    have hd' : (1:ℝ)≤d := by exact_mod_cast hd
    linarith
  unfold cardinalityReadoutTraceScale
  positivity

/-- Fixed coefficients bound the actual full-second scalar by n^r, including r=0. -/
theorem squared_traceScale_le_polynomial (d n r : ℕ) (hd : 1≤d) (hn : 1≤n) (lam : ℕ → ℝ) :
    cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)≤
      complementLambdaCoefficient d r (fun j => (lam j)^2)*(n:ℝ)^r := by
  rw [squared_traceScale_eq_complementLambda]
  exact complementLambda_le_polynomial d n r hd hn _

/-- A fixed n^-3 error is eventually below every fixed positive margin. -/
theorem eventually_inverse_cube_error (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,C*((n:ℝ)^3)⁻¹≤ε := by
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)^3)⁻¹) atTop (nhds 0) := by
    simpa only [Function.comp_apply,inv_pow,zero_pow (by omega : 3≠0)] using
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).pow 3
  have hc : Tendsto (fun n : ℕ => C*((n:ℝ)^3)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn
  exact hn.le

variable {H : Type u} [MeasurableSpace H] [TopologicalSpace H] [BorelSpace H]
  [CompactSpace H] [SecondCountableTopology H] {d : ℕ} [NeZero d]

/-- Actual radial B/S and full-M errors yield the explicit raw fixed-block test with the n^r budget.
All thresholds precede n, the target, every input state, and delta; the only remaining event premises
are the literal original operator controls. No moment, law, or independent-copy premise is supplied. -/
theorem radialWeyl_achievable_eventually (hd : 2≤d)
    (setting : H → LocalUnitary d) (hs : Continuous setting) (ν : Measure H) [IsProbabilityMeasure ν]
    (r : ℕ) (lam : ℕ → ℝ) (h0 : lam 0=1) (C₁ C₂ CM E a b : ℝ)
    (hE : 0≤E) (he : ∀ w : ℕ,radialSecondCoefficient d r lam w≤E)
    (ha : a≤1) (hb0 : 0≤b) (hb1 : b≤1)
    (hg : 0<scoreWindowGap (lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam))
      (upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)) a b) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ ψ : QIT.PureVector (QuditIndex d n),
      radialReadoutPolarControl d n r (ν.prod (uniformFiniteOutcome d))
        (fun p : H × Fin d => (setting p.1,p.2)) lam localWeylFin 0 C₁ C₂ (WithLp.toLp 2 ψ.amp) →
      ‖cardinalityReadoutSecond d (ν.prod (uniformFiniteOutcome d))
          (fun p : H × Fin d => (setting p.1,p.2)) r lam ((d:ℝ)^n) ψ.amp-
        (cardinalityReadoutTraceScale d n r (fun j => (lam j)^2) •
          (1 : Matrix (QuditIndex d n) (QuditIndex d n) ℂ)+
        cardinalityReadoutAuxiliary d (ν.prod (uniformFiniteOutcome d))
          (fun p : H × Fin d => (setting p.1,p.2)) r lam ((d:ℝ)^n) ψ.amp)‖≤CM*((n:ℝ)^3)⁻¹ →
      ∀ δ : ℝ,0<δ → δ≤1/2 →
        let l := lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
        let u := upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
        let V := cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)+E+1
        Valid (cardinalityMajorityProtocol setting hs ν r lam ψ l u a b V δ) ψ a b δ ∧
        Capped (cardinalityMajorityProtocol setting hs ν r lam ψ l u a b V δ)
          (blockCount δ*blockCopies V (scoreWindowGap l u a b)) ∧
        expectedBudget ψ a b δ≤ENat.toENNReal (maximumBudget ψ a b δ) ∧
        ENat.toENNReal (maximumBudget ψ a b δ)≤ENNReal.ofReal (K*(n:ℝ)^r*Real.log (1/δ)) := by
  let l := lowerEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let u := upperEnvelope ((d:ℝ)+1) (radialPolynomial d r lam)
  let Δ := scoreWindowGap l u a b
  let A := complementLambdaCoefficient d r (fun j => (lam j)^2)
  have hA : 0≤A := complementLambdaCoefficient_nonneg d r (by omega) _
  have hΔ : 0<Δ := hg
  refine ⟨1548*(A+E+1)/Δ^2,by positivity,?_⟩
  filter_upwards [eventually_inverse_cube_error (C₁+2*|1-l|) (Δ/4) (by positivity),
    eventually_inverse_cube_error (C₁+2*|1-u|) (Δ/4) (by positivity),
    eventually_inverse_cube_error (C₂+CM) 1 (by norm_num),eventually_ge_atTop 1] with n hL hU hM hn
  intro ψ hcontrol hrem δ hδ hδhalf
  let Q := radialWeylPolarMatrix r (WithLp.toLp 2 ψ.amp)
  let c : RadialWeylIndex d n r → ℝ := fun w => radialFirstCoefficient d r lam (weylWeight w.val)
  let e : RadialWeylIndex d n r → ℝ := fun w => radialSecondCoefficient d r lam (weylWeight w.val)
  let nu := cardinalityReadoutTraceScale d n r (fun j => (lam j)^2)
  have hq : 1<(d:ℝ)+1 := by
    have : (2:ℝ)≤d := by exact_mod_cast hd
    linarith
  have hc := radialWeyl_coefficients (d:=d) (n:=n) r lam h0 (by omega)
  have hL' : C₁*((n:ℝ)^3)⁻¹+|1-l| *(2*((n:ℝ)^3)⁻¹)≤Δ/4 := by nlinarith [hL]
  have hU' : C₁*((n:ℝ)^3)⁻¹+|1-u| *(2*((n:ℝ)^3)⁻¹)≤Δ/4 := by nlinarith [hU]
  let μ := ν.prod (uniformFiniteOutcome d)
  let record : H × Fin d → ComplexUnitary (Fin d) × Fin d := fun p => (setting p.1,p.2)
  let ψv : EuclideanSpace ℂ (QuditIndex d n) := WithLp.toLp 2 ψ.amp
  have hB := radialWeyl_first_matrix_error (d:=d) (n:=n) r μ record lam C₁ C₂ ψv hcontrol
  have hfull := radialWeyl_full_matrix_error (d:=d) (n:=n) r μ record lam C₁ C₂ CM nu ψv hcontrol hrem
  have hP := radialWeyl_target_projector (d:=d) (n:=n) r μ record lam C₁ C₂ ψ hcontrol
  have hr := cardinality_achievable_of_spectral_control (d:=d) (n:=n) (J:=RadialWeylIndex d n r) setting hs ν r lam ψ Q hcontrol.1
    (radialWeylIdentity d n r) c e hc.1 l u E nu (C₁*((n:ℝ)^3)⁻¹)
    ((C₂+CM)*((n:ℝ)^3)⁻¹) (2*((n:ℝ)^3)⁻¹) a b δ
    (envelope_zero_bounds _ hq _).1 (envelope_zero_bounds _ hq _).2 hE
    (squared_traceScale_nonneg d n r (by omega) lam)
    (fun w hw => (hc.2 w hw).1) (fun w hw => (hc.2 w hw).2) (fun w => he _)
    hB hfull hP
    ha hb0 hb1 hg hL' hU' hM hδ hδhalf
  refine ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hp : (1:ℝ)≤(n:ℝ)^r := one_le_pow₀ hn'
  have hnu := squared_traceScale_le_polynomial d n r (by omega) hn lam
  have hv : nu+E+1≤(A+E+1)*(n:ℝ)^r := by dsimp [nu,A] at *; nlinarith
  have hlog : 0≤Real.log (1/δ) := Real.log_nonneg (by
    apply (le_div_iff₀ hδ).mpr
    linarith)
  have hmul := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (show (0:ℝ)≤1548 by norm_num)) (sq_nonneg Δ)) hlog
  convert hmul using 1
  dsimp only [Δ]
  ring

end LocalCertification.Protocol
