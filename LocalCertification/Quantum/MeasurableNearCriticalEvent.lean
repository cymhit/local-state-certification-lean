import LocalCertification.Quantum.UniformCalibrationEvent
import LocalCertification.Quantum.MeasurablePOVMZeroScore

/-! Common compact target events for both sides of every fixed nearcritical window.
The same events and constants precede epsilon, confidence and arbitrary outcome spaces. -/
set_option autoImplicit false
open MeasureTheory Matrix Metric Set Filter LocalCertification.Extremal
open scoped ENNReal ComplexOrder Topology
noncomputable section
universe u
namespace LocalCertification.Quantum

def measurableNearCriticalFailure (d j n : ℕ) : ℝ :=
  ((2*j+1 : ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)) +
    2*Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3)

theorem measurableNearCriticalFailure_nonneg (d j n : ℕ) :
    0 ≤ measurableNearCriticalFailure d j n := by
  unfold measurableNearCriticalFailure
  positivity

theorem measurableNearCriticalFailure_tendsto {d : ℕ} (hd : 2 ≤ d) (j : ℕ) :
    Tendsto (measurableNearCriticalFailure d j) atTop (nhds 0) := by
  have hlog : 0 < Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < d by omega))
  have h1 := nat_pow_exp_decay (Real.log (d:ℝ)/4) (by positivity) 0
  have h3 := (nat_pow_exp_decay (Real.log (d:ℝ)/16) (by positivity) 0).comp
    (tendsto_pow_atTop (by decide : (3:ℕ) ≠ 0) : Tendsto (fun n : ℕ => n^3) atTop atTop)
  simp only [pow_zero, one_mul] at h1
  simp only [pow_zero, one_mul, Function.comp_def, Nat.cast_pow] at h3
  change Tendsto (fun n : ℕ => ((2*j+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)) +
    2*Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3)) atTop (nhds 0)
  simpa only [mul_zero, add_zero] using
    (h1.const_mul (((2*j+1:ℕ):ℝ))).add (h3.const_mul 2)

theorem measurableNearCriticalFailure_ofReal_tendsto {d : ℕ} (hd : 2 ≤ d) (j : ℕ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (measurableNearCriticalFailure d j n)) atTop (nhds 0) := by
  simpa only [ENNReal.ofReal_zero, Function.comp_def] using
    (ENNReal.continuous_ofReal.tendsto 0).comp (measurableNearCriticalFailure_tendsto hd j)

private theorem ofReal_two_failures (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (ENNReal.ofReal a + ENNReal.ofReal c) + (ENNReal.ofReal b + ENNReal.ofReal c) =
      ENNReal.ofReal (a+b+2*c) := by
  rw [← ENNReal.ofReal_add ha hc, ← ENNReal.ofReal_add hb hc,
    ← ENNReal.ofReal_add (add_nonneg ha hc) (add_nonneg hb hc)]
  congr 1
  ring

theorem measurableNearCritical_positive_eventually_uniform {d : ℕ} [NeZero d] (hd : 2 ≤ d) (j : ℕ) (hj : 1 ≤ j)
    (bmin bmax : ℝ) (hmin : 0 < bmin) (hI : bmin ≤ bmax) (hmax : bmax < 1) :
    ∃ Cj Cp : ℝ, 0 < Cj ∧ 0 < Cp ∧ ∀ᶠ n : ℕ in atTop,
      ∃ (hNj : (quditDualCertificate hd j).maxNode ≤ n)
        (hNp : (quditDualCertificate hd (j-1)).maxNode ≤ n)
        (good : Set (sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)),
      IsCompact good ∧
      CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) goodᶜ ≤
        ENNReal.ofReal (measurableNearCriticalFailure d j n) ∧
      ∀ ψ ∈ good, ∀ b : ℝ, ∀ (hl : bmin ≤ b) (hu : b ≤ bmax),
        ∃ (hlj : uncalibratedLowFidelity hd j (spherePureVector ψ) hNj < b)
          (hlp : uncalibratedLowFidelity hd (j-1) (spherePureVector ψ) hNp < b),
        ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
          (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
          (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd j (spherePureVector ψ) hNj b (hmin.trans_le hl) (hu.trans_lt hmax)) s -
            (MeasurablePOVM.product M).bornDensity (calibratedLowState hd j (spherePureVector ψ) hNj b (hmin.trans_le hl) (hu.trans_lt hmax) hlj) s)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ Cj/(n:ℝ)^(j+1) ∧
          (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd (j-1) (spherePureVector ψ) hNp b (hmin.trans_le hl) (hu.trans_lt hmax)) s -
            (MeasurablePOVM.product M).bornDensity (calibratedLowState hd (j-1) (spherePureVector ψ) hNp b (hmin.trans_le hl) (hu.trans_lt hmax) hlp) s)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ Cp/(n:ℝ)^j := by
  obtain ⟨Cj,hCj,hjEvent⟩ := measurableExponential_hard_states_uniform.{u} hd j bmin bmax hmin hI hmax
  obtain ⟨Cp,hCp,hpEvent⟩ := measurableExponential_hard_states_uniform.{u} hd (j-1) bmin bmax hmin hI hmax
  refine ⟨Cj,Cp,hCj,hCp,?_⟩
  filter_upwards [hjEvent,hpEvent] with n hjEvent hpEvent
  obtain ⟨hNj,hcompactj,hprobj,hpairj⟩ := hjEvent
  obtain ⟨hNp,hcompactp,hprobp,hpairp⟩ := hpEvent
  let good := measurableDualSphereGoodEvent hd j hNj (exponentialOverlapCutoff d n) ∩
    measurableDualSphereGoodEvent hd (j-1) hNp (exponentialOverlapCutoff d n)
  refine ⟨hNj,hNp,good,hcompactj.inter hcompactp,?_,?_⟩
  · change CertificationGaussian.canonicalSphereMeasure
      (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))
      (measurableDualSphereGoodEvent hd j hNj (exponentialOverlapCutoff d n) ∩
        measurableDualSphereGoodEvent hd (j-1) hNp (exponentialOverlapCutoff d n))ᶜ ≤ _
    rw [Set.compl_inter]
    have hbound := (measure_union_le
      (measurableDualSphereGoodEvent hd j hNj (exponentialOverlapCutoff d n))ᶜ
      (measurableDualSphereGoodEvent hd (j-1) hNp (exponentialOverlapCutoff d n))ᶜ).trans
      (add_le_add hprobj hprobp)
    refine hbound.trans_eq ?_
    rw [ofReal_two_failures _ _ _ (by positivity) (by positivity) (by positivity)]
    congr 1
    have hp : j-1+1=j := Nat.sub_add_cancel hj
    change ((j+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)) +
      ((j-1+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)) +
      2*Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3) =
      ((2*j+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)) +
      2*Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3)
    rw [hp]
    push_cast
    ring
  · intro ψ hψ b hl hu
    obtain ⟨hlj,hinfoj⟩ := hpairj ψ hψ.1 b hl hu
    obtain ⟨hlp,hinfop⟩ := hpairp ψ hψ.2 b hl hu
    refine ⟨hlj,hlp,?_⟩
    intro Ω _ M
    exact ⟨hinfoj Ω M, by simpa only [Nat.sub_add_cancel hj] using (hinfop Ω M)⟩

theorem measurableNearCritical_positive_eventually {d : ℕ} [NeZero d] (hd : 2 ≤ d) (j : ℕ) (hj : 1 ≤ j)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ Cj Cp : ℝ, 0 < Cj ∧ 0 < Cp ∧ ∀ᶠ n : ℕ in atTop,
      ∃ (hNj : (quditDualCertificate hd j).maxNode ≤ n)
        (hNp : (quditDualCertificate hd (j-1)).maxNode ≤ n)
        (good : Set (sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)),
      IsCompact good ∧
      CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) goodᶜ ≤
        ENNReal.ofReal (measurableNearCriticalFailure d j n) ∧
      ∀ ψ ∈ good,
        ∃ (hlj : uncalibratedLowFidelity hd j (spherePureVector ψ) hNj < b)
          (hlp : uncalibratedLowFidelity hd (j-1) (spherePureVector ψ) hNp < b),
        ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
          (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
          (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd j (spherePureVector ψ) hNj b hb0 hb1) s -
            (MeasurablePOVM.product M).bornDensity (calibratedLowState hd j (spherePureVector ψ) hNj b hb0 hb1 hlj) s)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ Cj/(n:ℝ)^(j+1) ∧
          (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd (j-1) (spherePureVector ψ) hNp b hb0 hb1) s -
            (MeasurablePOVM.product M).bornDensity (calibratedLowState hd (j-1) (spherePureVector ψ) hNp b hb0 hb1 hlp) s)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ Cp/(n:ℝ)^j := by
  obtain ⟨C, Cp, hC, hCp, hevent⟩ := measurableNearCritical_positive_eventually_uniform.{u} hd j hj
    b b hb0 le_rfl hb1
  refine ⟨C, Cp, hC, hCp, ?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨hNj,hNp,good, hc, hp, hall⟩ := hn
  exact ⟨hNj,hNp,good, hc, hp, fun ψ hψ => hall ψ hψ b le_rfl le_rfl⟩

theorem measurableNearCritical_zero_eventually_uniform {d : ℕ} [NeZero d] (hd : 2 ≤ d) (bmin bmax : ℝ) (hmin : 0 < bmin) (hI : bmin ≤ bmax) (hmax : bmax < 1) :
    ∃ C0 Cp : ℝ, 0 < C0 ∧ 0 < Cp ∧ ∀ᶠ n : ℕ in atTop,
      ∃ (hN : (quditDualCertificate hd 0).maxNode ≤ n)
        (good : Set (sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)),
      IsCompact good ∧
      CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) goodᶜ ≤
        ENNReal.ofReal (measurableNearCriticalFailure d 0 n) ∧
      ∀ ψ ∈ good, ∀ b : ℝ, ∀ (hl : bmin ≤ b) (hu : b ≤ bmax), ∃ hlb : uncalibratedLowFidelity hd 0 (spherePureVector ψ) hN < b,
        ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
          (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
          (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd 0 (spherePureVector ψ) hN b (hmin.trans_le hl) (hu.trans_lt hmax)) s -
            (MeasurablePOVM.product M).bornDensity (calibratedLowState hd 0 (spherePureVector ψ) hN b (hmin.trans_le hl) (hu.trans_lt hmax) hlb) s)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ C0/(n:ℝ) ∧
          (∫ s, ((MeasurablePOVM.product M).bornDensity (spherePureVector ψ).state s-1)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ Cp := by
  obtain ⟨C0,hC0,hEvent⟩ := measurableExponential_hard_states_uniform.{u} hd 0 bmin bmax hmin hI hmax
  refine ⟨C0,7,hC0,by norm_num,?_⟩
  filter_upwards [hEvent, CertificationGaussian.productFrame_common_sphere_eventually hd
    {0} (fun _ => 1) (by simp), eventually_ge_atTop 1] with n hEvent hzero hn
  obtain ⟨hN,hcompact,hprob,hpair⟩ := hEvent
  let zeroGood : Set (sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1) :=
    {ψ | ∀ T ∈ CertificationGaussian.signedProductFrameFamily (S := Fin n) (I := Fin d) {0} (fun _ => 1),
      CertificationGaussian.gaussianFrameSphereScore T ψ ≤
        (1+6/(n:ℝ))*CertificationGaussian.kernelVarianceScale d n {0} (fun _ => 1)}
  have hzeroCompact : IsCompact zeroGood := CertificationGaussian.productFrame_good_isCompact d n {0} (fun _ => 1)
  let good := measurableDualSphereGoodEvent hd 0 hN (exponentialOverlapCutoff d n) ∩ zeroGood
  refine ⟨hN,good,hcompact.inter hzeroCompact,?_,?_⟩
  · change CertificationGaussian.canonicalSphereMeasure
      (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n))
      (measurableDualSphereGoodEvent hd 0 hN (exponentialOverlapCutoff d n) ∩ zeroGood)ᶜ ≤ _
    rw [Set.compl_inter]
    have hbound := (measure_union_le
      (measurableDualSphereGoodEvent hd 0 hN (exponentialOverlapCutoff d n))ᶜ zeroGoodᶜ).trans
      (add_le_add hprob hzero)
    refine hbound.trans_eq ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    change ((0+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)) +
        Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3) +
        Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3) =
      ((2*0+1:ℕ):ℝ)*Real.exp (-(Real.log (d:ℝ)/4)*(n:ℝ)) +
        2*Real.exp (-(Real.log (d:ℝ)/16)*(n:ℝ)^3)
    ring
  · intro ψ hψ b hl hu
    obtain ⟨hlb,hinfo⟩ := hpair ψ hψ.1 b hl hu
    refine ⟨hlb,?_⟩
    intro Ω _ M
    refine ⟨by simpa only [Nat.zero_add, pow_one] using (hinfo Ω M),?_⟩
    have hv : CertificationGaussian.kernelVarianceScale d n {0} (fun _ => 1) = 1 := by
      change (∑ k ∈ ({0} : Finset ℕ), (1:ℝ)^2 / ((Nat.choose n k:ℝ)*((d-1:ℕ):ℝ)^k)) = 1
      simp
    have hfamily : ∀ T ∈ CertificationGaussian.signedProductFrameFamily (S := Fin n) (I := Fin d)
        {0} (fun _ => 1), CertificationGaussian.gaussianFrameSphereScore T ψ ≤ 7 := by
      intro T hT
      have h := hψ.2 T hT
      rw [hv, mul_one] at h
      have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hdiv := div_le_self (by norm_num : (0:ℝ) ≤ 6) hnR
      exact h.trans ((add_le_add le_rfl hdiv).trans_eq (by norm_num))
    have hP := pure_product_referenceL2_sq_le_of_frameFamily hd ψ 7 hfamily M
    calc
      _ = ∫ s, ((MeasurablePOVM.product M).bornDensity (spherePureVector ψ).state s -
          (MeasurablePOVM.product M).bornDensity (quditMaximallyMixed d n) s)^2
          ∂(MeasurablePOVM.product M).traceReference := by
        apply integral_congr_ae
        refine ae_of_all _ (fun s => ?_)
        have hm : (MeasurablePOVM.product M).bornDensity (quditMaximallyMixed d n) s = 1 :=
          (MeasurablePOVM.product M).bornDensity_maximallyMixed s
        dsimp only
        rw [hm]
      _ ≤ 7 := hP

theorem measurableNearCritical_zero_eventually {d : ℕ} [NeZero d] (hd : 2 ≤ d) (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ C0 Cp : ℝ, 0 < C0 ∧ 0 < Cp ∧ ∀ᶠ n : ℕ in atTop,
      ∃ (hN : (quditDualCertificate hd 0).maxNode ≤ n)
        (good : Set (sphere (0 : EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) 1)),
      IsCompact good ∧
      CertificationGaussian.canonicalSphereMeasure (EuclideanSpace ℂ (CertificationGaussian.QuditIndex d n)) goodᶜ ≤
        ENNReal.ofReal (measurableNearCriticalFailure d 0 n) ∧
      ∀ ψ ∈ good, ∃ hlb : uncalibratedLowFidelity hd 0 (spherePureVector ψ) hN < b,
        ∀ (Ω : Fin n → Type u) [∀ i, MeasurableSpace (Ω i)]
          (M : ∀ i, MeasurablePOVM (Ω i) (Fin d)),
          (∫ s, ((MeasurablePOVM.product M).bornDensity (calibratedHighState hd 0 (spherePureVector ψ) hN b hb0 hb1) s -
            (MeasurablePOVM.product M).bornDensity (calibratedLowState hd 0 (spherePureVector ψ) hN b hb0 hb1 hlb) s)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ C0/(n:ℝ) ∧
          (∫ s, ((MeasurablePOVM.product M).bornDensity (spherePureVector ψ).state s-1)^2
            ∂(MeasurablePOVM.product M).traceReference) ≤ Cp := by
  obtain ⟨C, Cp, hC, hCp, hevent⟩ := measurableNearCritical_zero_eventually_uniform.{u} hd
    b b hb0 le_rfl hb1
  refine ⟨C, Cp, hC, hCp, ?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨hN,good, hc, hp, hall⟩ := hn
  exact ⟨hN,good, hc, hp, fun ψ hψ => hall ψ hψ b le_rfl le_rfl⟩

end LocalCertification.Quantum
