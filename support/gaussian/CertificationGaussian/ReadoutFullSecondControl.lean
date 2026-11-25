import CertificationGaussian.ReadoutPolarNorm
import CertificationGaussian.ReadoutGoodEvents

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The original signed trace scale is bounded by the original Lambda and hence by a fixed polynomial. -/
theorem cardinalityReadoutTraceScale_abs_le (d n r : ℕ) (hd : 1≤d) (hn : 1≤n) (lam : ℕ → ℝ) :
    |cardinalityReadoutTraceScale d n r lam|≤complementLambdaCoefficient d r lam*(n:ℝ)^r := by
  have hd' : (0:ℝ)≤(d:ℝ)-1 := by
    have h : (1:ℝ)≤d := by exact_mod_cast hd
    linarith
  have h : |cardinalityReadoutTraceScale d n r lam|≤complementLambda d n r lam := by
    unfold cardinalityReadoutTraceScale complementLambda
    calc
      _ ≤ ∑ j : Fin (r+1),|lam j.val*(n.choose j.val:ℝ)*((d:ℝ)-1)^j.val| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul,abs_mul,abs_of_nonneg (show (0:ℝ)≤(n.choose j.val:ℝ) by positivity),
          abs_of_nonneg (pow_nonneg hd' _)]
  exact h.trans (complementLambda_le_polynomial d n r hd hn lam)

/-- Fixed trace and operator constants absorb all radius terms into the same n^-3 error. -/
theorem readout_full_error_scalar_le (n r : ℕ) (hn : 1≤n)
    (A An Kb Ks h nu : ℝ) (hA : 0≤A) (hAn : 0≤An) (hKb : 0≤Kb) (hKs : 0≤Ks)
    (hh : |h|≤A*(n:ℝ)^r) (hnu : |nu|≤An*(n:ℝ)^r) :
    2*((n:ℝ)^(r+4))⁻¹*Ks+4*((n:ℝ)^3)⁻¹+
      4*((n:ℝ)^(r+4))⁻¹*|h| *Kb+4*(((n:ℝ)^(r+4))⁻¹)^2*(|nu|+h^2)≤
      (2*Ks+4+4*A*Kb+4*(An+A^2))*((n:ℝ)^3)⁻¹ := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  let δ : ℝ := ((n:ℝ)^(r+4))⁻¹
  let t : ℝ := ((n:ℝ)^3)⁻¹
  have hd0 : 0≤δ := by positivity
  have ht0 : 0≤t := by positivity
  have ht1 : t≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ hn1)
  have hdt : δ≤t := inv_anti₀ (pow_pos hn0 3) (pow_le_pow_right₀ hn1 (by omega))
  have hdp : δ*(n:ℝ)^r≤t := by
    have he : δ*(n:ℝ)^r=((n:ℝ)^4)⁻¹ := by dsimp [δ]; rw [pow_add]; field_simp
    rw [he]
    exact inv_anti₀ (pow_pos hn0 3) (pow_le_pow_right₀ hn1 (by omega))
  have hh' : δ*|h|≤A*t := calc
    _ ≤ δ*(A*(n:ℝ)^r) := mul_le_mul_of_nonneg_left hh hd0
    _ = A*(δ*(n:ℝ)^r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdp hA
  have hnu' : δ*|nu|≤An*t := calc
    _ ≤ δ*(An*(n:ℝ)^r) := mul_le_mul_of_nonneg_left hnu hd0
    _ = An*(δ*(n:ℝ)^r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdp hAn
  have hnu2 : δ^2*|nu|≤An*t := calc
    _ = δ*(δ*|nu|) := by ring
    _ ≤ δ*(An*t) := mul_le_mul_of_nonneg_left hnu' hd0
    _ ≤ 1*(An*t) := mul_le_mul_of_nonneg_right (hdt.trans ht1) (mul_nonneg hAn ht0)
    _ = _ := one_mul _
  have hhsq : δ^2*h^2≤A^2*t := calc
    _ = (δ*|h|)^2 := by rw [mul_pow,sq_abs]
    _ ≤ (A*t)^2 := pow_le_pow_left₀ (mul_nonneg hd0 (abs_nonneg h)) hh' 2
    _ = A^2*t^2 := mul_pow _ _ _
    _ ≤ A^2*t := mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg A)
  have hfirst : 2*δ*Ks≤2*Ks*t := by nlinarith [mul_le_mul_of_nonneg_right hdt hKs]
  have hthird : 4*δ*|h| *Kb≤4*A*Kb*t := by nlinarith [mul_le_mul_of_nonneg_right hh' hKb]
  change 2*δ*Ks+4*t+4*δ*|h| *Kb+4*δ^2*(|nu|+h^2)≤(2*Ks+4+4*A*Kb+4*(An+A^2))*t
  nlinarith

/-- The genuine full second-moment error after subtracting its original nu I and actual auxiliary S. -/
def cardinalityReadoutSecondError {Ω : Type*} [MeasurableSpace Ω]
    (d n r : ℕ) (μ : Measure Ω) (record : Ω → ComplexUnitary (Fin d) × Fin d)
    (lam : ℕ → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) : ℝ :=
  ‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
    (cardinalityReadoutSecond d μ record r lam ((d:ℝ)^n) ψ.ofLp-
      cardinalityReadoutTraceScale d n r (fun j => (lam j)^2) •
        (1:Matrix (QuditIndex d n) (QuditIndex d n) ℂ)-
      cardinalityReadoutAuxiliary d μ record r lam ((d:ℝ)^n) ψ.ofLp)‖

/-- All B/S and trace-scale hypotheses in the actual full-Haar second-moment radius estimate are discharged.
Only the original explicit high/low, common-radius, and true remainder good events remain. -/
theorem radialHaar_full_second_control_eventually (d r : ℕ) (hd : 2≤d) [NeZero d]
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin d) (Fin d) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ∀ e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex d n)) 1,
      ∀ x : Fin 2 × QuditIndex d n → ℝ,
      sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)∉
        radialHighSphereBad d n r lam W k0 ∪ radialLowSphereBad d n r W k0 →
      |gaussianRadius (QuditIndex d n) x-1|≤((n:ℝ)^(r+4))⁻¹ →
      ‖Matrix.toEuclideanCLM (n:=QuditIndex d n) (𝕜:=ℂ)
        (cardinalityReadoutRemainder (S:=Fin n) d (haarBasisRecords d) id r lam (complexCoordinate x))‖≤((n:ℝ)^3)⁻¹ →
      cardinalityReadoutSecondError d n r (haarBasisRecords d) id lam
        (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x))≤C*((n:ℝ)^3)⁻¹ := by
  obtain ⟨Kb,Ks,hKb,hKs,hE⟩ := radialHaarReadout_norm_eventually d r hd lam k0 hcard
  let A := complementLambdaCoefficient d r lam
  let An := complementLambdaCoefficient d r (fun j => (lam j)^2)
  have hA : 0≤A := complementLambdaCoefficient_nonneg d r (by omega) lam
  have hAn : 0≤An := complementLambdaCoefficient_nonneg d r (by omega) _
  refine ⟨2*Ks+4+4*A*Kb+4*(An+A^2),by positivity,?_⟩
  filter_upwards [hE,eventually_ge_atTop 2] with n he hn
  intro W h0 hHS e₀ x hgood hr hZ
  have hnorm := he W h0 hHS (sphereDirection e₀ (complexGaussianLift (QuditIndex d n) x)) hgood
  have h := cardinalityHaar_second_error_of_good_radius d n r hd hn lam Kb Ks x e₀ hr hZ hnorm.1 hnorm.2
  exact h.trans (readout_full_error_scalar_le n r (by omega) A An Kb Ks _ _ hA hAn hKb.le hKs.le
    (cardinalityReadoutTraceScale_abs_le d n r (by omega) (by omega) lam)
    (cardinalityReadoutTraceScale_abs_le d n r (by omega) (by omega) _))

/-- The same true full second-moment estimate for the finite-Pauli record law, with no B/S norm premises. -/
theorem radialPauli_full_second_control_eventually (r : ℕ) (lam : ℕ → ℝ) (k0 : K)
    (hcard : Fintype.card K=4) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ W : K → Matrix (Fin 2) (Fin 2) ℂ,W k0=1 →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (2:ℂ) else 0) →
      ∀ e₀ : sphere (0 : EuclideanSpace ℂ (QuditIndex 2 n)) 1,
      ∀ x : Fin 2 × QuditIndex 2 n → ℝ,
      sphereDirection e₀ (complexGaussianLift (QuditIndex 2 n) x)∉
        radialHighSphereBad 2 n r lam W k0 ∪ radialLowSphereBad 2 n r W k0 →
      |gaussianRadius (QuditIndex 2 n) x-1|≤((n:ℝ)^(r+4))⁻¹ →
      ‖Matrix.toEuclideanCLM (n:=QuditIndex 2 n) (𝕜:=ℂ)
        (cardinalityReadoutRemainder (S:=Fin n) 2 pauliBasisRecords pauliFullRecord r lam (complexCoordinate x))‖≤((n:ℝ)^3)⁻¹ →
      cardinalityReadoutSecondError 2 n r pauliBasisRecords pauliFullRecord lam
        (sphereDirection e₀ (complexGaussianLift (QuditIndex 2 n) x))≤C*((n:ℝ)^3)⁻¹ := by
  obtain ⟨Kb,Ks,hKb,hKs,hE⟩ := radialPauliReadout_norm_eventually r lam k0 hcard
  let A := complementLambdaCoefficient 2 r lam
  let An := complementLambdaCoefficient 2 r (fun j => (lam j)^2)
  have hA : 0≤A := complementLambdaCoefficient_nonneg 2 r (by omega) lam
  have hAn : 0≤An := complementLambdaCoefficient_nonneg 2 r (by omega) _
  refine ⟨2*Ks+4+4*A*Kb+4*(An+A^2),by positivity,?_⟩
  filter_upwards [hE,eventually_ge_atTop 2] with n he hn
  intro W h0 hHS e₀ x hgood hr hZ
  have hnorm := he W h0 hHS (sphereDirection e₀ (complexGaussianLift (QuditIndex 2 n) x)) hgood
  have h := cardinalityPauli_second_error_of_good_radius n r hn lam Kb Ks x e₀ hr hZ hnorm.1 hnorm.2
  exact h.trans (readout_full_error_scalar_le n r (by omega) A An Kb Ks _ _ hA hAn hKb.le hKs.le
    (cardinalityReadoutTraceScale_abs_le 2 n r (by omega) (by omega) lam)
    (cardinalityReadoutTraceScale_abs_le 2 n r (by omega) (by omega) _))

end CertificationGaussian
