import CertificationGaussian.RadialBinomialEntropy
import CertificationGaussian.OrbitLowHighDecomposition
import CertificationGaussian.RadialLinearLowOrbit
import CertificationGaussian.RadialLinearHighSphere

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The actual low scalar mean is negligible; the original radial sequence is uniformly bounded before n is chosen. -/
theorem radialLinearFirstLow_mean_eventually (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,
      |(∑ w∈radialLinearLowLabels ε n k0,
          radialFirstCoefficient d r lam (radialBellSupport k0 w).card)/(d:ℝ)^n|≤((n:ℝ)^3)⁻¹ := by
  obtain ⟨C,hC,hmax⟩ := radialFirstCoefficient_bounded d r (by omega) lam
  have hlog : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  have hc : 0<(Real.log (d:ℝ)-radialLinearEntropy d ε)/2 := by linarith
  filter_upwards [radialLinearLowLabels_polynomial_ratio_via_binomial_entropy d hd ε hε hhalf k0 hcard C 0 1
    (by norm_num; linarith),eventually_exp_neg_le_inverse_pow hc 3] with n hratio hexp
  have hn : C*((radialLinearLowLabels ε n k0).card:ℝ)/(d:ℝ)^n≤((n:ℝ)^3)⁻¹ := by
    have hratio' : C*((radialLinearLowLabels ε n k0).card:ℝ)/(d:ℝ)^n≤
        Real.exp (-((Real.log (d:ℝ)-radialLinearEntropy d ε)/2)*n) := by
      simpa only [pow_zero,mul_one,pow_one,Nat.cast_one,one_mul] using hratio
    exact hratio'.trans hexp
  have hD : (0:ℝ)<(d:ℝ)^n := pow_pos (by exact_mod_cast (show 0<d by omega)) _
  have hs : |∑ w∈radialLinearLowLabels ε n k0,
      radialFirstCoefficient d r lam (radialBellSupport k0 w).card|≤
      C*((radialLinearLowLabels ε n k0).card:ℝ) := by
    calc
      _ ≤ ∑ w∈radialLinearLowLabels ε n k0,
          |radialFirstCoefficient d r lam (radialBellSupport k0 w).card| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w∈radialLinearLowLabels ε n k0,C := Finset.sum_le_sum (fun w _ => hmax _)
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
  rw [abs_div,abs_of_pos hD]
  exact (div_le_div_of_nonneg_right hs hD.le).trans (by simpa only [pow_zero,mul_one,pow_one] using hn)

/-- The actual CFC low compression, using precisely the fixed linear cutoff and original tensor orbit columns. -/
def radialLinearPolarCompression (d n : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (a : (Fin n → K) → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    EuclideanSpace ℂ (QuditIndex d n) →L[ℂ] EuclideanSpace ℂ (QuditIndex d n) :=
  let Q := matrixPolarCorrection (unitaryOrbitMatrix (radialLinearLowOrbitFamily d n ε W k0) ψ)
  rectangularEuclideanCLM (Q*Matrix.diagonal (fun w : (radialLinearLowLabels ε n k0) =>
    (a w.val:ℂ))*Qᴴ)

/-- Both original radial sequences use the same polar correction; only the diagonal coefficients scale. -/
theorem radialLinearPolarCompression_weight_smul (d n : ℕ) (ε : ℝ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (a : (Fin n → K) → ℝ) (c : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    radialLinearPolarCompression d n ε W k0 (fun w => c*a w) ψ=
      (c:ℂ) • radialLinearPolarCompression d n ε W k0 a ψ := by
  unfold radialLinearPolarCompression
  dsimp only
  have he : Matrix.diagonal (fun w : (radialLinearLowLabels ε n k0) => ((c*a w.val:ℝ):ℂ))=
      (c:ℂ) • Matrix.diagonal (fun w : (radialLinearLowLabels ε n k0) => (a w.val:ℂ)) := by
    ext w v
    simp [Matrix.diagonal,Complex.ofReal_mul]
  rw [he,Matrix.mul_smul,Matrix.smul_mul]
  simp only [rectangularEuclideanCLM,map_smul]

/-- The actual first full radial operator is uniformly O(n^-3) close to the genuine polar low compression on the same high/Gram good event. -/
theorem radialLinearFirst_polar_approx_eventually (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      ∀ ψ : EuclideanSpace ℂ (QuditIndex d n),
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (unitaryOrbitGramError (radialLinearLowOrbitFamily d n ε W k0) ψ)‖≤
        ((n:ℝ)^3)⁻¹ →
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialLinearFirstHighWeights d n r ε lam k0) ψ‖≤
        (2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹ →
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ-
        radialLinearPolarCompression d n ε W k0
          (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ‖≤C*((n:ℝ)^3)⁻¹ := by
  obtain ⟨M,hM,hmax⟩ := radialFirstCoefficient_bounded d r (by omega) lam
  have hA := complementLambdaCoefficient_nonneg d r (by omega) lam
  refine ⟨3*M+3+2*complementLambdaCoefficient d r lam,by positivity,?_⟩
  filter_upwards [radialLinearFirstLow_mean_eventually d r hd ε hε hhalf hgap lam k0 hcard,eventually_ge_atTop 2] with n hm hn
  intro W ψ hg hh
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have ht : ((n:ℝ)^3)⁻¹<1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hn1 (by omega))
  have hg' : ‖(unitaryOrbitMatrix
      (fun w : (radialLinearLowLabels ε n k0) => wickTensorMatrix (fun s => W (w.val s))) ψ)ᴴ*
      unitaryOrbitMatrix (fun w : (radialLinearLowLabels ε n k0) =>
        wickTensorMatrix (fun s => W (w.val s))) ψ-1‖≤((n:ℝ)^3)⁻¹ := by
    exact hg
  have h := unitarySphereCentered_polar_approx
    (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
    (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card)
    (radialLinearLowLabels ε n k0) ψ (((n:ℝ)^3)⁻¹)
    ((2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹) M ht hM.le (fun w _ => hmax _) hg'
    (by simpa only [radialLinearFirstHighWeights_remove] using hh)
  dsimp only at h
  simp only [qudit_card,Nat.cast_pow] at h
  have hbound := h.trans (add_le_add le_rfl hm)
  have he : 3*M*((n:ℝ)^3)⁻¹+(2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹+
      ((n:ℝ)^3)⁻¹=(3*M+3+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹ := by ring
  rw [he] at hbound
  have hfamily : radialLinearLowOrbitFamily d n ε W k0=
      (fun w : (radialLinearLowLabels ε n k0) => wickTensorMatrix (fun s => W (w.val s))) := rfl
  unfold radialLinearPolarCompression
  dsimp only
  rw [hfamily]
  exact hbound

/-- The actual second full radial operator has the same polar columns and the original doubled squared weights. -/
theorem radialLinearSecond_polar_approx_eventually (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      ∀ ψ : EuclideanSpace ℂ (QuditIndex d n),
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (unitaryOrbitGramError (radialLinearLowOrbitFamily d n ε W k0) ψ)‖≤
        ((n:ℝ)^3)⁻¹ →
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialLinearSecondHighWeights d n r ε lam k0) ψ‖≤
        (2+4*complementLambdaCoefficient d r (fun j => (lam j)^2))*((n:ℝ)^3)⁻¹ →
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ-
        radialLinearPolarCompression d n ε W k0
          (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ‖≤C*((n:ℝ)^3)⁻¹ := by
  obtain ⟨C,hC,hE⟩ := radialLinearFirst_polar_approx_eventually d r hd ε hε hhalf hgap (fun j => (lam j)^2) k0 hcard
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hE] with n hn
  intro W ψ hg hh
  have he : radialLinearSecondHighWeights d n r ε lam k0=
      (fun w => 2*radialLinearFirstHighWeights d n r ε (fun j => (lam j)^2) k0 w) := by
    funext w
    exact radialLinearSecondHighWeights_eq d n r ε lam k0 w
  rw [he,unitarySphereCentered_weight_smul,norm_smul,Complex.norm_of_nonneg (show (0:ℝ)≤2 by norm_num)] at hh
  have hhigh : ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialLinearFirstHighWeights d n r ε (fun j => (lam j)^2) k0) ψ‖≤
      (2+2*complementLambdaCoefficient d r (fun j => (lam j)^2))*((n:ℝ)^3)⁻¹ := by
    nlinarith [show (0:ℝ)≤((n:ℝ)^3)⁻¹ by positivity]
  have h := hn W ψ hg hhigh
  have he2 (A B : EuclideanSpace ℂ (QuditIndex d n) →L[ℂ] EuclideanSpace ℂ (QuditIndex d n)) :
      ((2:ℝ):ℂ) • A-((2:ℝ):ℂ) • B=((2:ℝ):ℂ) • (A-B) := by
    ext x i
    simp only [_root_.sub_apply,_root_.smul_apply,
      PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    ring
  simp only [radialSecondCoefficient,unitarySphereCentered_weight_smul,
    radialLinearPolarCompression_weight_smul]
  rw [he2,norm_smul,Complex.norm_of_nonneg (show (0:ℝ)≤2 by norm_num)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (show (0:ℝ)≤2 by norm_num)

end CertificationGaussian
