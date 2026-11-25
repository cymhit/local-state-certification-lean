import CertificationGaussian.OrbitLowHighDecomposition

noncomputable section
open Matrix MeasureTheory Metric Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The actual low scalar mean is negligible; the original radial sequence is uniformly bounded before n is chosen. -/
theorem radialFirstLow_mean_eventually (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) :
    ∀ᶠ n : ℕ in atTop,
      |(∑ w∈radialLowLabels (S:=Fin n) d r k0,
          radialFirstCoefficient d r lam (radialBellSupport k0 w).card)/(d:ℝ)^n|≤((n:ℝ)^3)⁻¹ := by
  obtain ⟨C,hC,hmax⟩ := radialFirstCoefficient_bounded d r (by omega) lam
  filter_upwards [radialLowLabels_polynomial_ratio_inverse d r hd k0 C 0 1 3] with n hn
  have hD : (0:ℝ)<(d:ℝ)^n := pow_pos (by exact_mod_cast (show 0<d by omega)) _
  have hs : |∑ w∈radialLowLabels (S:=Fin n) d r k0,
      radialFirstCoefficient d r lam (radialBellSupport k0 w).card|≤
      C*((radialLowLabels (S:=Fin n) d r k0).card:ℝ) := by
    calc
      _ ≤ ∑ w∈radialLowLabels (S:=Fin n) d r k0,
          |radialFirstCoefficient d r lam (radialBellSupport k0 w).card| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w∈radialLowLabels (S:=Fin n) d r k0,C := Finset.sum_le_sum (fun w _ => hmax _)
      _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,mul_comm]
  rw [abs_div,abs_of_pos hD]
  exact (div_le_div_of_nonneg_right hs hD.le).trans (by simpa only [pow_zero,mul_one,pow_one] using hn)

/-- The actual CFC low compression, using precisely the original cutoff and original tensor orbit columns. -/
def radialPolarCompression (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (a : (Fin n → K) → ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    EuclideanSpace ℂ (QuditIndex d n) →L[ℂ] EuclideanSpace ℂ (QuditIndex d n) :=
  let Q := matrixPolarCorrection (unitaryOrbitMatrix (radialLowOrbitFamily d n r W k0) ψ)
  rectangularEuclideanCLM (Q*Matrix.diagonal (fun w : (radialLowLabels (S:=Fin n) d r k0) =>
    (a w.val:ℂ))*Qᴴ)

/-- Both original radial sequences use the same polar correction; only the diagonal coefficients scale. -/
theorem radialPolarCompression_weight_smul (d n r : ℕ) (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K)
    (a : (Fin n → K) → ℝ) (c : ℝ) (ψ : EuclideanSpace ℂ (QuditIndex d n)) :
    radialPolarCompression d n r W k0 (fun w => c*a w) ψ=
      (c:ℂ) • radialPolarCompression d n r W k0 a ψ := by
  unfold radialPolarCompression
  dsimp only
  have he : Matrix.diagonal (fun w : (radialLowLabels (S:=Fin n) d r k0) => ((c*a w.val:ℝ):ℂ))=
      (c:ℂ) • Matrix.diagonal (fun w : (radialLowLabels (S:=Fin n) d r k0) => (a w.val:ℂ)) := by
    ext w v
    simp [Matrix.diagonal,Complex.ofReal_mul]
  rw [he,Matrix.mul_smul,Matrix.smul_mul]
  simp only [rectangularEuclideanCLM,map_smul]

/-- The actual first full radial operator is uniformly O(n^-3) close to the genuine polar low compression on the same high/Gram good event. -/
theorem radialFirst_polar_approx_eventually (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      ∀ ψ : EuclideanSpace ℂ (QuditIndex d n),
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (unitaryOrbitGramError (radialLowOrbitFamily d n r W k0) ψ)‖≤
        ((n:ℝ)^3)⁻¹ →
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialFirstHighWeights d r lam k0) ψ‖≤
        (2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹ →
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ-
        radialPolarCompression d n r W k0
          (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card) ψ‖≤C*((n:ℝ)^3)⁻¹ := by
  obtain ⟨M,hM,hmax⟩ := radialFirstCoefficient_bounded d r (by omega) lam
  have hA := complementLambdaCoefficient_nonneg d r (by omega) lam
  refine ⟨3*M+3+2*complementLambdaCoefficient d r lam,by positivity,?_⟩
  filter_upwards [radialFirstLow_mean_eventually d r hd lam k0,eventually_ge_atTop 2] with n hm hn
  intro W ψ hg hh
  let : Nonempty (QuditIndex d n) := ⟨fun _ => ⟨0,by omega⟩⟩
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have ht : ((n:ℝ)^3)⁻¹<1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hn1 (by omega))
  have hg' : ‖(unitaryOrbitMatrix
      (fun w : (radialLowLabels (S:=Fin n) d r k0) => wickTensorMatrix (fun s => W (w.val s))) ψ)ᴴ*
      unitaryOrbitMatrix (fun w : (radialLowLabels (S:=Fin n) d r k0) =>
        wickTensorMatrix (fun s => W (w.val s))) ψ-1‖≤((n:ℝ)^3)⁻¹ := by
    exact hg
  have h := unitarySphereCentered_polar_approx
    (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
    (fun w => radialFirstCoefficient d r lam (radialBellSupport k0 w).card)
    (radialLowLabels (S:=Fin n) d r k0) ψ (((n:ℝ)^3)⁻¹)
    ((2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹) M ht hM.le (fun w _ => hmax _) hg'
    (by simpa only [radialFirstHighWeights_remove] using hh)
  dsimp only at h
  simp only [qudit_card,Nat.cast_pow] at h
  have hbound := h.trans (add_le_add le_rfl hm)
  have he : 3*M*((n:ℝ)^3)⁻¹+(2+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹+
      ((n:ℝ)^3)⁻¹=(3*M+3+2*complementLambdaCoefficient d r lam)*((n:ℝ)^3)⁻¹ := by ring
  rw [he] at hbound
  have hfamily : radialLowOrbitFamily d n r W k0=
      (fun w : (radialLowLabels (S:=Fin n) d r k0) => wickTensorMatrix (fun s => W (w.val s))) := rfl
  unfold radialPolarCompression
  dsimp only
  rw [hfamily]
  exact hbound

/-- The actual second full radial operator has the same polar columns and the original doubled squared weights. -/
theorem radialSecond_polar_approx_eventually (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) (k0 : K) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      ∀ ψ : EuclideanSpace ℂ (QuditIndex d n),
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (unitaryOrbitGramError (radialLowOrbitFamily d n r W k0) ψ)‖≤
        ((n:ℝ)^3)⁻¹ →
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialSecondHighWeights d r lam k0) ψ‖≤
        (2+4*complementLambdaCoefficient d r (fun j => (lam j)^2))*((n:ℝ)^3)⁻¹ →
      ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ-
        radialPolarCompression d n r W k0
          (fun w => radialSecondCoefficient d r lam (radialBellSupport k0 w).card) ψ‖≤C*((n:ℝ)^3)⁻¹ := by
  obtain ⟨C,hC,hE⟩ := radialFirst_polar_approx_eventually d r hd (fun j => (lam j)^2) k0
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hE] with n hn
  intro W ψ hg hh
  have he : radialSecondHighWeights (S:=Fin n) d r lam k0=
      (fun w => 2*radialFirstHighWeights d r (fun j => (lam j)^2) k0 w) := by
    funext w
    exact radialSecondHighWeights_eq d r lam k0 w
  rw [he,unitarySphereCentered_weight_smul,norm_smul,Complex.norm_of_nonneg (show (0:ℝ)≤2 by norm_num)] at hh
  have hhigh : ‖unitarySphereCentered (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
      (radialFirstHighWeights d r (fun j => (lam j)^2) k0) ψ‖≤
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
    radialPolarCompression_weight_smul]
  rw [he2,norm_smul,Complex.norm_of_nonneg (show (0:ℝ)≤2 by norm_num)]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (show (0:ℝ)≤2 by norm_num)

end CertificationGaussian
