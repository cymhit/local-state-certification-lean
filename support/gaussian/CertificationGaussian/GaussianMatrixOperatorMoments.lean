import CertificationGaussian.GaussianMatrixTraceMoments

noncomputable section
open MeasureTheory ProbabilityTheory Matrix Finset Unitary
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
namespace CertificationGaussian
variable {I N : Type*} [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]

omit [Fintype I] [DecidableEq I] in
/-- The operator norm of a Hermitian matrix is the sup norm of its actual eigenvalue diagonal. -/
theorem hermitian_opNorm_eq_eigenvalues (X : Matrix N N ℂ) (hX : X.IsHermitian) :
    ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) X‖ = ‖fun i => (hX.eigenvalues i : ℂ)‖ := by
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  conv_lhs => rw [hX.spectral_theorem]
  simp only [conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  rfl

omit [Fintype I] [DecidableEq I] in
/-- The genuine operator norm at a positive even power is bounded by the Hermitian trace moment. -/
theorem hermitian_opNorm_even_power_le_trace (X : Matrix N N ℂ) (hX : X.IsHermitian)
    {k : Nat} (hk : 0 < k) (heven : Even k) :
    ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) X‖^k ≤ (Matrix.trace (X^k)).re := by
  cases isEmpty_or_nonempty N with
  | inl hN =>
    let := hN
    have hx0 : X = 0 := Subsingleton.elim _ _
    simp [hx0, Nat.ne_zero_of_lt hk, Matrix.trace]
  | inr hN =>
    let := hN
    rw [hermitian_opNorm_eq_eigenvalues X hX, trace_hermitian_power X hX]
    simp only [← Complex.ofReal_pow, Complex.re_sum, Complex.ofReal_re]
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset N)
      (fun i => ‖(hX.eigenvalues i : ℂ)‖) Finset.univ_nonempty
    have hm : ‖fun j => (hX.eigenvalues j : ℂ)‖ ≤ ‖(hX.eigenvalues i : ℂ)‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hi j (Finset.mem_univ j))
    calc
      _ ≤ ‖(hX.eigenvalues i : ℂ)‖^k := pow_le_pow_left₀ (norm_nonneg _) hm _
      _ = (hX.eigenvalues i)^k := by
        rw [Complex.norm_real, Real.norm_eq_abs, heven.pow_abs]
      _ ≤ _ := Finset.single_le_sum (fun j _ => heven.pow_nonneg _) (Finset.mem_univ i)

omit [DecidableEq I] in
@[fun_prop] theorem gaussianMatrixSeries_opNorm_continuous (H : I → Matrix N N ℂ) :
    Continuous (fun x : I → ℝ => ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixSeries H x)‖) := by
  simp only [gaussianMatrixSeries, map_sum, map_smul]
  fun_prop

omit [DecidableEq I] in
/-- Integrability of every positive even operator-norm moment follows from the actual trace bound. -/
theorem gaussianMatrixSeries_opNorm_even_integrable (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) {k : Nat} (hk : 0 < k) (heven : Even k) :
    Integrable (fun x : I → ℝ => ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ)
      (gaussianMatrixSeries H x)‖^k) (realGaussianProduct I) := by
  have hi : Integrable (fun x => (Matrix.trace ((gaussianMatrixSeries H x)^k)).re)
      (realGaussianProduct I) := (gaussianMatrixSeries_trace_power_integrable H k).re
  refine hi.mono' ((gaussianMatrixSeries_opNorm_continuous H).pow k).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hermitian_opNorm_even_power_le_trace _ (gaussianMatrixSeries_isHermitian H hH x) hk heven

omit [DecidableEq I] in
/-- All finite Lp integrability for the genuine matrix operator norm, including exponent zero. -/
theorem gaussianMatrixSeries_opNorm_memLp (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : I → ℝ => ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ)
      (gaussianMatrixSeries H x)‖) p (realGaussianProduct I) := by
  let n : Nat := Nat.ceil p.toReal + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hi := gaussianMatrixSeries_opNorm_even_integrable H hH (k := 2*n)
    (by omega) (even_two.mul_right n)
  have hq : MemLp (fun x : I → ℝ => ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ)
      (gaussianMatrixSeries H x)‖) (2*n:Nat) (realGaussianProduct I) := by
    apply (integrable_norm_rpow_iff (gaussianMatrixSeries_opNorm_continuous H).aestronglyMeasurable
      (by exact_mod_cast (by omega : 2*n ≠ 0)) (by finiteness)).mp
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, norm_norm] using hi
  apply hq.mono_exponent
  apply (ENNReal.toReal_le_toReal hp (by finiteness)).mp
  simp only [ENNReal.toReal_natCast]
  have hceil := Nat.le_ceil p.toReal
  dsimp [n]
  push_cast
  linarith

/-- The genuine Hermitian Gaussian operator-norm moment bound in every positive even degree. -/
theorem gaussianMatrixSeries_opNorm_moment_bound (H : I → Matrix N N ℂ)
    (hH : ∀ i, (H i).IsHermitian) {p : Nat} (hp : 0 < p) :
    ∫ x : I → ℝ, ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixSeries H x)‖^(2*p)
      ∂realGaussianProduct I ≤ (Fintype.card N : ℝ)*(Nat.doubleFactorial (2*p-1) : ℝ)*
        ‖Matrix.toEuclideanCLM (n := N) (𝕜 := ℂ) (gaussianMatrixCovariance H)‖^p := by
  have hi := gaussianMatrixSeries_opNorm_even_integrable H hH (k := 2*p)
    (by omega) (even_two.mul_right p)
  have ht : Integrable (fun x => (Matrix.trace ((gaussianMatrixSeries H x)^(2*p))).re)
      (realGaussianProduct I) := (gaussianMatrixSeries_trace_power_integrable H (2*p)).re
  exact (integral_mono hi ht (fun x => hermitian_opNorm_even_power_le_trace _
    (gaussianMatrixSeries_isHermitian H hH x) (by omega) (even_two.mul_right p))).trans
    (gaussianTraceMoment_bound H hH p)

end CertificationGaussian
