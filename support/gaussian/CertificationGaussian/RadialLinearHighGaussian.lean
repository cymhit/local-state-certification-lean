import CertificationGaussian.RadialLinearHighChoi
import CertificationGaussian.RadialHighGaussian

noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- A common positive rate for all three actual high Gaussian parameters. -/
def radialLinearHighRate (d : ℕ) (ε : ℝ) : ℝ :=
  min (ε*Real.log (d+1:ℝ)/4) (radialLinearChoiRate d ε)

theorem radialLinearHighRate_pos (d : ℕ) (hd : 2≤d) (ε : ℝ) (hε : 0<ε)
    (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2) : 0<radialLinearHighRate d ε := by
  apply lt_min
  · apply div_pos (mul_pos hε (Real.log_pos ?_)) (by norm_num)
    exact_mod_cast (show 1<d+1 by omega)
  · exact radialLinearChoiRate_pos d hd ε hgap

/-- Rate comparison for the actual natural system size. -/
theorem radialLinear_exp_rate_le (n : ℕ) (a b : ℝ) (hab : b≤a) :
    Real.exp (-a*n)≤Real.exp (-b*n) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hab) (Nat.cast_nonneg n))

/-- All three parameters of the proved Gaussian theorem are exponential, uniformly in the genuine local basis. -/
theorem radialLinearFirstHigh_gaussian_parameters (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      let a := radialLinearFirstHighWeights d n r ε lam k0
      let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
      max (Real.sqrt (unitaryWeightSquareMean (I:=QuditIndex d n) a))
        (max ‖a‖ ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix G a))‖)≤
          2*Real.exp (-radialLinearHighRate d ε*n) := by
  filter_upwards [radialLinearFirstHighWeights_sqrt_eventually d r (by omega) ε hε lam k0 hcard,
    radialLinearFirstHighWeights_norm_eventually d r (by omega) ε hε lam k0,
    radialLinearFirstHigh_bell_partialTranspose_eventually d r hd ε hε hhalf hgap lam k0 hcard] with n hs hn ht
  intro W h0 hW hHS
  dsimp only
  have hleft : radialLinearHighRate d ε≤ε*Real.log (d+1:ℝ)/4 := min_le_left _ _
  have hright : radialLinearHighRate d ε≤radialLinearChoiRate d ε := min_le_right _ _
  have ha : 0<ε*Real.log (d+1:ℝ) := mul_pos hε (Real.log_pos (by exact_mod_cast (show 1<d+1 by omega)))
  have hnorm := hn.trans (radialLinear_exp_rate_le n _ _ (by linarith : radialLinearHighRate d ε≤ε*Real.log (d+1:ℝ)/2))
  have hsqrt : Real.sqrt (unitaryWeightSquareMean (I:=QuditIndex d n) (radialLinearFirstHighWeights d n r ε lam k0))≤
      Real.exp (-radialLinearHighRate d ε*n) := by
    simpa only [unitaryWeightSquareMean,qudit_card,Nat.cast_pow] using
      hs.trans (radialLinear_exp_rate_le n _ _ hleft)
  have hpt := (ht W h0 hW hHS).trans (mul_le_mul_of_nonneg_left
    (radialLinear_exp_rate_le n _ _ hright) (by norm_num : (0:ℝ)≤2))
  refine max_le (hsqrt.trans (by nlinarith [Real.exp_pos (-radialLinearHighRate d ε*n)]))
    (max_le (hnorm.trans (by nlinarith [Real.exp_pos (-radialLinearHighRate d ε*n)])) ?_)
  simpa only [rectangularEuclideanCLM_norm,Matrix.l2_opNorm_toEuclideanCLM] using hpt

/-- True centered Gaussian operator expectation for the original first linear high block. -/
theorem radialLinearFirstHigh_gaussian_expectation (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      (∫ x,‖unitaryGaussianCentered
        (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialLinearFirstHighWeights d n r ε lam k0) x‖∂pairedGaussian (QuditIndex d n))≤
          Real.exp (-(radialLinearHighRate d ε/2)*n) := by
  let : NeZero d := ⟨by omega⟩
  have hrate := radialLinearHighRate_pos d hd ε hε hgap
  have hlog : 0≤Real.log 2+Real.log (d:ℝ) := by
    have h2 : 0≤Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
    have hd' : 0≤Real.log (d:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤d by omega))
    linarith
  filter_upwards [radialLinearFirstHigh_gaussian_parameters d r hd ε hε hhalf hgap lam k0 hcard,
    eventually_polynomial_le_exp ((16*gaussianMatrixChaosConstant)*(Real.log 2+Real.log (d:ℝ))) 1
      (by linarith : 0<radialLinearHighRate d ε/2),eventually_ge_atTop 1] with n hm hp hn
  intro W h0 hW hHS
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a := radialLinearFirstHighWeights d n r ε lam k0
  have hg := unitaryGaussianConjugation_expectation_bound G a
    (radialTensorFamily_unitary d n W hW) (radialTensorFamily_hilbertSchmidt d n W hHS)
  have hm' := hm W h0 hW hHS
  have hfactor := mul_le_mul_of_nonneg_left (qudit_log_dimension_le d n (by omega) hn)
    (mul_nonneg (by norm_num : (0:ℝ)≤8) gaussianMatrixChaosConstant_pos.le)
  have hm0 : 0≤max (Real.sqrt (unitaryWeightSquareMean (I:=QuditIndex d n) a))
      (max ‖a‖ ‖rectangularEuclideanCLM (partialTransposeFirst (weightedBellMatrix G a))‖) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hf0 : 0≤(8*gaussianMatrixChaosConstant)*((Real.log 2+Real.log (d:ℝ))*(n:ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) gaussianMatrixChaosConstant_pos.le) (mul_nonneg hlog (Nat.cast_nonneg _))
  calc
    _ ≤ (8*gaussianMatrixChaosConstant)*((Real.log 2+Real.log (d:ℝ))*(n:ℝ))*
        (2*Real.exp (-radialLinearHighRate d ε*n)) := hg.trans (mul_le_mul hfactor hm' hm0 hf0)
    _ = ((16*gaussianMatrixChaosConstant)*(Real.log 2+Real.log (d:ℝ)))*(n:ℝ)^1*
        Real.exp (-radialLinearHighRate d ε*n) := by ring
    _ ≤ Real.exp ((radialLinearHighRate d ε/2)*n)*Real.exp (-radialLinearHighRate d ε*n) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The second original high block keeps its exact factor2 and squared lambda, under the same exponential rate. -/
theorem radialLinearSecondHigh_gaussian_expectation (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      (∫ x,‖unitaryGaussianCentered
        (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialLinearSecondHighWeights d n r ε lam k0) x‖∂pairedGaussian (QuditIndex d n))≤
          2*Real.exp (-(radialLinearHighRate d ε/2)*n) := by
  filter_upwards [radialLinearFirstHigh_gaussian_expectation d r hd ε hε hhalf hgap
    (fun j => (lam j)^2) k0 hcard] with n hn
  intro W h0 hW hHS
  have he : radialLinearSecondHighWeights d n r ε lam k0=
      (fun w => 2*radialLinearFirstHighWeights d n r ε (fun j => (lam j)^2) k0 w) :=
    funext (radialLinearSecondHighWeights_eq d n r ε lam k0)
  simp only [he,unitaryGaussianCentered_weight_smul,norm_smul]
  rw [Complex.norm_of_nonneg (show (0:ℝ)≤2 by norm_num),integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hn W h0 hW hHS) (by norm_num : (0:ℝ)≤2)

end CertificationGaussian
