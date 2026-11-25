import CertificationGaussian.RadialBinomialEntropy
import CertificationGaussian.RadialLinearHighWeights
import CertificationGaussian.RadialHighChoi

noncomputable section
open Matrix Filter
open scoped BigOperators Matrix.Norms.L2Operator Topology
namespace CertificationGaussian
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The smaller of the full Choi rate and the actual linear low-label deletion rate. -/
def radialLinearChoiRate (d : ℕ) (ε : ℝ) : ℝ :=
  min (-(Real.log (2/(d+1:ℝ))/2)) ((Real.log (d:ℝ)-radialLinearEntropy d ε)/2)

theorem radialLinearChoiRate_pos (d : ℕ) (hd : 2≤d) (ε : ℝ)
    (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2) : 0<radialLinearChoiRate d ε := by
  have hq0 : (0:ℝ)<2/(d+1:ℝ) := by positivity
  have hq1 : (2:ℝ)/(d+1:ℝ)<1 := (div_lt_one (by positivity)).mpr
    (by exact_mod_cast (show 2<d+1 by omega))
  have hlog : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  apply lt_min
  · linarith [Real.log_neg hq0 hq1]
  · linarith

/-- The full original Choi tail has a positive exponential rate before any low-label deletion. -/
theorem radialChoiTail_eventually_exponential (d r : ℕ) (hd : 2≤d) (lam : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,radialChoiTail d n r lam≤Real.exp ((Real.log (2/(d+1:ℝ))/2)*n) := by
  have hq0 : (0:ℝ)<2/(d+1:ℝ) := by positivity
  have hq1 : (2:ℝ)/(d+1:ℝ)<1 := (div_lt_one (by positivity)).mpr
    (by exact_mod_cast (show 2<d+1 by omega))
  filter_upwards [eventually_polynomial_geometric_shift (∑ j : Fin (r+1),|lam j.val|) r r hq0 hq1,
    eventually_ge_atTop (max 1 r)] with n hg hn
  exact (radialChoiTail_le_polynomial d n r (by omega) (by omega) (by omega) lam).trans hg

/-- Exact finite truncation estimate for the actual original radial Bell matrix, before asymptotic absorption. -/
theorem radialLinearFirstHigh_bell_partialTranspose_le (d r n : ℕ) (ε : ℝ) (hd : 0<d) (lam : ℕ → ℝ)
    (W : K → Matrix (Fin d) (Fin d) ℂ) (k0 : K) (h0 : W k0=1)
    (hW : ∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ))
    (hHS : ∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0)
    (hcard : Fintype.card K=d^2) {C : ℝ} (hC : 0≤C)
    (hmax : ∀ w : ℕ,|radialFirstCoefficient d r lam w|≤C) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (partialTransposeFirst
      (weightedBellMatrix (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
        (radialLinearFirstHighWeights d n r ε lam k0)))‖ ≤
      radialChoiTail d n r lam+(radialLinearLowLabels ε n k0).card*C/(d:ℝ)^n := by
  let G := fun w : Fin n → K => wickTensorMatrix (fun s => W (w s))
  let a := fun w : Fin n → K => radialFirstCoefficient d r lam (radialBellSupport k0 w).card
  have hGa : ∀ w,G w∈unitary (Matrix (QuditIndex d n) (QuditIndex d n) ℂ) := radialTensorFamily_unitary d n W hW
  have ha : ‖a‖≤C := by
    apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro w
    exact hmax (radialBellSupport k0 w).card
  have hrem := weightedBell_partialTranspose_remove_card_bound G a hGa (radialLinearLowLabels ε n k0)
  rw [← radialLinearFirstHighWeights_remove] at hrem
  simp only [qudit_card,Nat.cast_pow,Matrix.l2_opNorm_toEuclideanCLM] at hrem
  have hrem' : ‖partialTransposeFirst (weightedBellMatrix G a)-
      partialTransposeFirst (weightedBellMatrix G (radialLinearFirstHighWeights d n r ε lam k0))‖ ≤
      (radialLinearLowLabels ε n k0).card*C/(d:ℝ)^n := hrem.trans (by gcongr)
  have hfull := radialFirstCoefficient_bell_partialTranspose_bound (S:=Fin n) d hd W k0 h0 hHS hcard r lam
  simp only [Matrix.l2_opNorm_toEuclideanCLM,Fintype.card_fin] at hfull
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  have he : partialTransposeFirst (weightedBellMatrix G (radialLinearFirstHighWeights d n r ε lam k0))=
      partialTransposeFirst (weightedBellMatrix G a)-
        (partialTransposeFirst (weightedBellMatrix G a)-partialTransposeFirst (weightedBellMatrix G (radialLinearFirstHighWeights d n r ε lam k0))) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hfull hrem')

/-- The genuine high Bell PT has exponential decay after deleting the actual linear low-label set. -/
theorem radialLinearFirstHigh_bell_partialTranspose_eventually (d r : ℕ) (hd : 2≤d)
    (ε : ℝ) (hε : 0<ε) (hhalf : ε<1/2) (hgap : radialLinearEntropy d ε<Real.log (d:ℝ)/2)
    (lam : ℕ → ℝ) (k0 : K) (hcard : Fintype.card K=d^2) :
    ∀ᶠ n : ℕ in atTop,∀ W : K → Matrix (Fin d) (Fin d) ℂ,
      W k0=1 → (∀ k,W k∈unitary (Matrix (Fin d) (Fin d) ℂ)) →
      (∀ u v,Matrix.trace ((W u)ᴴ*W v)=if u=v then (d:ℂ) else 0) →
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (partialTransposeFirst
        (weightedBellMatrix (fun w : Fin n → K => wickTensorMatrix (fun s => W (w s)))
          (radialLinearFirstHighWeights d n r ε lam k0)))‖ ≤
        2*Real.exp (-radialLinearChoiRate d ε*n) := by
  obtain ⟨C,hC,hmax⟩ := radialFirstCoefficient_bounded d r (by omega) lam
  have hlog : 0<Real.log (d:ℝ) := Real.log_pos (by exact_mod_cast (show 1<d by omega))
  filter_upwards [radialChoiTail_eventually_exponential d r hd lam,
    radialLinearLowLabels_polynomial_ratio_via_binomial_entropy d hd ε hε hhalf k0 hcard C 0 1 (by norm_num; linarith)] with n hf hl
  intro W h0 hW hHS
  have h := radialLinearFirstHigh_bell_partialTranspose_le d r n ε (by omega) lam W k0 h0 hW hHS hcard hC.le hmax
  have hl' : (radialLinearLowLabels ε n k0).card*C/(d:ℝ)^n≤
      Real.exp (-((Real.log (d:ℝ)-radialLinearEntropy d ε)/2)*n) := by
    simpa only [pow_zero,pow_one,mul_one,Nat.cast_one,one_mul,mul_comm C] using hl
  have hf' : radialChoiTail d n r lam≤Real.exp (-radialLinearChoiRate d ε*n) := by
    refine hf.trans (Real.exp_le_exp.mpr ?_)
    have hh := min_le_left (-(Real.log (2/(d+1:ℝ))/2)) ((Real.log (d:ℝ)-radialLinearEntropy d ε)/2)
    unfold radialLinearChoiRate
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  have hl'' : (radialLinearLowLabels ε n k0).card*C/(d:ℝ)^n≤Real.exp (-radialLinearChoiRate d ε*n) := by
    refine hl'.trans (Real.exp_le_exp.mpr ?_)
    have hh := min_le_right (-(Real.log (2/(d+1:ℝ))/2)) ((Real.log (d:ℝ)-radialLinearEntropy d ε)/2)
    unfold radialLinearChoiRate
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]
  exact h.trans (by linarith)

end CertificationGaussian
